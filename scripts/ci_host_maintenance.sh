#!/usr/bin/env bash
set -euo pipefail

CACHE_ROOT="${CACHE_ROOT:-/srv/verity-ci-cache}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LAKE_BUILD_MAX_AGE_DAYS="${LAKE_BUILD_MAX_AGE_DAYS:-21}"
LAKE_PACKAGES_MAX_AGE_DAYS="${LAKE_PACKAGES_MAX_AGE_DAYS:-14}"
LAKE_PACKAGES_MAX_ENTRIES="${LAKE_PACKAGES_MAX_ENTRIES:-20}"
MIN_FREE_GB="${MIN_FREE_GB:-100}"
MIN_ENTRY_AGE_HOURS="${MIN_ENTRY_AGE_HOURS:-6}"
COMPILER_CCACHE_MAX_AGE_DAYS="${COMPILER_CCACHE_MAX_AGE_DAYS:-21}"
ARTIFACT_MAX_AGE_HOURS="${ARTIFACT_MAX_AGE_HOURS:-24}"
JOURNAL_VACUUM_TIME="${JOURNAL_VACUUM_TIME:-14d}"
JOURNAL_VACUUM_SIZE="${JOURNAL_VACUUM_SIZE:-1G}"
DOCKER_PRUNE_FILTER="${DOCKER_PRUNE_FILTER:-until=168h}"

usage() {
  cat <<'EOF'
Usage:
  scripts/ci_host_maintenance.sh run
  scripts/ci_host_maintenance.sh install-systemd

Subcommands:
  run              Prune stale Verity CI cache entries, vacuum journald, and prune unused Docker data.
  install-systemd  Install and enable a weekly systemd timer for this script.

Environment:
  CACHE_ROOT                    Default: /srv/verity-ci-cache
  LAKE_BUILD_MAX_AGE_DAYS       Default: 21
  LAKE_PACKAGES_MAX_AGE_DAYS    Default: 14
  LAKE_PACKAGES_MAX_ENTRIES     Default: 20 (newest kept; one entry exists per PR/branch)
  MIN_FREE_GB                   Default: 100 (LRU-evict lake-packages below this)
  MIN_ENTRY_AGE_HOURS           Default: 6 (never delete entries touched more recently;
                                ci_local_persistence.sh mount touches an entry on attach,
                                so caches of running/recent jobs are spared)
  COMPILER_CCACHE_MAX_AGE_DAYS  Default: 21
  ARTIFACT_MAX_AGE_HOURS        Default: 24
  JOURNAL_VACUUM_TIME           Default: 14d
  JOURNAL_VACUUM_SIZE           Default: 1G
  DOCKER_PRUNE_FILTER           Default: until=168h
EOF
}

require_root() {
  if [ "$(id -u)" -ne 0 ]; then
    echo "Run this script as root." >&2
    exit 1
  fi
}

prune_tree() {
  local dir="$1"
  local max_age_days="$2"
  local label="$3"

  if [ ! -d "$dir" ]; then
    return
  fi

  local count=0
  while IFS= read -r -d '' entry; do
    rm -rf "$entry"
    count=$((count + 1))
  done < <(find "$dir" -mindepth 1 -maxdepth 1 -mtime +"$max_age_days" -print0 2>/dev/null)

  echo "${label}: removed ${count} entries older than ${max_age_days} days"
}

# Direct children of $1 as NUL-delimited "epoch-mtime<TAB>path" records —
# newline-safe, unlike parsing ls output. Order controlled by the caller.
list_entries_with_mtime() {
  find "$1" -mindepth 1 -maxdepth 1 -printf '%T@\t%p\0' 2>/dev/null
}

# Whether an epoch mtime ($1) is younger than MIN_ENTRY_AGE_HOURS.
# ci_local_persistence.sh touches an entry when a job attaches it, so a
# young mtime means "a running or recent CI job may be using this" — the
# maintenance pass must never delete it out from under the job.
entry_is_recent() {
  local mtime_epoch="${1%%.*}"
  local now
  now="$(date +%s)"
  [ $((now - mtime_epoch)) -lt $((MIN_ENTRY_AGE_HOURS * 3600)) ]
}

avail_gb() {
  df --output=avail -BG "$1" | tail -1 | tr -dc '0-9'
}

# Keep only the newest $2 entries of $1 (mtime order). Age-based pruning
# alone cannot bound this cache: one ~6 GB entry exists per PR/branch, so
# two weeks of PR churn filled 664 GB and took the runner host disk to 100%
# on 2026-07-12 (runner listener crash-looped, CI jobs sat queued forever).
cap_tree_entries() {
  local dir="$1"
  local max_entries="$2"
  local label="$3"

  if [ ! -d "$dir" ]; then
    return
  fi

  local index=0 removed=0 failed=0 mtime entry
  while IFS=$'\t' read -r -d '' mtime entry; do
    index=$((index + 1))
    if [ "$index" -le "$max_entries" ]; then
      continue
    fi
    if entry_is_recent "$mtime"; then
      continue
    fi
    if rm -rf "$entry"; then
      removed=$((removed + 1))
    else
      failed=$((failed + 1))
      echo "${label}: failed to remove ${entry}" >&2
    fi
  done < <(list_entries_with_mtime "$dir" | sort -z -r -n)

  if [ "$removed" -gt 0 ] || [ "$failed" -gt 0 ]; then
    echo "${label}: removed ${removed} entries beyond the newest ${max_entries} (${failed} failures)"
  fi
}

# LRU-evict entries of $1 until the filesystem has at least $2 GiB free.
# Single pass over an oldest-first snapshot: an entry whose rm fails is
# skipped, never retried, so a stuck entry cannot spin this loop forever.
evict_until_free() {
  local dir="$1"
  local min_free_gb="$2"
  local label="$3"

  if [ ! -d "$dir" ]; then
    return
  fi
  if [ "$(avail_gb "$dir")" -ge "$min_free_gb" ]; then
    return
  fi

  local removed=0 mtime entry
  while IFS=$'\t' read -r -d '' mtime entry; do
    if [ "$(avail_gb "$dir")" -ge "$min_free_gb" ]; then
      break
    fi
    if entry_is_recent "$mtime"; then
      continue
    fi
    if rm -rf "$entry"; then
      removed=$((removed + 1))
    else
      echo "${label}: failed to evict ${entry}" >&2
    fi
  done < <(list_entries_with_mtime "$dir" | sort -z -n)

  if [ "$removed" -gt 0 ]; then
    echo "${label}: evicted ${removed} LRU entries to restore ${min_free_gb} GiB free"
  fi
  if [ "$(avail_gb "$dir")" -lt "$min_free_gb" ]; then
    echo "${label}: still below ${min_free_gb} GiB free after eviction (remaining entries are recent or unremovable)" >&2
  fi
}

run_maintenance() {
  require_root

  mkdir -p "$CACHE_ROOT"
  prune_tree "$CACHE_ROOT/lake-build" "$LAKE_BUILD_MAX_AGE_DAYS" "lake-build cache"
  prune_tree "$CACHE_ROOT/lake-packages" "$LAKE_PACKAGES_MAX_AGE_DAYS" "lake-packages cache"
  cap_tree_entries "$CACHE_ROOT/lake-packages" "$LAKE_PACKAGES_MAX_ENTRIES" "lake-packages cache"
  evict_until_free "$CACHE_ROOT/lake-packages" "$MIN_FREE_GB" "lake-packages cache"
  prune_tree "$CACHE_ROOT/compiler-ccache" "$COMPILER_CCACHE_MAX_AGE_DAYS" "compiler ccache"

  if [ -x "$SCRIPT_DIR/ci_local_persistence.sh" ]; then
    "$SCRIPT_DIR/ci_local_persistence.sh" cleanup --max-age-hours "$ARTIFACT_MAX_AGE_HOURS"
  fi

  if command -v journalctl >/dev/null 2>&1; then
    journalctl --vacuum-time="$JOURNAL_VACUUM_TIME"
    journalctl --vacuum-size="$JOURNAL_VACUUM_SIZE"
  fi

  if command -v docker >/dev/null 2>&1; then
    docker image prune -af --filter "$DOCKER_PRUNE_FILTER"
    docker builder prune -af --filter "$DOCKER_PRUNE_FILTER"
  fi
}

install_systemd() {
  require_root

  local script_path
  script_path="$(readlink -f "$0")"

  cat > /etc/systemd/system/verity-ci-host-maintenance.service <<EOF
[Unit]
Description=Verity CI host maintenance
Documentation=file://${script_path}

[Service]
Type=oneshot
ExecStart=${script_path} run
EOF

  cat > /etc/systemd/system/verity-ci-host-maintenance.timer <<'EOF'
[Unit]
Description=Daily Verity CI host maintenance

[Timer]
OnCalendar=*-*-* 04:30:00
Persistent=true
RandomizedDelaySec=30m

[Install]
WantedBy=timers.target
EOF

  systemctl daemon-reload
  systemctl enable --now verity-ci-host-maintenance.timer
  systemctl list-timers verity-ci-host-maintenance.timer
}

case "${1:-}" in
  run)
    run_maintenance
    ;;
  install-systemd)
    install_systemd
    ;;
  *)
    usage >&2
    exit 1
    ;;
esac
