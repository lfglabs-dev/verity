#!/usr/bin/env bash
set -euo pipefail

CACHE_ROOT="${CACHE_ROOT:-/srv/verity-ci-cache}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LAKE_BUILD_MAX_AGE_DAYS="${LAKE_BUILD_MAX_AGE_DAYS:-7}"
LAKE_BUILD_MAX_ENTRIES="${LAKE_BUILD_MAX_ENTRIES:-12}"
LAKE_PACKAGES_MAX_AGE_DAYS="${LAKE_PACKAGES_MAX_AGE_DAYS:-14}"
LAKE_PACKAGES_MAX_ENTRIES="${LAKE_PACKAGES_MAX_ENTRIES:-20}"
MIN_FREE_GB="${MIN_FREE_GB:-100}"
MIN_ENTRY_AGE_HOURS="${MIN_ENTRY_AGE_HOURS:-12}"
COMPILER_CCACHE_MAX_AGE_DAYS="${COMPILER_CCACHE_MAX_AGE_DAYS:-7}"
ELAN_MAX_AGE_DAYS="${ELAN_MAX_AGE_DAYS:-7}"
ARTIFACT_MAX_AGE_HOURS="${ARTIFACT_MAX_AGE_HOURS:-24}"
JOURNAL_VACUUM_TIME="${JOURNAL_VACUUM_TIME:-14d}"
JOURNAL_VACUUM_SIZE="${JOURNAL_VACUUM_SIZE:-1G}"
DOCKER_PRUNE_FILTER="${DOCKER_PRUNE_FILTER:-until=168h}"

usage() {
  cat <<'EOF'
Usage:
  scripts/ci_host_maintenance.sh run
  scripts/ci_host_maintenance.sh caches
  scripts/ci_host_maintenance.sh install-systemd

Subcommands:
  run              Prune stale Verity CI cache entries, vacuum journald, and prune unused Docker data.
  caches           Only prune the Verity CI cache trees under CACHE_ROOT (no root required).
  install-systemd  Install and enable a daily systemd timer for this script.

Environment:
  CACHE_ROOT                    Default: /srv/verity-ci-cache
  LAKE_BUILD_MAX_AGE_DAYS       Default: 7
  LAKE_BUILD_MAX_ENTRIES        Default: 12 (newest kept; up to three namespaces per PR)
  LAKE_PACKAGES_MAX_AGE_DAYS    Default: 14
  LAKE_PACKAGES_MAX_ENTRIES     Default: 20 (newest kept; one entry exists per PR/branch)
  MIN_FREE_GB                   Default: 100 (LRU-evict lake-build, then lake-packages,
                                below this)
  MIN_ENTRY_AGE_HOURS           Default: 12 (never delete entries touched more recently;
                                ci_local_persistence.sh mount touches an entry, and the
                                fallback it copies from, on attach. 12h outlasts the
                                longest job timeout (6h), so an attach is a lease for
                                the whole consuming job. Attach and deletion also
                                serialize on per-entry flock locks in CACHE_ROOT/.locks)
  COMPILER_CCACHE_MAX_AGE_DAYS  Default: 7
  ELAN_MAX_AGE_DAYS             Default: 7 (one toolchain copy per workflow prefix and
                                toolchain hash; attach refreshes the mtime of live ones)
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
    if delete_entry_if_idle "$entry"; then
      count=$((count + 1))
    fi
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

# Available GiB on the filesystem backing $1. Fails SAFE: if df errors (path
# vanished, transient fs issue), report "plenty of space" so eviction stops
# instead of looping or over-deleting on garbage input.
avail_gb() {
  local out
  out="$(df --output=avail -BG "$1" 2>/dev/null | tail -1 | tr -dc '0-9')"
  if [ -z "$out" ]; then
    echo 999999999
  else
    echo "$out"
  fi
}

# Current epoch mtime of $1, empty if it vanished.
current_mtime() {
  stat -c %Y "$1" 2>/dev/null || true
}

# Lock file shared with ci_local_persistence.sh for cache entry $1. Locks live
# in CACHE_ROOT/.locks, outside every pruned tree, so they are never evicted.
entry_lock_path() {
  local tree
  tree="$(dirname "$1")"
  printf '%s/.locks/%s__%s.lock' "$(dirname "$tree")" "$(basename "$tree")" "$(basename "$1")"
}

# Delete cache entry $1 unless it is in use. The eligibility re-check and the
# rm run under the entry's exclusive lock: an attach (which holds the same lock
# while it validates, leases and seeds an entry) either completes first, so the
# fresh lease makes the entry ineligible, or starts after the deletion and
# re-creates it. A lock that is already held means "in use": skip.
# Returns 0 if deleted, 1 if skipped, 2 if rm failed.
delete_entry_if_idle() {
  local entry="$1" lock mtime status=1 fd
  lock="$(entry_lock_path "$entry")"
  mkdir -p "$(dirname "$lock")"
  exec {fd}>"$lock"
  if flock -x -n "$fd"; then
    mtime="$(current_mtime "$entry")"
    if [ -n "$mtime" ] && ! entry_is_recent "$mtime"; then
      if rm -rf "$entry"; then status=0; else status=2; fi
    fi
  fi
  exec {fd}>&-
  return "$status"
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

  local index=0 removed=0 failed=0 rc mtime entry
  while IFS=$'\t' read -r -d '' mtime entry; do
    index=$((index + 1))
    if [ "$index" -le "$max_entries" ]; then
      continue
    fi
    # Re-checked under the entry lock: a job may have attached it since the
    # snapshot above was taken.
    delete_entry_if_idle "$entry" && rc=0 || rc=$?
    if [ "$rc" -eq 0 ]; then
      removed=$((removed + 1))
    elif [ "$rc" -eq 2 ]; then
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

  local removed=0 rc mtime entry
  while IFS=$'\t' read -r -d '' mtime entry; do
    if [ "$(avail_gb "$dir")" -ge "$min_free_gb" ]; then
      break
    fi
    # Re-checked under the entry lock (same attach race as cap_tree_entries).
    delete_entry_if_idle "$entry" && rc=0 || rc=$?
    if [ "$rc" -eq 0 ]; then
      removed=$((removed + 1))
    elif [ "$rc" -eq 2 ]; then
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

prune_caches() {
  mkdir -p "$CACHE_ROOT"
  prune_tree "$CACHE_ROOT/lake-build" "$LAKE_BUILD_MAX_AGE_DAYS" "lake-build cache"
  cap_tree_entries "$CACHE_ROOT/lake-build" "$LAKE_BUILD_MAX_ENTRIES" "lake-build cache"
  prune_tree "$CACHE_ROOT/lake-packages" "$LAKE_PACKAGES_MAX_AGE_DAYS" "lake-packages cache"
  cap_tree_entries "$CACHE_ROOT/lake-packages" "$LAKE_PACKAGES_MAX_ENTRIES" "lake-packages cache"
  # Build trees are the largest and cheapest to recreate (seeded from main), so
  # evict them before package trees when the disk runs low.
  evict_until_free "$CACHE_ROOT/lake-build" "$MIN_FREE_GB" "lake-build cache"
  evict_until_free "$CACHE_ROOT/lake-packages" "$MIN_FREE_GB" "lake-packages cache"
  prune_tree "$CACHE_ROOT/compiler-ccache" "$COMPILER_CCACHE_MAX_AGE_DAYS" "compiler ccache"
  prune_tree "$CACHE_ROOT/elan" "$ELAN_MAX_AGE_DAYS" "elan toolchains"
}

run_maintenance() {
  require_root
  prune_caches

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
  caches)
    prune_caches
    ;;
  install-systemd)
    install_systemd
    ;;
  *)
    usage >&2
    exit 1
    ;;
esac
