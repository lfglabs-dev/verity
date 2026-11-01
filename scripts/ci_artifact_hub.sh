#!/usr/bin/env bash
# Configure the cross-host CI artifact hub used by ci_local_persistence.sh.
#
# One runner host is the hub: its local artifact store
# (CACHE_ROOT/artifacts) is the hub directory. Other runner hosts push and
# pull artifacts there with rsync over ssh, using a per-host key that the hub
# confines to that directory with rrsync. Trust is unchanged from the local
# store: only runner users can write artifacts.
set -euo pipefail

CACHE_ROOT="${CACHE_ROOT:-/srv/verity-ci-cache}"
CONF_DIR="${VERITY_CI_CONF_DIR:-/usr/local/lib/verity-ci}"

usage() {
  cat <<'EOF'
Usage (as root):
  scripts/ci_artifact_hub.sh server-init
  scripts/ci_artifact_hub.sh server-authorize PUBKEY_TYPE PUBKEY_BLOB [COMMENT]...
  scripts/ci_artifact_hub.sh client-init USER@HUB_HOST HOSTKEY_TYPE HOSTKEY_BLOB

server-init       Mark this host as the hub (its local store is the hub directory).
server-authorize  Allow client public keys (type/blob/comment triples) to rsync
                  into the hub directory only (rrsync, no shell, no forwarding).
client-init       Create this host's hub key, pin the hub host key, write
                  CONF_DIR/hub.env and print the public key to authorize.
EOF
}

require_root() {
  if [ "$(id -u)" -ne 0 ]; then
    echo "Run this script as root." >&2
    exit 1
  fi
}

runner_user() {
  local user
  user="$(stat -c %U "$CACHE_ROOT")"
  if [ -z "$user" ] || [ "$user" = "root" ]; then
    echo "${CACHE_ROOT} must be owned by the runner user, not '${user}'" >&2
    exit 1
  fi
  printf '%s' "$user"
}

home_of() {
  getent passwd "$1" | cut -d: -f6
}

server_init() {
  require_root
  local user
  user="$(runner_user)"
  install -d -m 0755 -o "$user" -g "$(id -gn "$user")" "$CACHE_ROOT/artifacts"
  install -d -m 0755 "$CONF_DIR"
  printf 'VERITY_CI_HUB_SELF=1\nVERITY_CI_HUB_DIR=%s/artifacts\n' "$CACHE_ROOT" > "$CONF_DIR/hub.env"
  chmod 0644 "$CONF_DIR/hub.env"
  echo "This host is the artifact hub for ${CACHE_ROOT}/artifacts"
}

server_authorize() {
  require_root
  if [ "$#" -lt 2 ]; then
    usage >&2
    exit 1
  fi
  local user home keys="" arg
  user="$(runner_user)"
  home="$(home_of "$user")"
  for arg in "$@"; do
    case "$arg" in
      *[[:space:]]*|"") echo "key arguments must not contain whitespace" >&2; exit 1 ;;
    esac
  done
  while [ "$#" -ge 2 ]; do
    local type="$1" blob="$2" comment=""
    shift 2
    if [ "$#" -ge 1 ] && [ "${1#ssh-}" = "$1" ]; then
      comment="$1"
      shift
    fi
    case "$type" in
      ssh-ed25519) ;;
      *) echo "only ssh-ed25519 keys are accepted: $type" >&2; exit 1 ;;
    esac
    case "$blob" in
      AAAA*) ;;
      *) echo "not an ssh public key blob: $blob" >&2; exit 1 ;;
    esac
    # -no-lock: rrsync's default per-user LOCK_EX|LOCK_NB would make concurrent
    # transfers from two runner hosts fail (clients serialize per artifact).
    # -munge: symlinks written by a client cannot point outside the hub dir.
    keys+="restrict,command=\"/usr/bin/rrsync -no-lock -munge ${CACHE_ROOT}/artifacts\" ${type} ${blob} ${comment}"$'\n'
  done
  if [ "$#" -ne 0 ]; then
    echo "unexpected trailing argument: $1" >&2
    exit 1
  fi
  install -d -m 0700 -o "$user" -g "$(id -gn "$user")" "$home/.ssh"
  local file="$home/.ssh/authorized_keys" begin="# BEGIN verity-ci-hub" end="# END verity-ci-hub"
  touch "$file"
  # Replace only the managed block; any other key in the file is kept.
  {
    awk -v b="$begin" -v e="$end" '$0==b{skip=1;next} $0==e{skip=0;next} !skip' "$file"
    printf '%s\n%s%s\n' "$begin" "$keys" "$end"
  } > "$file.new"
  mv "$file.new" "$file"
  chown "$user:$(id -gn "$user")" "$file"
  chmod 0600 "$file"
  echo "Authorized $(printf '%s' "$keys" | grep -c .) hub client key(s) for ${user}"
}

client_init() {
  require_root
  if [ "$#" -ne 3 ]; then
    usage >&2
    exit 1
  fi
  local target="$1" hostkey_type="$2" hostkey_blob="$3"
  local user home keydir host
  user="$(runner_user)"
  home="$(home_of "$user")"
  keydir="$home/.verity-ci-hub"
  host="${target#*@}"
  install -d -m 0700 -o "$user" -g "$(id -gn "$user")" "$keydir"
  if [ ! -f "$keydir/id_ed25519" ]; then
    runuser -u "$user" -- ssh-keygen -q -t ed25519 -N "" -C "verity-ci-hub@$(hostname)" -f "$keydir/id_ed25519"
  fi
  install -d -m 0755 "$CONF_DIR"
  printf '%s %s %s\n' "$host" "$hostkey_type" "$hostkey_blob" > "$CONF_DIR/hub_known_hosts"
  chmod 0644 "$CONF_DIR/hub_known_hosts"
  printf 'VERITY_CI_HUB_TARGET=%s\nVERITY_CI_HUB_KEY=%s\nVERITY_CI_HUB_KNOWN_HOSTS=%s\n' \
    "$target" "$keydir/id_ed25519" "$CONF_DIR/hub_known_hosts" > "$CONF_DIR/hub.env"
  chmod 0644 "$CONF_DIR/hub.env"
  cat "$keydir/id_ed25519.pub"
}

case "${1:-}" in
  server-init) shift; server_init "$@" ;;
  server-authorize) shift; server_authorize "$@" ;;
  client-init) shift; client_init "$@" ;;
  *) usage >&2; exit 1 ;;
esac
