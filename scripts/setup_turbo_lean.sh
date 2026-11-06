#!/usr/bin/env bash
set -euo pipefail

# Provision host-cached `turbo-lean`, standalone Git >= 2.46 (`TURBO_LEAN_GIT`),
# and persistent `TURBO_LEAN_CACHE_DIR` for Verity CI jobs.
#
# All cold downloads/builds serialize on per-entry `flock` locks in
# `${LOCAL_CACHE_ROOT}/.locks` (matching `scripts/ci_local_persistence.sh` and
# `scripts/ci_host_maintenance.sh`) so parallel runners on a shared host build
# each version once and never race host maintenance eviction.

DEFAULT_TURBO_LEAN_COMMIT="6c6a8741769bf5f97bef0dfecdc1fb17924c3f67"
TURBO_LEAN_COMMIT="${TURBO_LEAN_COMMIT:-$DEFAULT_TURBO_LEAN_COMMIT}"
TURBO_LEAN_REPO_URL="${TURBO_LEAN_REPO_URL:-https://github.com/Th0rgal/turbo-lean.git}"
USE_STICKY_DISKS="${USE_STICKY_DISKS:-false}"
LOCAL_CACHE_ROOT="${LOCAL_CACHE_ROOT:-/srv/verity-ci-cache}"
GIT_STANDALONE_VERSION="${GIT_STANDALONE_VERSION:-2.47.1}"
GIT_STANDALONE_SHA256="${GIT_STANDALONE_SHA256:-f32be7ebe3fbac8eb5bd6beeb5bece2f14d12b9a5b6bc7b739c2b2c5b6e8d51c}"
ZLIB_VERSION="${ZLIB_VERSION:-1.3.1}"

usage() {
  cat <<'EOF'
Usage:
  scripts/setup_turbo_lean.sh [--use-sticky-disks true|false] [--local-cache-root DIR] [--commit SHA]
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --use-sticky-disks)
      USE_STICKY_DISKS="$2"
      shift 2
      ;;
    --local-cache-root)
      LOCAL_CACHE_ROOT="$2"
      shift 2
      ;;
    --commit)
      TURBO_LEAN_COMMIT="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "Unknown argument: $1" >&2
      usage >&2
      exit 1
      ;;
  esac
done

entry_lock_path() {
  local tree
  tree="$(dirname "$1")"
  printf '%s/.locks/%s__%s.lock' "$(dirname "$tree")" "$(basename "$tree")" "$(basename "$1")"
}

append_github_path() {
  local dir="$1"
  export PATH="${dir}:${PATH}"
  if [ -n "${GITHUB_PATH:-}" ]; then
    echo "${dir}" >> "${GITHUB_PATH}"
  fi
}

append_github_env() {
  local kv="$1"
  if [ -n "${GITHUB_ENV:-}" ]; then
    echo "${kv}" >> "${GITHUB_ENV}"
  fi
}

git_version_ge_2_46() {
  local git_bin="$1"
  local ver major minor
  ver="$("$git_bin" --version 2>/dev/null | awk '{print $3}')" || return 1
  major="${ver%%.*}"
  minor="${ver#*.}"
  minor="${minor%%.*}"
  case "$major" in
    ''|*[!0-9]*) return 1 ;;
  esac
  case "$minor" in
    ''|*[!0-9]*) return 1 ;;
  esac
  if [ "$major" -gt 2 ]; then
    return 0
  fi
  [ "$major" -eq 2 ] && [ "$minor" -ge 46 ]
}

cargo_version_ge_1_80() {
  local cargo_bin="$1"
  local ver major minor
  ver="$("$cargo_bin" --version 2>/dev/null | awk '{print $2}')" || return 1
  major="${ver%%.*}"
  minor="${ver#*.}"
  minor="${minor%%.*}"
  case "$major" in
    ''|*[!0-9]*) return 1 ;;
  esac
  case "$minor" in
    ''|*[!0-9]*) return 1 ;;
  esac
  if [ "$major" -gt 1 ]; then
    return 0
  fi
  [ "$major" -eq 1 ] && [ "$minor" -ge 80 ]
}

if [ "${USE_STICKY_DISKS}" = "true" ]; then
  CACHE_BASE="${LOCAL_CACHE_ROOT}"
else
  CACHE_BASE="${HOME}/.cache/verity-turbo-lean"
fi

OS_ARCH="$(uname -s)-$(uname -m)"

ensure_turbo_lean_git() {
  if [ -n "${TURBO_LEAN_GIT:-}" ] && [ -x "${TURBO_LEAN_GIT}" ] && git_version_ge_2_46 "${TURBO_LEAN_GIT}"; then
    export TURBO_LEAN_GIT
    append_github_env "TURBO_LEAN_GIT=${TURBO_LEAN_GIT}"
    return 0
  fi

  if command -v git >/dev/null 2>&1 && git_version_ge_2_46 "$(command -v git)"; then
    return 0
  fi

  local git_entry="${CACHE_BASE}/git/git-${GIT_STANDALONE_VERSION}-${OS_ARCH}"
  local git_bin="${git_entry}/bin/git"
  local lock fd
  lock="$(entry_lock_path "${git_entry}")"
  mkdir -p "$(dirname "${lock}")" "$(dirname "${git_entry}")"
  exec {fd}>"${lock}"
  if ! flock -x -w "${MOUNT_LOCK_TIMEOUT:-900}" "${fd}"; then
    echo "::error::timed out waiting for standalone Git build lock ${lock}" >&2
    exit 1
  fi

  if [ ! -x "${git_bin}" ] || ! git_version_ge_2_46 "${git_bin}"; then
    echo "System git ($(git --version 2>/dev/null || echo missing)) is older than 2.46; building standalone Git ${GIT_STANDALONE_VERSION}..."
    local tmpdir staging nproc_jobs
    tmpdir="$(mktemp -d)"
    staging="${git_entry}.building.$$"
    rm -rf "${staging}"
    nproc_jobs="$(nproc 2>/dev/null || echo 4)"

    (
      set -euo pipefail
      trap 'rm -rf "${tmpdir}" "${staging}"' EXIT

      local zlib_prefix="${tmpdir}/zlib-install"
      curl -sSfL --retry 3 --retry-delay 5 \
        "https://zlib.net/fossils/zlib-${ZLIB_VERSION}.tar.gz" \
        -o "${tmpdir}/zlib.tar.gz"
      tar -xzf "${tmpdir}/zlib.tar.gz" -C "${tmpdir}"
      (
        cd "${tmpdir}/zlib-${ZLIB_VERSION}"
        CFLAGS="-O2 -fPIC" ./configure --static --prefix="${zlib_prefix}" >/dev/null
        make -j"${nproc_jobs}" >/dev/null
        make install >/dev/null
      )

      curl -sSfL --retry 3 --retry-delay 5 \
        "https://www.kernel.org/pub/software/scm/git/git-${GIT_STANDALONE_VERSION}.tar.xz" \
        -o "${tmpdir}/git.tar.xz"
      tar -xJf "${tmpdir}/git.tar.xz" -C "${tmpdir}"
      (
        cd "${tmpdir}/git-${GIT_STANDALONE_VERSION}"
        make -j"${nproc_jobs}" \
          prefix="${staging}" \
          ZLIB_PATH="${zlib_prefix}" \
          NO_OPENSSL=YesPlease \
          NO_CURL=YesPlease \
          NO_EXPAT=YesPlease \
          NO_GETTEXT=YesPlease \
          NO_TCLTK=YesPlease \
          NO_PERL=YesPlease \
          NO_PYTHON=YesPlease \
          CFLAGS="-O2 -I${zlib_prefix}/include" \
          LDFLAGS="-L${zlib_prefix}/lib" \
          git >/dev/null
        mkdir -p "${staging}/bin"
        cp -f git "${staging}/bin/git"
        chmod +x "${staging}/bin/git"
      )
      rm -rf "${git_entry}"
      mv "${staging}" "${git_entry}"
      trap - EXIT
      rm -rf "${tmpdir}"
    )
  fi

  touch "${git_entry}"
  exec {fd}>&-

  # Export TURBO_LEAN_GIT without prepending standalone no-curl Git ahead of /usr/bin/git on PATH.
  export TURBO_LEAN_GIT="${git_bin}"
  append_github_env "TURBO_LEAN_GIT=${git_bin}"
  echo "Configured TURBO_LEAN_GIT=${git_bin} ($(${git_bin} --version))"
}

ensure_rust_toolchain() {
  local candidate
  for candidate in "$(command -v cargo 2>/dev/null || true)" "${HOME}/.cargo/bin/cargo"; do
    if [ -n "${candidate}" ] && [ -x "${candidate}" ] && cargo_version_ge_1_80 "${candidate}"; then
      export PATH="$(dirname "${candidate}"):${PATH}"
      return 0
    fi
  done

  local rust_entry="${CACHE_BASE}/rustup/stable-${OS_ARCH}"
  local lock fd
  lock="$(entry_lock_path "${rust_entry}")"
  mkdir -p "$(dirname "${lock}")" "${rust_entry}"
  exec {fd}>"${lock}"
  if ! flock -x -w "${MOUNT_LOCK_TIMEOUT:-900}" "${fd}"; then
    echo "::error::timed out waiting for rustup lock ${lock}" >&2
    exit 1
  fi

  export RUSTUP_HOME="${rust_entry}/rustup"
  export CARGO_HOME="${rust_entry}/cargo"
  export PATH="${CARGO_HOME}/bin:${PATH}"

  if [ ! -x "${CARGO_HOME}/bin/cargo" ] || ! cargo_version_ge_1_80 "${CARGO_HOME}/bin/cargo"; then
    echo "Installing minimal stable Rust toolchain into ${rust_entry}..."
    if [ -x "${CARGO_HOME}/bin/rustup" ]; then
      "${CARGO_HOME}/bin/rustup" toolchain install stable --profile minimal
      "${CARGO_HOME}/bin/rustup" default stable
    else
      curl --proto '=https' --tlsv1.2 -sSf --retry 3 --retry-delay 5 https://sh.rustup.rs \
        | sh -s -- -y --no-modify-path --default-toolchain stable --profile minimal
    fi
  fi

  touch "${rust_entry}"
  exec {fd}>&-
}

ensure_turbo_lean_binary() {
  local turbo_entry="${CACHE_BASE}/turbo-lean/turbo-lean-${TURBO_LEAN_COMMIT}-${OS_ARCH}"
  local turbo_bin="${turbo_entry}/bin/turbo-lean"
  local lock fd
  lock="$(entry_lock_path "${turbo_entry}")"
  mkdir -p "$(dirname "${lock}")" "$(dirname "${turbo_entry}")"
  exec {fd}>"${lock}"
  if ! flock -x -w "${MOUNT_LOCK_TIMEOUT:-1200}" "${fd}"; then
    echo "::error::timed out waiting for turbo-lean build lock ${lock}" >&2
    exit 1
  fi

  if [ ! -x "${turbo_bin}" ] || [ "$(cat "${turbo_entry}/.commit" 2>/dev/null || true)" != "${TURBO_LEAN_COMMIT}" ]; then
    ensure_rust_toolchain
    echo "Building turbo-lean @ ${TURBO_LEAN_COMMIT} (${OS_ARCH})..."
    local tmpdir staging
    tmpdir="$(mktemp -d)"
    staging="${turbo_entry}.building.$$"
    rm -rf "${staging}"

    (
      set -euo pipefail
      trap 'rm -rf "${tmpdir}" "${staging}"' EXIT

      git init -q "${tmpdir}/src"
      git -C "${tmpdir}/src" remote add origin "${TURBO_LEAN_REPO_URL}"
      git -C "${tmpdir}/src" fetch --depth 1 origin "${TURBO_LEAN_COMMIT}"
      git -C "${tmpdir}/src" checkout -q FETCH_HEAD

      cargo build --release --locked --manifest-path "${tmpdir}/src/Cargo.toml"

      mkdir -p "${staging}/bin"
      cp -f "${tmpdir}/src/target/release/turbo-lean" "${staging}/bin/turbo-lean"
      chmod +x "${staging}/bin/turbo-lean"
      printf '%s\n' "${TURBO_LEAN_COMMIT}" > "${staging}/.commit"

      rm -rf "${turbo_entry}"
      mv "${staging}" "${turbo_entry}"
      trap - EXIT
      rm -rf "${tmpdir}"
    )
  fi

  touch "${turbo_entry}"
  exec {fd}>&-

  append_github_path "${turbo_entry}/bin"
  "${turbo_bin}" --version
}

configure_turbo_lean_env() {
  export TURBO_LEAN_TELEMETRY="${TURBO_LEAN_TELEMETRY:-off}"
  append_github_env "TURBO_LEAN_TELEMETRY=${TURBO_LEAN_TELEMETRY}"

  if [ "${USE_STICKY_DISKS}" = "true" ]; then
    local toolchain_hash="default"
    if [ -f "lean-toolchain" ]; then
      toolchain_hash="$(sha256sum lean-toolchain | awk '{print substr($1, 1, 16)}')"
    fi
    local cas_entry="${CACHE_BASE}/turbo-lean-cas/cas-${OS_ARCH}-${toolchain_hash}"
    local lock fd
    lock="$(entry_lock_path "${cas_entry}")"
    mkdir -p "$(dirname "${lock}")" "${cas_entry}"
    exec {fd}>"${lock}"
    if flock -x -w "${MOUNT_LOCK_TIMEOUT:-600}" "${fd}"; then
      touch "${cas_entry}"
    fi
    exec {fd}>&-
    export TURBO_LEAN_CACHE_DIR="${cas_entry}"
    append_github_env "TURBO_LEAN_CACHE_DIR=${cas_entry}"
  fi
}

ensure_turbo_lean_git
ensure_turbo_lean_binary
configure_turbo_lean_env
