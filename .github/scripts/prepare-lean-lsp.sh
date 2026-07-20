#!/usr/bin/env bash
# Prepare only the Lean toolchain named by the checked-out repository.  This is
# intentionally a trusted workflow helper: it validates untrusted PR metadata
# before it reaches elan and keeps the installed toolchain in the run temp dir.
set -euo pipefail

repo=${1:?usage: prepare-lean-lsp.sh REPOSITORY_ROOT}
toolchain_file="$repo/lean-toolchain"

if [ ! -f "$toolchain_file" ]; then
  echo "::error::Lean LSP evidence requires a repository-root lean-toolchain file"
  exit 1
fi

toolchain="$(tr -d '\r\n' < "$toolchain_file")"
if ! [[ "$toolchain" =~ ^leanprover/lean4:v4\.[0-9]+\.[0-9]+$ ]]; then
  echo "::error::Refusing non-pinned or unsupported Lean toolchain value"
  exit 1
fi

# ELAN_HOME is supplied by the workflow and must be per-run, never a shared
# runner installation.  This prevents a PR-selected toolchain from persisting
# on the self-hosted host.  Bootstrap the pinned elan client there as well: the
# OCR runner pool need not expose a host-installed elan on PATH.
: "${ELAN_HOME:?ELAN_HOME must point to a per-run directory}"
mkdir -p "$ELAN_HOME"

elan_bin="$ELAN_HOME/bin/elan"
if [ ! -x "$elan_bin" ]; then
  elan_version='v4.1.2'
  elan_archive='elan-x86_64-unknown-linux-gnu.tar.gz'
  elan_sha256='f81c2e48c1588d4612cd2c8851947898a45ac8d72748a07dff3a5694f1cf589b'
  elan_url="https://github.com/leanprover/elan/releases/download/${elan_version}/${elan_archive}"
  if [ "${PREPARE_LEAN_LSP_TESTING:-}" = "1" ]; then
    elan_archive="${PREPARE_LEAN_LSP_TEST_ELAN_ARCHIVE:-$elan_archive}"
    elan_sha256="${PREPARE_LEAN_LSP_TEST_ELAN_SHA256:-$elan_sha256}"
    elan_url="${PREPARE_LEAN_LSP_TEST_ELAN_URL:-$elan_url}"
  fi
  tmpdir="$(mktemp -d)"
  trap 'rm -rf "$tmpdir"' EXIT
  curl -fsSL --retry 3 --retry-delay 5 --connect-timeout 20 --max-time 120 "$elan_url" -o "$tmpdir/$elan_archive"
  printf '%s  %s\n' "$elan_sha256" "$tmpdir/$elan_archive" | sha256sum -c -
  tar -xzf "$tmpdir/$elan_archive" -C "$tmpdir"
  ELAN_HOME="$ELAN_HOME" "$tmpdir/elan-init" -y --no-modify-path --default-toolchain none
  trap - EXIT
  rm -rf "$tmpdir"
fi

export PATH="$ELAN_HOME/bin:$PATH"
if [ -n "${GITHUB_PATH:-}" ]; then
  printf '%s\n' "$ELAN_HOME/bin" >> "$GITHUB_PATH"
fi
"$elan_bin" toolchain install "$toolchain"
"$elan_bin" run "$toolchain" lean --version

printf 'LEAN_TOOLCHAIN=%s\n' "$toolchain" >> "$GITHUB_ENV"
