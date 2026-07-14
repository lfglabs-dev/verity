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

if ! command -v elan >/dev/null 2>&1; then
  echo "::error::elan is required on the OCR runner to collect Lean LSP evidence"
  exit 1
fi

# ELAN_HOME is supplied by the workflow and must be per-run, never a shared
# runner installation.  This prevents a PR-selected toolchain from persisting
# on the self-hosted host.
: "${ELAN_HOME:?ELAN_HOME must point to a per-run directory}"
mkdir -p "$ELAN_HOME"
elan toolchain install "$toolchain"
elan run "$toolchain" lean --version

printf 'LEAN_TOOLCHAIN=%s\n' "$toolchain" >> "$GITHUB_ENV"
