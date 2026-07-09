#!/usr/bin/env bash
set -euo pipefail

# Temporary compatibility shim for Alibaba OpenCodeReview 1.7.5.
# OCR's code_search invokes: git --no-pager grep ... --end-of-options <validated-ref> -- <pathspec>
# Some Git versions (including 2.43 on Ubuntu 24.04) do not accept --end-of-options
# in `git grep` and treat it as the revision, causing:
#   fatal: unable to resolve revision: --end-of-options
# OCR validates PR refs before invoking git grep, and this workflow supplies a GitHub
# commit SHA as --to, so dropping the unsupported flag for grep only preserves review
# functionality without widening the workflow's trust boundary.

real_git=/usr/bin/git

is_grep=false
for arg in "$@"; do
  if [[ "$arg" == "grep" ]]; then
    is_grep=true
    break
  fi
done

if $is_grep; then
  filtered=()
  for arg in "$@"; do
    [[ "$arg" == "--end-of-options" ]] && continue
    filtered+=("$arg")
  done
  exec "$real_git" "${filtered[@]}"
fi

exec "$real_git" "$@"
