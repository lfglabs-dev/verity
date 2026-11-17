#!/usr/bin/env bash
set -euo pipefail

# Vercel ignoreCommand contract:
# - exit 0 => skip build/deployment
# - exit 1 => continue build/deployment
#
# Skips builds that cannot change the site: draft PRs, and PRs or pushes that
# touch nothing under docs-site/. Anything this script cannot determine builds
# (fails open). Runs with docs-site/ as the working directory.

# Not a PR deployment (branch push, including main): build only when docs-site/
# changed since the last deployed commit, when that commit is in the clone.
if [ -z "${VERCEL_GIT_PULL_REQUEST_ID:-}" ]; then
  prev="${VERCEL_GIT_PREVIOUS_SHA:-}"
  if [ -n "$prev" ] && git cat-file -e "${prev}^{commit}" 2>/dev/null; then
    if git diff --quiet "$prev" HEAD -- .; then
      echo "No docs-site changes since ${prev}; skipping Vercel build"
      exit 0
    fi
    echo "docs-site changed since ${prev}; continuing build"
    exit 1
  fi
  echo "Not a PR deployment and no previous deployment to compare; continuing build"
  exit 1
fi

# If no GitHub token is configured, fail open and continue build.
if [ -z "${GITHUB_TOKEN:-}" ]; then
  echo "GITHUB_TOKEN missing; continuing build"
  exit 1
fi

owner="${VERCEL_GIT_REPO_OWNER:-}"
repo="${VERCEL_GIT_REPO_SLUG:-}"
pr="${VERCEL_GIT_PULL_REQUEST_ID:-}"

if [ -z "$owner" ] || [ -z "$repo" ]; then
  echo "Repository metadata missing; continuing build"
  exit 1
fi

api_url="https://api.github.com/repos/${owner}/${repo}/pulls/${pr}"
gh_get() {
  curl -fsSL \
    -H "Authorization: Bearer ${GITHUB_TOKEN}" \
    -H "Accept: application/vnd.github+json" \
    "$1"
}

response="$(gh_get "$api_url")"

is_draft="$(printf '%s' "$response" | python3 -c 'import json,sys; print(str(json.load(sys.stdin).get("draft", False)).lower())')"

if [ "$is_draft" = "true" ]; then
  echo "Draft PR detected; skipping Vercel build"
  exit 0
fi

# Ready PR: build only if it changes a file under docs-site/. The files API
# pages 100 at a time and lists at most 3000 files; a PR at that cap builds.
touches_docs=false
page=1
while [ "$page" -le 30 ]; do
  files="$(gh_get "${api_url}/files?per_page=100&page=${page}" || echo FAIL)"
  if [ "$files" = "FAIL" ]; then
    echo "Could not list PR files; continuing build"
    exit 1
  fi
  verdict="$(printf '%s' "$files" | python3 -c '
import json, sys
fs = json.load(sys.stdin)
docs = any(f.get("filename", "").startswith("docs-site/") or f.get("previous_filename", "").startswith("docs-site/") for f in fs)
print("docs" if docs else ("more" if len(fs) == 100 else "done"))')"
  case "$verdict" in
    docs) touches_docs=true; break ;;
    done) break ;;
  esac
  page=$((page + 1))
done

if [ "$page" -gt 30 ]; then
  echo "PR lists 3000+ files; continuing build"
  exit 1
fi

if [ "$touches_docs" = "false" ]; then
  echo "PR does not change docs-site/; skipping Vercel build"
  exit 0
fi

echo "PR is ready for review and changes docs-site/; continuing build"
exit 1
