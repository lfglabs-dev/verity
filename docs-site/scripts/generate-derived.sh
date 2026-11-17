#!/usr/bin/env bash
# Prebuild: render repository counts into git-ignored build outputs.
#
# Counts (tests, theorems, lines) are never committed, so concurrent PRs do not
# conflict on them; the docs build computes them from the checkout instead:
# - public/verification-status.txt: docs/VERIFICATION_STATUS.md with its
#   generated count sections filled, served at /verification-status.txt.
# - public/llms.txt (served at /llms.txt): llms.template.txt with its
#   GENERATED QUICK FACTS block filled.
#
# Without python3 the build continues: public/llms.txt is the template with an
# empty quick-facts block, and public/verification-status.txt is absent.
# `--fast` (used by `npm run dev`) does the same on purpose: computing the counts
# takes ~40 s, and only real builds publish them.
# Runs with docs-site/ as the working directory.
set -euo pipefail

if [ "${1:-}" = "--fast" ] || ! command -v python3 >/dev/null 2>&1; then
  if [ "${1:-}" = "--fast" ]; then reason="fast mode (npm run dev)"; else reason="python3 not found"; fi
  echo "generate-derived: $reason; skipping generated counts"
  cp llms.template.txt public/llms.txt
  exit 0
fi

python3 ../scripts/sync_verification_status_doc.py --write public/verification-status.txt
python3 ../scripts/update_doc_numbers.py --write --output public/llms.txt
