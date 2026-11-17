#!/usr/bin/env bash
# Prebuild: render repository counts into git-ignored build outputs.
#
# Counts (tests, theorems, lines) are never committed, so concurrent PRs do not
# conflict on them; the docs build computes them from the checkout instead:
# - public/verification-status.txt: docs/VERIFICATION_STATUS.md with its
#   generated count sections filled, served at /verification-status.txt.
# - public/llms.txt: its GENERATED QUICK FACTS block, filled in place. The
#   committed block is empty; do not commit a filled one (make check fails).
#
# Without python3 the build continues and these outputs stay empty or absent.
# Runs with docs-site/ as the working directory.
set -euo pipefail

if ! command -v python3 >/dev/null 2>&1; then
  echo "generate-derived: python3 not found; skipping generated counts"
  exit 0
fi

python3 ../scripts/sync_verification_status_doc.py --write public/verification-status.txt
python3 ../scripts/update_doc_numbers.py --write
