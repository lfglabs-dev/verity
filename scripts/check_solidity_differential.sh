#!/bin/sh
set -eu
# Keep the caller's Lake workspace: this script also runs from downstream repos.
verity_test_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
verity_test_venv=".lake/slice-testing-venv"
if [ ! -x "$verity_test_venv/bin/python" ]; then
    python3 -m venv "$verity_test_venv"
fi
"$verity_test_venv/bin/python" -m pip install --disable-pip-version-check -q -r "$verity_test_root/scripts/solidity_differential/requirements.txt"
python3 "$verity_test_root/scripts/setup_solc_import.py" --output .lake/solidity-import/solc-0.8.34
exec "$verity_test_venv/bin/python" "$verity_test_root/scripts/solidity_import_differential.py" "$@"
