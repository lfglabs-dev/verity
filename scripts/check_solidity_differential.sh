#!/bin/sh
set -eu
# Keep the caller's Lake workspace: this script also runs from downstream repos.
verity_test_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
verity_test_venv=".lake/slice-testing-venv"
if [ ! -x "$verity_test_venv/bin/python" ] || ! "$verity_test_venv/bin/python" -m pip --version >/dev/null 2>&1; then
    rm -rf "$verity_test_venv"
    # Hosts without python3-venv lack ensurepip: bootstrap pip from a pinned wheel.
    if ! python3 -m venv "$verity_test_venv" >&2; then
        rm -rf "$verity_test_venv"
        python3 -m venv --without-pip "$verity_test_venv"
        verity_test_pip_wheel="$verity_test_venv/pip-24.3.1-py3-none-any.whl"
        curl -sSfL --retry 3 -o "$verity_test_pip_wheel" \
            https://files.pythonhosted.org/packages/ef/7d/500c9ad20238fcfcb4cb9243eede163594d7020ce87bd9610c9e02771876/pip-24.3.1-py3-none-any.whl
        echo "3790624780082365f47549d032f3770eeb2b1e8bd1f7b2e02dace1afa361b4ed  $verity_test_pip_wheel" | sha256sum -c - >&2
        "$verity_test_venv/bin/python" "$verity_test_pip_wheel/pip" install --disable-pip-version-check -q --no-index "$verity_test_pip_wheel" >&2
        rm -f "$verity_test_pip_wheel"
    fi
fi
verity_test_requirements="$verity_test_root/scripts/solidity_differential/requirements.txt"
verity_test_stamp="$verity_test_venv/.requirements.sha256"
verity_test_digest=$(python3 -c 'import hashlib, sys; print(hashlib.sha256(open(sys.argv[1], "rb").read()).hexdigest())' "$verity_test_requirements")
# Parallel mutation workers share this venv: install only when requirements change.
if [ ! -f "$verity_test_stamp" ] || [ "$(cat "$verity_test_stamp")" != "$verity_test_digest" ]; then
    "$verity_test_venv/bin/python" -m pip install --disable-pip-version-check -q -r "$verity_test_requirements"
    printf '%s\n' "$verity_test_digest" > "$verity_test_stamp"
fi
python3 "$verity_test_root/scripts/setup_solc_import.py" --output .lake/solidity-import/solc-0.8.34
python3 "$verity_test_root/scripts/setup_solc_import.py" --version 0.8.10 --output .lake/solidity-import/solc-0.8.10
exec "$verity_test_venv/bin/python" "$verity_test_root/scripts/solidity_import_differential.py" "$@"
