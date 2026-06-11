#!/usr/bin/env python3
"""Deprecated shim: this checker now lives in scripts/docsync.py (entry `low_level_call_boundary`).

Prefer `python3 scripts/docsync.py --check --only low_level_call_boundary`.
This wrapper is kept so existing callers of this path keep working.
"""

from __future__ import annotations

import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from docsync import run_entry

ENTRY = "low_level_call_boundary"


def main() -> int:
    return run_entry(ENTRY)


if __name__ == "__main__":
    raise SystemExit(main())
