#!/usr/bin/env python3
"""Deprecated shim: this report now lives in scripts/property_pipeline.py (`report`).

Prefer `python3 scripts/property_pipeline.py report [--format ...] [--fail-below ...]`.
This wrapper is kept so existing callers of this path keep working.
"""

from __future__ import annotations

import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from property_pipeline import main as pipeline_main


def main() -> int:
    return pipeline_main(["report", *sys.argv[1:]])


if __name__ == "__main__":
    raise SystemExit(main())
