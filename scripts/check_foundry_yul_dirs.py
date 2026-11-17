#!/usr/bin/env python3
"""Foundry tests never read or write the committed `artifacts/yul/` snapshots.

`artifacts/yul/*.yul` are committed snapshots that are not regenerated with the
compiler. Tests read Yul from `compiler/yul` / `compiler/yul-smoke` (what CI
generates, or what `test/yul/YulTestBase.sol` compiles on demand). A test that
fell back to `artifacts/yul` tested stale Yul, and its on-demand manifest compile
rewrote the tracked snapshots while parallel suites were reading them.

Usage: python3 scripts/check_foundry_yul_dirs.py [--root DIR]
Silent and exit 0 when no Solidity string literal under `test/` starts with
`artifacts/yul`;
otherwise lists the offending lines and exits 1.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# A Solidity string literal starting with the directory (comments may name it).
_FORBIDDEN = re.compile(r"\"artifacts/yul(?![\w-])")


def offending_lines(root: Path) -> list[str]:
    """`path:line: text` for every Solidity line under `test/` naming `artifacts/yul`."""
    out: list[str] = []
    for path in sorted((root / "test").rglob("*.sol")):
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if _FORBIDDEN.search(line):
                out.append(f"{path.relative_to(root)}:{number}: {line.strip()}")
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args(argv)
    bad = offending_lines(args.root)
    if bad:
        print("Foundry tests must not use the committed artifacts/yul snapshots "
              "(read compiler/yul via YulTestBase._yulDir()):", file=sys.stderr)
        for line in bad:
            print(f"  {line}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
