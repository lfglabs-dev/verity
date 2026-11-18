#!/usr/bin/env python3
"""List the Lean modules whose Yul the Foundry tests compile on demand.

A Foundry test compiles a Verity module locally through
`deployCompiledVerityModule("Contracts.X", ...)` or
`_ensureVerityModuleYul("Contracts.X", ...)` (test/yul/YulTestBase.sol).
CI's Foundry jobs have no Lean toolchain, so `.github/workflows/verify.yml`
prebuilds the Yul of every such module from this script's output.

Prints the string-literal first argument of every such call in `test/**/*.sol`
(comments ignored, calls may span several lines), one per line, sorted and
deduplicated. Exits 1 when no module is found.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HELPERS = ("deployCompiledVerityModule", "_ensureVerityModuleYul")
# Floor on the number of distinct modules found under test/: the 26 modules of the
# hand-maintained lists this script replaced. Fewer means the scan regressed (a parser
# change, a renamed helper) and would silently stop prebuilding modules, so it fails
# instead. Raise it when smoke tests are added; never lower it to make CI pass.
MIN_MODULES = 26

_CALL = re.compile(r"\b(?:" + "|".join(HELPERS) + r")\s*\(\s*\"([^\"\\]+)\"")
# String literals are matched first so that `//` inside a string is kept.
_TOKEN = re.compile(r'"(?:[^"\\\n]|\\.)*"|//[^\n]*|/\*.*?\*/', re.DOTALL)


def strip_comments(source: str) -> str:
    """Remove Solidity comments, keeping string literals and line structure."""

    def repl(match: re.Match[str]) -> str:
        token = match.group(0)
        if token.startswith('"'):
            return token
        return "\n" * token.count("\n") or " "

    return _TOKEN.sub(repl, source)


def modules_in_source(source: str) -> set[str]:
    """Modules named by a string-literal first argument of a compile helper."""
    return set(_CALL.findall(strip_comments(source)))


def list_smoke_modules(test_dir: Path) -> list[str]:
    """Sorted, deduplicated modules compiled on demand by tests under `test_dir`."""
    modules: set[str] = set()
    for path in sorted(test_dir.rglob("*.sol")):
        modules |= modules_in_source(path.read_text(encoding="utf-8"))
    return sorted(modules)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--test-dir", type=Path, default=ROOT / "test", help="Foundry test root (default: test/)"
    )
    parser.add_argument(
        "--min-modules", type=int, default=MIN_MODULES,
        help=f"fail if fewer distinct modules are found (default: {MIN_MODULES})",
    )
    args = parser.parse_args(argv)
    modules = list_smoke_modules(args.test_dir)
    if len(modules) < args.min_modules:
        print(f"found {len(modules)} on-demand Verity module(s) under {args.test_dir}, "
              f"expected at least {args.min_modules}", file=sys.stderr)
        return 1
    print("\n".join(modules))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
