#!/usr/bin/env python3
"""Import model drivers render the Yul they hand to solc with `Compiler.emitYulSpilled`.

The stateful differential drivers (`Contracts/**/*Model.lean`), the importer's `describe`
entrypoint (`Compiler/SolidityImport/`) and the generated pinned-sequence driver
(`scripts/solidity_differential/`) all write Yul that solc must assemble. Plain
`Compiler.emitYul` skips the temporary spill pass, so a model with many live temporaries fails
with StackTooDeep (#2831). Lean unit tests that only inspect rendered text are out of scope.

Usage: python3 scripts/check_import_driver_yul_emission.py [--root DIR]
Silent and exit 0 when no driver renders plain `Compiler.emitYul`; otherwise lists the
offending lines and exits 1.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

_PLAIN_EMIT = re.compile(r"Compiler\.Yul\.render\s*\(\s*Compiler\.emitYul\s")
_SCOPES = (
    ("Contracts", "*.lean"),
    ("Compiler/SolidityImport", "*.lean"),
    ("scripts/solidity_differential", "*.py"),
)


def offending_lines(root: Path) -> list[str]:
    """`path:line: text` for every driver line rendering plain `Compiler.emitYul`."""
    out: list[str] = []
    for directory, pattern in _SCOPES:
        for path in sorted((root / directory).rglob(pattern)):
            text = path.read_text(encoding="utf-8")
            for number, line in enumerate(text.splitlines(), 1):
                if _PLAIN_EMIT.search(line):
                    out.append(f"{path.relative_to(root)}:{number}: {line.strip()}")
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    bad = offending_lines(args.root)
    if bad:
        print("Import drivers must render `Compiler.emitYulSpilled`, not `Compiler.emitYul` (#2831):")
        print("\n".join(bad))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
