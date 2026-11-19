#!/usr/bin/env python3
"""Every import-abi mutant's anchor occurs exactly once in Import.lean.

The mutation campaign only runs when the importer changes, and an anchor that no
longer matches makes its mutant a harness error, not a detection. A reindent of
the root scalar guards (#2675) left five of these mutants unable to apply. This
test catches such drift in the fast suite.
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from solidity_differential.check_abi_mutations import MUTANTS

IMPORT_LEAN = SCRIPT_DIR.parent / "Compiler" / "SolidityImport" / "Import.lean"


class AbiMutantAnchorTests(unittest.TestCase):
    def test_every_anchor_occurs_exactly_once(self) -> None:
        text = IMPORT_LEAN.read_text(encoding="utf-8")
        counts = {name: text.count(before) for name, (before, _after) in MUTANTS.items()}
        self.assertEqual({name: n for name, n in counts.items() if n != 1}, {})

    def test_every_mutant_changes_its_anchor(self) -> None:
        for name, (before, after) in MUTANTS.items():
            with self.subTest(name=name):
                self.assertNotEqual(before, after)


if __name__ == "__main__":
    unittest.main()
