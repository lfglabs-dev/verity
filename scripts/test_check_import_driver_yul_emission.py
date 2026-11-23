"""Tests for `check_import_driver_yul_emission.py`."""
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_import_driver_yul_emission import offending_lines  # noqa: E402


class ImportDriverYulEmissionTests(unittest.TestCase):
    def _tree(self, files: dict[str, str]) -> Path:
        root = Path(tempfile.mkdtemp())
        for rel, text in files.items():
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        return root

    def test_plain_emit_in_model_driver_is_reported(self) -> None:
        root = self._tree({"Contracts/X/FooModel.lean":
            "IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))\n"})
        self.assertEqual(len(offending_lines(root)), 1)

    def test_plain_emit_in_pinned_template_is_reported(self) -> None:
        root = self._tree({"scripts/solidity_differential/pinned.py":
            "      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))\n"})
        self.assertEqual(len(offending_lines(root)), 1)

    def test_other_spellings_are_reported(self) -> None:
        root = self._tree({"Contracts/X/BarModel.lean":
            "open Compiler in\nIO.FS.writeFile o (Yul.render <| emitYul compiled)\n"})
        self.assertEqual(len(offending_lines(root)), 1)

    def test_spilled_emit_and_unit_tests_pass(self) -> None:
        root = self._tree({
            "Contracts/X/FooModel.lean":
                "IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))\n",
            "Compiler/FooTest.lean": "pure (Compiler.Yul.render (Compiler.emitYul ir))\n",
            "Contracts/X/Proofs/Native.lean": "(Compiler.emitYul c).runtimeCode = x\n",
        })
        self.assertEqual(offending_lines(root), [])

    def test_current_repo_tree_is_clean(self) -> None:
        self.assertEqual(offending_lines(Path(__file__).resolve().parents[1]), [])


if __name__ == "__main__":
    unittest.main()
