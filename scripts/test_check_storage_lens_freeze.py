#!/usr/bin/env python3
"""Regression tests for the C5 storage-lens freeze boundary."""

from __future__ import annotations

import contextlib
import io
import tempfile
import unittest
from pathlib import Path

import check_storage_lens_freeze


class StorageLensFreezeTests(unittest.TestCase):
    def run_gate(self, files: dict[str, str]) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            for relative, contents in files.items():
                target = root / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(contents, encoding="utf-8")
            old_root = check_storage_lens_freeze.ROOT
            old_baseline = check_storage_lens_freeze.BASELINE
            try:
                check_storage_lens_freeze.ROOT = root
                check_storage_lens_freeze.BASELINE = {}
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    status = check_storage_lens_freeze.main()
                return status, output.getvalue()
            finally:
                check_storage_lens_freeze.ROOT = old_root
                check_storage_lens_freeze.BASELINE = old_baseline

    def test_rejects_contracts_storage_words_bypass(self) -> None:
        status, output = self.run_gate({
            "Contracts/Bypass.lean": "def bypass (s : ContractState) := { s with storageWords := fun _ => 0 }\n",
        })
        self.assertEqual(status, 1)
        self.assertIn("Contracts/Bypass.lean", output)

    def test_rejects_compiler_contract_state_transient_bypass(self) -> None:
        status, output = self.run_gate({
            "Compiler/Bypass.lean": (
                "def bypass (world : Verity.ContractState) :=\n"
                "  { world with transientStorage := fun _ => 0 }\n"
            ),
        })
        self.assertEqual(status, 1)
        self.assertIn("Compiler/Bypass.lean", output)

    def test_ignores_compiler_ir_state_field_collision(self) -> None:
        status, output = self.run_gate({
            "Compiler/IRState.lean": (
                "structure IRState where transientStorage : Nat → Nat\n"
                "def update (state : IRState) := { state with transientStorage := fun _ => 0 }\n"
            ),
        })
        self.assertEqual(status, 0, output)


if __name__ == "__main__":
    unittest.main()
