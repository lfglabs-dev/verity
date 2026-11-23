#!/usr/bin/env python3
"""Tests for check_importer_name_selection.py: the repository passes, and each way of selecting
a lowering by name, or around the trusted shortcut registry, fails."""
from __future__ import annotations

import shutil
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_importer_name_selection as lint

REPO = SCRIPT_DIR.parent
IMPORT = "Compiler/SolidityImport/Import.lean"
REGISTRY = "Compiler/SolidityImport/InlineAssemblyShims.lean"
EVIDENCE = [
    "Contracts/SolidityImportSmoke/RootArrayReturnStateCountChecks.lean",
    "Contracts/SolidityImportSmoke/TailAssemblyArrayReadChecks.lean",
    "Contracts/SolidityImportSmoke/TailAssemblyRangeReadChecks.lean",
]


class ImporterNameSelectionTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        shutil.copytree(REPO / "Compiler/SolidityImport", self.root / "Compiler/SolidityImport")
        for ev in EVIDENCE:
            (self.root / ev).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(REPO / ev, self.root / ev)

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def edit(self, rel: str, old: str, new: str) -> None:
        path = self.root / rel
        text = path.read_text(encoding="utf-8")
        self.assertEqual(text.count(old), 1, f"{old!r} must occur once in {rel}")
        path.write_text(text.replace(old, new), encoding="utf-8")

    def append(self, rel: str, code: str) -> None:
        path = self.root / rel
        path.write_text(path.read_text(encoding="utf-8") + code, encoding="utf-8")

    def assertFails(self, needle: str) -> None:
        errors = lint.run(self.root)
        self.assertTrue(any(needle in e for e in errors), "\n".join(errors) or "no error")

    def test_repository_passes(self) -> None:
        self.assertEqual(lint.run(REPO), [])

    def test_copy_passes(self) -> None:
        self.assertEqual(lint.run(self.root), [])

    def test_function_name_comparison_fails(self) -> None:
        self.append(IMPORT, '\ndef isHookHelper (callee : Json) : Bool :=\n'
                    '  optStr callee "name" == some "callHook"\n')
        self.assertFails("`callHook`")

    def test_library_name_match_arm_fails(self) -> None:
        self.append(IMPORT, '\ndef isCurrency : Option String → Bool\n'
                    '  | some "CurrencyLibrary" => true\n  | _ => false\n')
        self.assertFails("`CurrencyLibrary`")

    def test_qualified_name_in_list_fails(self) -> None:
        self.append(IMPORT, '\ndef isFlip (n : String) : Bool :=\n'
                    '  ["TickBitmap.flipTick", "flipTick"].contains n\n')
        self.assertFails("`flipTick`")

    def test_yul_variable_lookup_outside_registry_gate_fails(self) -> None:
        self.append(IMPORT, '\ndef startOf (env : Env) : Option Expr :=\n'
                    '  env.yulNames.find? "startSlot"\n')
        self.assertFails("`startSlot`")

    def test_range_names_before_registry_match_fail(self) -> None:
        self.edit(IMPORT,
                  "  let m ← matchTrustedShortcut? asm\n"
                  "  guard (m.shortcut.lowering == .rangeStorageRead)\n",
                  "  let m ← matchTrustedShortcut? asm\n")
        self.assertFails("before the block matched the trusted shortcut registry")

    def test_fingerprint_constant_outside_registry_fails(self) -> None:
        self.append(IMPORT, '\ndef isRange (asm : Json) : Bool :=\n'
                    '  yulBlockFingerprint asm == extsloadRangeYulFingerprint\n')
        self.assertFails("extsloadRangeYulFingerprint outside the registry")
        self.assertFails("compares a yulBlockFingerprint outside the registry")

    def test_shim_lowering_outside_registry_fails(self) -> None:
        self.append(IMPORT, '\ndef lowerCallHookShim : Nat := 0\n')
        self.assertFails("lowerCallHookShim defined outside the registry module")

    def test_registry_name_must_be_its_constant(self) -> None:
        self.edit(REGISTRY,
                  "fingerprintName := (``exttloadBatchYulFingerprint).getString!",
                  "fingerprintName := (``extsloadBatchYulFingerprint).getString!")
        self.assertFails("fingerprintName names extsloadBatchYulFingerprint")

    def test_registry_evidence_must_exist(self) -> None:
        (self.root / EVIDENCE[2]).unlink()
        self.assertFails("does not exist")

    def test_registry_fingerprints_distinct(self) -> None:
        self.edit(REGISTRY,
                  '"fde99fddf01f23a921eb50aadccf35541f1d93ab92ea966af76de65e839097f8"',
                  '"be5cd0027ebaa78d230b732c81cebe4339c348553867668201b357cc758aae83"')
        self.assertFails("have the same fingerprint")

    def test_match_constructor_stays_private(self) -> None:
        self.edit(REGISTRY, "  private mk ::\n", "")
        self.assertFails("private mk")

    def test_lowering_must_take_a_match_and_record(self) -> None:
        self.edit(REGISTRY,
                  "def lowerBatchRangeSloadShim (m : TrustedShortcutMatch) (startSlotExpr nSlotsExpr : Expr) :",
                  "def lowerBatchRangeSloadShim (startSlotExpr nSlotsExpr : Expr) :")
        self.assertFails("lowerBatchRangeSloadShim must take `(m : TrustedShortcutMatch)` first")

    def test_unregistered_fingerprint_constant_fails(self) -> None:
        self.append(REGISTRY, '\ndef callHookYulFingerprint : String :=\n  "'
                    + "0" * 64 + '"\n')
        self.assertFails("callHookYulFingerprint is defined but no registry entry uses it")

    def test_comments_are_ignored(self) -> None:
        self.append(IMPORT, '\n-- optStr callee "name" == some "callHook"\n'
                    '/- | "CurrencyLibrary" => true -/\n')
        self.assertEqual(lint.run(self.root), [])


if __name__ == "__main__":
    unittest.main()
