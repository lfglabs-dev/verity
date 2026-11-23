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

    def test_literal_on_the_left_fails(self) -> None:
        self.append(IMPORT, '\ndef isHook (n : String) : Bool := "callHook" == n\n')
        self.assertFails("`callHook`")

    def test_prop_equality_fails(self) -> None:
        self.append(IMPORT, '\ndef isCurrency (n : String) : Bool := decide (n = "CurrencyLibrary")\n')
        self.assertFails("`CurrencyLibrary`")
        self.append(IMPORT, '\ndef notFlip (n : String) : Prop := n ≠ "flipTick"\n')
        self.assertFails("`flipTick`")

    def test_prefix_test_fails(self) -> None:
        self.append(IMPORT, '\ndef isHook (n : String) : Bool := "callHook".isPrefixOf n\n')
        self.assertFails("`callHook`")

    def test_named_name_constant_fails(self) -> None:
        self.append(IMPORT, '\ndef hookName : String := "callHook"\n'
                    'def isHook (n : String) : Bool := n == hookName\n')
        self.assertFails("named string constant")

    def test_shortcut_lowering_outside_registry_fails(self) -> None:
        self.append(IMPORT, '\ndef lowerSwapStepShortcut : Nat := 0\n')
        self.assertFails("lowerSwapStepShortcut defined outside the registry module")

    def test_name_literal_in_any_position_fails(self) -> None:
        forms = [
            'def a (n : String) : Bool := decide (n ∈ ["callHook"])',
            'def a (ns : List String) : Bool := decide ("callHook" ∈ ns)',
            'def a (n : String) : Bool := if let "callHook" := n then true else false',
            'def a (n : String) : Bool :=\n  match n with\n  | "callHook"\n    => true\n  | _ => false',
            'def zzs : List String := ["callHook", "flipTick"]',
            'def zz : String × Nat := ("callHook", 2)',
            'def a (n : String) : Bool :=\n  let h := "callHook"\n  n == h',
            'def a (n : String) : Bool := String.isPrefixOf "callHook" n',
            'def a (n : String) : Bool := bne n "callHook"',
        ]
        original = (self.root / IMPORT).read_text(encoding="utf-8")
        for form in forms:
            with self.subTest(form=form):
                (self.root / IMPORT).write_text(original + "\n" + form + "\n", encoding="utf-8")
                self.assertFails("`callHook`")
        (self.root / IMPORT).write_text(original, encoding="utf-8")

    def test_lean_name_literal_fails(self) -> None:
        self.append(IMPORT, '\ndef a (n : Lean.Name) : Bool := n == `callHook\n')
        self.assertFails("Lean name literal `callHook")

    def test_attributed_or_local_shim_lowering_fails(self) -> None:
        for form in ['@[inline] def lowerMyShim : Nat := 0', 'noncomputable def lowerMyShim : Nat := 0',
                     'def b : Nat := c where lowerMyShim : Nat := 0']:
            with self.subTest(form=form):
                self.append(IMPORT, "\n" + form + "\n")
                self.assertFails("lowerMyShim defined outside the registry module")

    def test_code_after_a_theorem_is_checked(self) -> None:
        for form in ['mutual\n  def zzA (n : String) : Bool := n == "callHook"\nend',
                     'public def zzA (n : String) : Bool := n == "callHook"',
                     '  where zzA (n : String) : Bool := n == "callHook"',
                     'initialize zzR : IO.Ref String ← IO.mkRef "callHook"']:
            with self.subTest(form=form):
                self.append(IMPORT, "\ntheorem zzT : True := trivial\n" + form + "\n")
                self.assertFails("`callHook`")

    def test_indented_command_after_a_theorem_is_checked(self) -> None:
        self.append(IMPORT, '\ntheorem zzT : True := trivial\n'
                    '  def zzA (n : String) : Bool := n == "callHook"\n')
        self.assertFails("`callHook`")

    def test_selection_inside_a_theorem_is_checked(self) -> None:
        self.append(IMPORT, '\ntheorem zzT : ("callHook" == "x") = false := by decide\n')
        self.assertFails("`callHook`")

    def test_raw_strings_keep_the_scanner_in_step(self) -> None:
        self.append(IMPORT, '\nprivate def zzSlash : String := r"\\"\n'
                    'def zzA (n : String) : Bool := n == "callHook" || n == r"\\"\n')
        self.assertFails("`callHook`")

    def test_raw_string_name_fails(self) -> None:
        self.append(IMPORT, '\ndef zzA (n : String) : Bool := n == r#"callHook"#\n')
        self.assertFails("`callHook`")

    def test_importing_a_test_module_fails(self) -> None:
        (self.root / "Compiler/SolidityImport/ShortcutTest.lean").write_text(
            'def zzA (n : String) : Bool := n == "callHook"\n', encoding="utf-8")
        path = self.root / IMPORT
        path.write_text("import Compiler.SolidityImport.ShortcutTest\n"
                        + path.read_text(encoding="utf-8"), encoding="utf-8")
        self.assertFails("imports the test module Compiler.SolidityImport.ShortcutTest")

    def test_name_split_by_a_string_gap_fails(self) -> None:
        self.append(IMPORT, '\ndef zzName : String := "callHo\\\n  ok"\n'
                    'def zzA (n : String) : Bool := n == zzName\n')
        self.assertFails("`callHook`")

    def test_name_split_by_an_empty_interpolation_fails(self) -> None:
        self.append(IMPORT, '\ndef zzA (n : String) : Bool := n == s!"call{""}Hook"\n')
        self.assertFails("`callHook`")

    def test_where_helper_ending_a_theorem_line_is_checked(self) -> None:
        self.append(IMPORT, '\ntheorem zzT : True := trivial where\n'
                    '  zzName : String := "callHook"\n')
        self.assertFails("`callHook`")

    def test_nonrec_after_a_theorem_is_checked(self) -> None:
        self.append(IMPORT, '\ntheorem zzT : True := trivial\n'
                    '  nonrec def zzA (n : String) : Bool := n == "callHook"\n')
        self.assertFails("`callHook`")

    def test_meta_import_of_a_test_module_fails(self) -> None:
        (self.root / "Compiler/SolidityImport/ShortcutTest.lean").write_text(
            'def zzA (n : String) : Bool := n == "callHook"\n', encoding="utf-8")
        path = self.root / IMPORT
        path.write_text("meta import Compiler.SolidityImport.ShortcutTest\n"
                        + path.read_text(encoding="utf-8"), encoding="utf-8")
        self.assertFails("imports the test module Compiler.SolidityImport.ShortcutTest")

    def test_comparison_with_an_interpolated_string_fails(self) -> None:
        for form in ['def zzA (n f : String) : Bool := n == s!"TickBitmap.{f}"',
                     'def zzA (n lib : String) : Bool := n == s!"{lib}.flipTick"',
                     'def zzA (n lib : String) : Bool := n.startsWith s!"{lib}.flip"']:
            with self.subTest(form=form):
                self.append(IMPORT, "\n" + form + "\n")
                self.assertFails("which is not a solc AST")

    def test_operand_built_with_append_fails(self) -> None:
        for form in ['def zzA (n lib : String) : Bool := n == lib ++ ".flipTick"',
                     'def zzA (n lib : String) : Bool := n.endsWith (lib ++ ".flipTick")',
                     'def zzA (n lib : String) : Bool := n == lib ++ ".flipTick(int24,int24,int24)"',
                     'def zzA (n lib : String) : Bool := n == lib ++ s!".flipTick"',
                     'def zzA (n : String) : Bool := n.endsWith (".flipTick")']:
            with self.subTest(form=form):
                self.append(IMPORT, "\n" + form + "\n")
                self.assertFails("`flipTick`")

    def test_membership_with_elem_sign_fails(self) -> None:
        self.append(IMPORT, '\ndef zzA (n : String) : Bool := decide (n ∈ ["flipTick(int24)", "x y"])\n')
        self.assertFails("`flipTick`")

    def test_prefix_form_string_functions_fail(self) -> None:
        for form in ['def zzA (n : String) : Bool := String.startsWith n "TickBitmap."',
                     'def zzA (n : String) : Bool := String.isPrefixOf "TickBitmap." n']:
            with self.subTest(form=form):
                self.append(IMPORT, "\n" + form + "\n")
                self.assertFails("`TickBitmap`")

    def test_theorem_literals_are_exempt(self) -> None:
        self.append(IMPORT, '\ntheorem zzT : ("callHook" : String).length = 8 := by decide\n')
        self.assertEqual(lint.run(self.root), [])

    def test_escaped_name_fails(self) -> None:
        self.append(IMPORT, '\ndef zzA (n : String) : Bool := n == "call\\x48ook"\n')
        self.assertFails("`callHook`")

    def test_json_key_of_a_user_name_fails(self) -> None:
        self.append(IMPORT, '\ndef zzA (j : Json) : Bool := (field? j "callHook").isSome\n')
        self.assertFails("`callHook`")

    def test_resolved_name_literal_outside_registry_fails(self) -> None:
        self.append(IMPORT, '\ndef zzA (n : Lean.Name) : Bool := n == (``callHook)\n')
        self.assertFails("Lean name literal ``callHook")

    def test_unused_allowlist_entry_fails(self) -> None:
        lint.ALLOWED_IDENTIFIERS.add("zzUnusedName")
        try:
            self.assertFails("allowlist entry `zzUnusedName` is not needed")
        finally:
            lint.ALLOWED_IDENTIFIERS.discard("zzUnusedName")

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
