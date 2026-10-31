#!/usr/bin/env python3
from __future__ import annotations

import io
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_axioms


class CheckAxiomsLocationTests(unittest.TestCase):
    def test_parse_axiom_entries(self) -> None:
        text = (
            "### 1. `a1`\n\n"
            "**Location**: `Compiler/Foo.lean:12`\n\n"
            "### 2. `a2` (private)\n\n"
            "**Location**: `Verity/Bar.lean:34`\n"
        )
        self.assertEqual(
            check_axioms.parse_axiom_entries(text),
            [("a1", "Compiler/Foo.lean", 12), ("a2", "Verity/Bar.lean", 34)],
        )

    def test_parse_active_axiom_count(self) -> None:
        self.assertEqual(check_axioms.parse_active_axiom_count("- Active axioms: 2\n"), 2)
        self.assertIsNone(check_axioms.parse_active_axiom_count("no summary line"))

    def test_discover_repo_axioms_ignores_comments_and_strings(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Verity").mkdir(parents=True, exist_ok=True)
            (root / "Benchmark").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "A.lean").write_text(
                "\n".join(
                    [
                        "-- axiom commented_out : True",
                        "/- axiom in_block_comment : True -/",
                        'def s := "axiom in_string"',
                        "axiom real_axiom : True",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            (root / "Benchmark" / "Case.lean").write_text(
                "axiom benchmark_axiom : True\n",
                encoding="utf-8",
            )

            old_root = check_axioms.ROOT
            try:
                check_axioms.ROOT = root
                discovered = check_axioms.discover_repo_axioms()
            finally:
                check_axioms.ROOT = old_root

        self.assertEqual(
            discovered,
            {
                "real_axiom": ("Compiler/A.lean", 4),
                "benchmark_axiom": ("Benchmark/Case.lean", 1),
            },
        )

    def test_main_reports_missing_registry_entries_and_count_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Verity").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "A.lean").write_text(
                "axiom documented_axiom : True\naxiom missing_axiom : True\n",
                encoding="utf-8",
            )
            (root / "docs").mkdir(parents=True, exist_ok=True)
            (root / "docs" / "AXIOMS.md").write_text(
                "\n".join(
                    [
                        "### 1. `documented_axiom`",
                        "",
                        "**Location**: `Compiler/A.lean:1`",
                        "",
                        "## Trust Summary",
                        "",
                        "- Active axioms: 1",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )

            stderr = io.StringIO()
            old_root = check_axioms.ROOT
            try:
                check_axioms.ROOT = root
                with redirect_stderr(stderr), self.assertRaises(SystemExit):
                    check_axioms.main([])
            finally:
                check_axioms.ROOT = old_root

        err = stderr.getvalue()
        self.assertIn("missing_axiom: declared in Compiler/A.lean:2 but missing from AXIOMS.md", err)
        self.assertIn("AXIOMS.md trust summary says Active axioms: 1, but source has 2", err)


class CheckAxiomsReportTests(unittest.TestCase):
    def test_parse_axiom_output(self) -> None:
        text = (
            "'Foo.bar' depends on axioms: [propext, solidityMappingSlot_lt_evmModulus]\n"
            "'Baz.qux' does not depend on any axioms\n"
        )
        self.assertEqual(
            check_axioms.parse_axiom_output(text),
            {
                "Foo.bar": ["propext", "solidityMappingSlot_lt_evmModulus"],
                "Baz.qux": [],
            },
        )

    def test_classify_axioms_separates_forbidden_and_unexpected(self) -> None:
        axiom_map = {
            "Foo.bar": ["propext", "mysteryAx"],
            "Baz.qux": ["sorryAx"],
        }
        builtin, documented, forbidden, unexpected = check_axioms.classify_axioms(axiom_map)
        self.assertEqual(builtin, {"propext"})
        self.assertEqual(documented, set())
        self.assertEqual(forbidden, {"sorryAx"})
        self.assertEqual(unexpected, {"mysteryAx": ["Foo.bar"]})

    def test_classifies_lean424_native_codegen_axioms_as_builtin(self) -> None:
        axiom_map = {
            "Compiler.CompilationModel.compatScratch_startsWith_reserved": [
                "Lean.ofReduceBool",
                "Lean.trustCompiler",
            ],
        }

        builtin, documented, forbidden, unexpected = check_axioms.classify_axioms(axiom_map)
        report = check_axioms.generate_report(
            axiom_map, builtin, documented, forbidden, unexpected
        )

        self.assertEqual(builtin, {"Lean.ofReduceBool", "Lean.trustCompiler"})
        self.assertEqual(documented, set())
        self.assertEqual(forbidden, set())
        self.assertEqual(unexpected, {})
        self.assertIn("Lean.trustCompiler", report)
        self.assertIn("## Result: PASS", report)

    def test_classifies_lean431_per_proof_native_decide_axiom_as_builtin(self) -> None:
        generated = (
            "Compiler.SimpleStorageNativeWitness.lowerRuntimeContractNative_eq"
            "._native.native_decide.ax_1_1"
        )
        axiom_map = {"Compiler.Proofs.EndToEnd.simpleStorage_endToEnd": [generated]}

        builtin, documented, forbidden, unexpected = check_axioms.classify_axioms(axiom_map)
        report = check_axioms.generate_report(
            axiom_map, builtin, documented, forbidden, unexpected
        )

        self.assertEqual(builtin, {generated})
        self.assertEqual(documented, set())
        self.assertEqual(forbidden, set())
        self.assertEqual(unexpected, {})
        self.assertIn("generated per-proof native_decide axioms", report)
        self.assertIn("## Result: PASS", report)

    def test_similar_project_axiom_is_not_treated_as_native_decide_builtin(self) -> None:
        fake = "Project.native_decide.ax_1_1"
        _, _, _, unexpected = check_axioms.classify_axioms({"Foo.bar": [fake]})
        self.assertEqual(unexpected, {fake: ["Foo.bar"]})

    def test_dependency_cannot_spoof_native_decide_generated_name(self) -> None:
        fake = "Dependency.foo._native.native_decide.ax_1_1"
        _, _, _, unexpected = check_axioms.classify_axioms({"Foo.bar": [fake]})
        self.assertEqual(unexpected, {fake: ["Foo.bar"]})

    def test_classifies_lean431_per_proof_bv_decide_axiom_when_origin_allowed(self) -> None:
        origin = "Compiler.Proofs.MetaSpecs.hasMask_compl_eq_not_maskSubset"
        generated = f"{origin}._native.bv_decide.ax_1_7"
        old_bv = check_axioms.BV_DECIDE_AXIOM_ORIGINS
        try:
            check_axioms.BV_DECIDE_AXIOM_ORIGINS = frozenset([origin])
            builtin, documented, forbidden, unexpected = check_axioms.classify_axioms(
                {origin: [generated]}
            )
        finally:
            check_axioms.BV_DECIDE_AXIOM_ORIGINS = old_bv
        self.assertEqual(builtin, {generated})
        self.assertEqual(documented, set())
        self.assertEqual(forbidden, set())
        self.assertEqual(unexpected, {})

    def test_rejects_bv_decide_axiom_when_bv_allowlist_is_empty(self) -> None:
        generated = (
            "Compiler.Proofs.MetaSpecs.hasMask_compl_eq_not_maskSubset"
            "._native.bv_decide.ax_1_7"
        )
        _, _, _, unexpected = check_axioms.classify_axioms({"Foo.bar": [generated]})
        self.assertEqual(unexpected, {generated: ["Foo.bar"]})

    def test_dependency_cannot_spoof_bv_decide_generated_name(self) -> None:
        fake = "Dependency.foo._native.bv_decide.ax_1_7"
        _, _, _, unexpected = check_axioms.classify_axioms({"Foo.bar": [fake]})
        self.assertEqual(unexpected, {fake: ["Foo.bar"]})

    def test_same_origin_spoofed_native_decide_axiom_rejected_when_origin_does_not_use_it(
        self,
    ) -> None:
        origin = "Compiler.SimpleStorageNativeWitness.lowerRuntimeContractNative_eq"
        real_aux = f"{origin}._native.native_decide.ax_1_1"
        spoof_aux = f"{origin}._native.native_decide.ax_999"
        axiom_map = {
            origin: [real_aux],
            "Compiler.SpoofConsumer.bad": [spoof_aux],
        }
        builtin, _, _, unexpected = check_axioms.classify_axioms(axiom_map)
        self.assertEqual(builtin, {real_aux})
        self.assertEqual(unexpected, {spoof_aux: ["Compiler.SpoofConsumer.bad"]})

    def test_discover_repo_axioms_rejects_dotted_aux_spoof_declaration_names(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "Spoof.lean").write_text(
                "axiom thm._native.native_decide.ax_999 : False\n",
                encoding="utf-8",
            )
            stderr = io.StringIO()
            old_root = check_axioms.ROOT
            try:
                check_axioms.ROOT = root
                with redirect_stderr(stderr), self.assertRaises(SystemExit):
                    check_axioms.discover_repo_axioms()
            finally:
                check_axioms.ROOT = old_root
        self.assertIn("Forbidden hand-written native_decide/bv_decide auxiliary axiom", stderr.getvalue())

    def test_discover_repo_axioms_detects_indented_prefixed_quoted_and_split_axioms(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "Forms.lean").write_text(
                "\n".join(
                    [
                        "section Inner",
                        "  axiom indented_ax : True",
                        "  @[simp] noncomputable axiom attr_ax : True",
                        "  set_option linter.unusedVariables false in axiom opt_ax : True",
                        "  axiom «quoted.ax» : True",
                        "  axiom",
                        "    split_line_ax : True",
                        "  def keep («axiom» : Nat) : Nat := «axiom»",
                        "end Inner",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            old_root = check_axioms.ROOT
            try:
                check_axioms.ROOT = root
                discovered = check_axioms.discover_repo_axioms()
            finally:
                check_axioms.ROOT = old_root
        self.assertEqual(
            discovered,
            {
                "indented_ax": ("Compiler/Forms.lean", 2),
                "attr_ax": ("Compiler/Forms.lean", 3),
                "opt_ax": ("Compiler/Forms.lean", 4),
                "quoted.ax": ("Compiler/Forms.lean", 5),
                "split_line_ax": ("Compiler/Forms.lean", 6),
            },
        )

    def test_discover_repo_axioms_not_blinded_by_double_quote_char_literal(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "QuoteChar.lean").write_text(
                "\n".join(
                    [
                        "def openQuote : Char := '\"'",
                        "axiom hidden_between_quote_chars : False",
                        "def closeQuote : Char := '\"'",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            old_root = check_axioms.ROOT
            try:
                check_axioms.ROOT = root
                discovered = check_axioms.discover_repo_axioms()
            finally:
                check_axioms.ROOT = old_root
        self.assertEqual(
            discovered,
            {"hidden_between_quote_chars": ("Compiler/QuoteChar.lean", 2)},
        )

    def test_discover_repo_axioms_not_blinded_by_lambda_char_literal_or_interpolated_string(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "LambdaAndInterp.lean").write_text(
                "\n".join(
                    [
                        'macro "m_ign" term : command => `(command| def dummy := 0)',
                        "m_ign (λ'\"' => 0)",
                        "axiom after_lambda_char : False",
                        'def msg := s!"hole {1 /- " -/ + 2} and {\\"q\\\\\\"uote\\"}"',
                        "axiom α_unicode_ax₁ : False",
                        '-- "',
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            old_root = check_axioms.ROOT
            try:
                check_axioms.ROOT = root
                discovered = check_axioms.discover_repo_axioms()
            finally:
                check_axioms.ROOT = old_root
        self.assertEqual(
            discovered,
            {
                "after_lambda_char": ("Compiler/LambdaAndInterp.lean", 3),
                "α_unicode_ax₁": ("Compiler/LambdaAndInterp.lean", 5),
            },
        )

    def test_discover_repo_axioms_not_blinded_by_prime_suffix_tokens_or_custom_syntax(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "PrimeAndCustomSyntax.lean").write_text(
                "\n".join(
                    [
                        'def p := (1, 2) ×\'"\'open_first"',
                        "axiom ax_pprod : False",
                        'syntax term (" +\' " term)? : term',
                        'def q := 1 +\'"\'open_second"',
                        "axiom ax_paren_atom : False",
                        'syntax "myMany " ident* interpolatedStr(term) : term',
                        'def r := myMany a b "{ \'\\\"\' }"',
                        "axiom ax_many_interp : False",
                        '@[term_parser] def myLP := leading_parser "myLP! " >> interpolatedStr termParser',
                        'def s := myLP! "{ \'\\\"\' }"',
                        "axiom ax_lp_interp : False",
                        'def closeQuotes := "done"',
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            old_root = check_axioms.ROOT
            try:
                check_axioms.ROOT = root
                discovered = check_axioms.discover_repo_axioms()
            finally:
                check_axioms.ROOT = old_root
        self.assertEqual(
            discovered,
            {
                "ax_pprod": ("Compiler/PrimeAndCustomSyntax.lean", 2),
                "ax_paren_atom": ("Compiler/PrimeAndCustomSyntax.lean", 5),
                "ax_many_interp": ("Compiler/PrimeAndCustomSyntax.lean", 8),
                "ax_lp_interp": ("Compiler/PrimeAndCustomSyntax.lean", 11),
            },
        )

    def test_run_report_check_passes_and_writes_output_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            output = Path(tmpdir) / "axiom-report.md"
            old_output = os.environ.get("AXIOM_REPORT_FILE")
            os.environ["AXIOM_REPORT_FILE"] = str(output)
            stdout = io.StringIO()
            stderr = io.StringIO()
            try:
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = check_axioms.run_report_check(
                        "'Foo.bar' depends on axioms: [propext]\n"
                    )
            finally:
                if old_output is None:
                    os.environ.pop("AXIOM_REPORT_FILE", None)
                else:
                    os.environ["AXIOM_REPORT_FILE"] = old_output

            self.assertEqual(rc, 0)
            self.assertIn("## Result: PASS", stdout.getvalue())
            self.assertIn("Report written to", stderr.getvalue())
            self.assertTrue(output.exists())

    def test_run_report_check_fails_on_unexpected_axioms(self) -> None:
        stdout = io.StringIO()
        with redirect_stdout(stdout):
            rc = check_axioms.run_report_check("'Foo.bar' depends on axioms: [mysteryAx]\n")
        self.assertEqual(rc, 1)
        self.assertIn("## Result: FAIL", stdout.getvalue())
        self.assertIn("mysteryAx", stdout.getvalue())

    def test_main_report_mode_reads_log(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            log = Path(tmpdir) / "axioms.log"
            log.write_text("'Foo.bar' does not depend on any axioms\n", encoding="utf-8")
            stdout = io.StringIO()
            with redirect_stdout(stdout):
                rc = check_axioms.main(["--log", str(log)])
        self.assertEqual(rc, 0)
        self.assertIn("Total theorems checked: 1", stdout.getvalue())

    def test_scan_lean_file_axioms_fails_closed_on_bypass_constructs(self) -> None:
        forbidden_samples = [
            ('macro "sneak" : command => `(command| axiom hid : False)\n', "Nested or quoted axiom"),
            ('macro "sneakStx" : command => `(command| syntax "z" : term)\n', "Forbidden quoted syntax"),
            ('def q := `(stx| "bad")\n', "Forbidden syntax-category quotation"),
            ("#eval Lean.addDecl (.axiomDecl { name := `bad, levelParams := [], type := .sort .zero, isUnsafe := false })\n", "addDecl"),
            ("def p := Lean.ParserDescr.node `k 0 (.symbol \"x\")\n", "ParserDescr"),
            ("def s := stx.setKind ``Lean.Parser.Command.axiom\n", "Command.axiom"),
            ("def s2 := stx.setKind k\n", "setKind"),
            ("def n := Lean.Syntax.node .none k #[]\n", "Syntax.node"),
            ("def n2 : Lean.Syntax := .node .none k #[]\n", ".node"),
            ("def sym := Lean.Parser.symbol myStr\n", "Non-literal parser symbol"),
            ('def g := Lean. «addDecl»\n', "addDecl"),
        ]
        for sample, needle in forbidden_samples:
            stderr = io.StringIO()
            with redirect_stderr(stderr):
                with self.assertRaises(SystemExit, msg=f"Sample did not fail closed: {sample!r}"):
                    check_axioms.scan_lean_file_axioms(sample, "Compiler/Bypass.lean")
            self.assertIn(needle, stderr.getvalue())

    def test_scan_lean_file_axioms_ignores_guillemet_identifier_and_backtick_name_lit(self) -> None:
        src = "\n".join(
            [
                "def «axiom» : Nat := 0",
                "def k := (`axiom, ``Lean.Parser.Term.app)",
                "def m (x : Lean.Syntax) : Nat := match x with",
                "  | .node _ _ _ => 1",
                "  | _ => 0",
            ]
        ) + "\n"
        self.assertEqual(check_axioms.scan_lean_file_axioms(src, "Compiler/Benign.lean"), [])


if __name__ == "__main__":
    unittest.main()
