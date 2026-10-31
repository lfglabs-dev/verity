#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import property_utils


class PropertyUtilsContractNameTests(unittest.TestCase):
    def test_load_manifest_allows_contract_names_starting_with_underscore(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            manifest = Path(tmpdir) / "property_manifest.json"
            manifest.write_text('{"_Vault":["theorem_ok"]}\n', encoding="utf-8")

            original_manifest = property_utils.MANIFEST
            try:
                property_utils.MANIFEST = manifest
                loaded = property_utils.load_manifest()
            finally:
                property_utils.MANIFEST = original_manifest

            self.assertEqual(loaded, {"_Vault": {"theorem_ok"}})

    def test_collect_covered_allows_property_files_with_underscore_contract(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            test_dir = Path(tmpdir)
            (test_dir / "Property_Vault.t.sol").write_text(
                "// SPDX-License-Identifier: MIT\n"
                "/// Property 1: theorem_ok\n"
                "contract Property_Vault {}\n",
                encoding="utf-8",
            )

            original_test_dir = property_utils.TEST_DIR
            try:
                property_utils.TEST_DIR = test_dir
                covered = property_utils.collect_covered()
            finally:
                property_utils.TEST_DIR = original_test_dir

            self.assertEqual(covered, {"_Vault": {"theorem_ok"}})

    def test_extract_manifest_from_proofs_allows_underscore_contract_dirs(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            proofs_dir = root / "Proofs"
            examples_dir = root / "Examples"
            proofs_dir.mkdir()
            examples_dir.mkdir()

            contract_dir = proofs_dir / "_Vault"
            contract_dir.mkdir()
            proofs_subdir = contract_dir / "Proofs"
            proofs_subdir.mkdir()
            (proofs_subdir / "Basic.lean").write_text(
                "theorem theorem_ok : True := by\n"
                "  trivial\n",
                encoding="utf-8",
            )

            original_proofs_dir = property_utils.PROOFS_DIR
            original_examples_dir = property_utils.EXAMPLES_DIR
            try:
                property_utils.PROOFS_DIR = proofs_dir
                property_utils.EXAMPLES_DIR = examples_dir
                manifest = property_utils.extract_manifest_from_proofs()
            finally:
                property_utils.PROOFS_DIR = original_proofs_dir
                property_utils.EXAMPLES_DIR = original_examples_dir

            self.assertEqual(manifest, {"_Vault": ["theorem_ok"]})


class PropertyUtilsPropertyTagTests(unittest.TestCase):
    def test_extract_property_names_rejects_plain_line_comment_tag(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "PropertyCounter.t.sol"
            path.write_text(
                "pragma solidity ^0.8.13;\n"
                "contract PropertyCounter {\n"
                "    function test_note_only() public {\n"
                "        // Property: fake_from_line_comment\n"
                "    }\n"
                "}\n",
                encoding="utf-8",
            )

            names = property_utils.extract_property_names(path)
            self.assertEqual(names, [])

    def test_extract_property_names_accepts_structured_doc_tags(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "PropertyCounter.t.sol"
            path.write_text(
                "pragma solidity ^0.8.13;\n"
                "contract PropertyCounter {\n"
                "    /// Property 1: theorem_indexed\n"
                "    /// Property: theorem_simple\n"
                "    /**\n"
                "     * Property 2: theorem_block_doc\n"
                "     */\n"
                "}\n",
                encoding="utf-8",
            )

            names = property_utils.extract_property_names(path)
            self.assertEqual(names, ["theorem_indexed", "theorem_simple", "theorem_block_doc"])


class PropertyUtilsImportParsingTests(unittest.TestCase):
    def test_extract_lean_import_modules_supports_multiple_modules(self) -> None:
        modules = property_utils.extract_lean_import_modules(
            "import Verity.Bar Compiler.CompilationModel"
        )
        self.assertEqual(modules, ["Verity.Bar", "Compiler.CompilationModel"])

    def test_extract_lean_import_modules_ignores_aliases(self) -> None:
        modules = property_utils.extract_lean_import_modules(
            "import Compiler as C Contracts.Specs as Specs"
        )
        self.assertEqual(modules, ["Compiler", "Contracts.Specs"])

    def test_extract_lean_import_modules_ignores_non_import_lines(self) -> None:
        modules = property_utils.extract_lean_import_modules("theorem not_an_import : True := by")
        self.assertEqual(modules, [])

    def test_extract_lean_header_imports_ignores_strings_and_non_header_lines(self) -> None:
        text = (
            "prelude\n"
            "public import Verity.Core\n"
            "import all Compiler.A as CA\n"
            "\n"
            'def decoy : String := "\\nimport Contracts.Hidden\\n"\n'
            "def rawDecoy : String := r#\"\n"
            "import Contracts.RawHidden\n"
            "\"#\n"
        )
        self.assertEqual(
            property_utils.extract_lean_header_imports(text),
            ["Verity.Core", "Compiler.A"],
        )

    def test_extract_lean_header_imports_handles_module_multiline_continuations_and_quotes(
        self,
    ) -> None:
        text = (
            "module\n\n"
            "prelude\n"
            "public\n"
            "meta\n"
            "import\n"
            "all\n"
            "«Verity».«Core»\n"
            "import\n"
            "  «Compiler.Main»\n"
            "public section\n"
            "def x : Nat := 0\n"
        )
        self.assertEqual(
            property_utils.extract_lean_header_imports(text),
            ["Verity.Core", "Compiler.Main"],
        )

    def test_extract_lean_header_imports_fails_closed_on_incomplete_or_body_import(self) -> None:
        with self.assertRaises(ValueError):
            property_utils.extract_lean_header_imports("import\n")
        with self.assertRaises(ValueError):
            property_utils.extract_lean_header_imports("import Verity.Core\ndef x := 1\nimport Bad\n")


class PropertyUtilsTheoremExtractionTests(unittest.TestCase):
    def test_collect_theorems_ignores_block_and_line_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "Spec.lean"
            path.write_text(
                "/-\n"
                " theorem ghost_from_comment : True := by\n"
                "   trivial\n"
                "-/\n"
                "\n"
                "-- theorem ghost_from_line_comment : True := by\n"
                "theorem real_theorem : True := by\n"
                "  trivial\n",
                encoding="utf-8",
            )

            names = property_utils.collect_theorems(path)
            self.assertEqual(names, ["real_theorem"])

    def test_collect_theorems_accepts_declaration_prefixes(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "Spec.lean"
            path.write_text(
                "theorem plain_theorem : True := by\n"
                "  trivial\n"
                "\n"
                "@[simp] theorem simp_theorem : True := by\n"
                "  trivial\n"
                "\n"
                "private theorem private_theorem : True := by\n"
                "  trivial\n",
                encoding="utf-8",
            )

            names = property_utils.collect_theorems(path, include_helpers=True)
            self.assertEqual(names, ["plain_theorem", "simp_theorem", "private_theorem"])

    def test_collect_theorems_accepts_multiline_attribute_block(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "Spec.lean"
            path.write_text(
                "@[\n"
                "  simp,\n"
                "  reducible\n"
                "]\n"
                "theorem multi_attr_theorem : True := by\n"
                "  trivial\n",
                encoding="utf-8",
            )

            names = property_utils.collect_theorems(path, include_helpers=True)
            self.assertEqual(names, ["multi_attr_theorem"])

    def test_collect_theorems_excludes_helper_declarations_by_default(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "Spec.lean"
            path.write_text(
                "theorem plain_theorem : True := by\n"
                "  trivial\n"
                "@[simp] theorem simp_theorem : True := by\n"
                "  trivial\n"
                "private theorem private_theorem : True := by\n"
                "  trivial\n",
                encoding="utf-8",
            )

            names = property_utils.collect_theorems(path)
            self.assertEqual(names, ["plain_theorem"])

    def test_scrub_lean_code_handles_double_quote_char_literals_and_apostrophes(self) -> None:
        src = (
            "def q : Char := '\"'\n"
            "def escQuote : Char := '\\\"'\n"
            "def escSingle : Char := '\\''\n"
            "def hexChar : Char := '\\x22'\n"
            "def uniChar : Char := '\\u0022'\n"
            "def primed' : String := \"axiom fake_in_primed_str : False\"\n"
            "def pairQuote : Char := '\"' -- trailing comment after quote char\n"
            "axiom visible_after_quote_char : True\n"
            "def closePair : Char := '\"'\n"
        )
        stripped = property_utils.strip_lean_comments(src)
        scrubbed = property_utils.scrub_lean_code(src)
        self.assertEqual(len(stripped.splitlines()), len(src.splitlines()))
        self.assertEqual(len(scrubbed.splitlines()), len(src.splitlines()))
        self.assertNotIn("trailing comment", stripped)
        self.assertIn("axiom visible_after_quote_char : True", stripped)
        self.assertIn("axiom visible_after_quote_char : True", scrubbed)
        self.assertNotIn("fake_in_primed_str", scrubbed)

    def test_scrub_lean_code_matches_lean_ascii_id_rules_and_interpolated_strings(self) -> None:
        # `λ` (U+03BB), `Π` (U+03A0), `Σ` (U+03A3), `×` (U+00D7), and `÷` (U+00F7)
        # are excluded from Lean `isLetterLike`; `λ'"'` must tokenize as `λ` plus
        # char literal `'"'`, never as identifier `λ'` followed by an open string.
        src = (
            'macro "m_ign" term : command => `(command| def dummy := 0)\n'
            "m_ign (λ'\"' => 0)\n"
            "axiom visible_after_lambda_quote : False\n"
            'def s1 := s!"prefix {"inner\\"quote"} {1 /- " -/ + 2} suffix"\n'
            'def s2 := s!"escaped \\{\'\\\"\'}"\n'
            'def s3 : IO Unit := println! "msg {(1 /- " -/ + 2)}"\n'
            "axiom α_unicode_visible₁! : False\n"
            "-- \"\n"
            "theorem after_all : True := trivial\n"
        )
        scrubbed = property_utils.scrub_lean_code(src)
        self.assertEqual(len(scrubbed.splitlines()), len(src.splitlines()))
        self.assertIn("axiom visible_after_lambda_quote : False", scrubbed)
        self.assertIn("axiom α_unicode_visible₁! : False", scrubbed)
        self.assertIn("theorem after_all : True := trivial", scrubbed)
        self.assertNotIn("inner", scrubbed)

    def test_lean_id_predicates_exclude_lambda_pi_sigma_times_div_and_non_ascii_digits(self) -> None:
        for ch in ("λ", "Π", "Σ", "×", "÷", "²", "٠"):
            self.assertFalse(property_utils._is_lean_id_first(ch), ch)
            self.assertFalse(property_utils._is_lean_id_rest(ch), ch)
        for ch in ("α", "β", "Γ", "Ω", "𝔸"):
            self.assertTrue(property_utils._is_lean_id_first(ch), ch)
            self.assertTrue(property_utils._is_lean_id_rest(ch), ch)
        for ch in ("₀", "₉", "ₐ", "'", "!", "?"):
            self.assertFalse(property_utils._is_lean_id_first(ch), ch)
            self.assertTrue(property_utils._is_lean_id_rest(ch), ch)

    def test_scrub_lean_code_tracks_prime_suffix_builtins_and_custom_syntax_tokens(self) -> None:
        src = "\n".join(
            [
                'def pprodPair := (1, 2) ×\'"\'close_pprod"',
                "axiom ax_after_pprod : False",
                'def psumVal : Nat ⊕\' String := ⊕\'.inl 0',
                'def bracketGet (xs : Array String) (h : 0 < xs.size) := xs[0]\'"\'close_brk"',
                "axiom ax_after_bracket_prime : False",
                'infixl:65 " +\' " => HAdd.hAdd',
                'def customPrime := "a" +\'"\'close_custom_prime"',
                "axiom ax_after_custom_prime : False",
                'syntax term (" ?\' " term)? : term',
                'def parenOptAtom := 1 ?\'"\'close_paren_atom"',
                "axiom ax_after_paren_atom : False",
                'syntax ("myOpt! " interpolatedStr(term))? : term',
                'def optInterp := myOpt! "{ \'\\\"\' }"',
                "axiom ax_after_opt_interp : False",
                'syntax "myBrk[" ident "]" interpolatedStr(term) : term',
                'def brkInterp := myBrk[tag]"{ \'\\\"\' }"',
                "axiom ax_after_brk_interp : False",
                '@[term_parser] def lp := leading_parser " *\' " >> termParser',
                'def lpUse := *\'"\'close_lp"',
                "axiom ax_after_lp : False",
                'def charThenNonBuiltin : Char × String := (\'a\', "ok")',
                'def closeAll : String := "done"',
            ]
        ) + "\n"
        scrubbed = property_utils.scrub_lean_code(src)
        self.assertEqual(len(scrubbed.splitlines()), len(src.splitlines()))
        for expected in (
            "axiom ax_after_pprod : False",
            "axiom ax_after_bracket_prime : False",
            "axiom ax_after_custom_prime : False",
            "axiom ax_after_paren_atom : False",
            "axiom ax_after_opt_interp : False",
            "axiom ax_after_brk_interp : False",
            "axiom ax_after_lp : False",
        ):
            self.assertIn(expected, scrubbed)

    def test_scrub_lean_code_tracks_simp_like_tactic_multibracket_and_qualified_interp(self) -> None:
        src = "\n".join(
            [
                'declare_simp_like_tactic mySimpTac "§\\" "',
                'theorem t : True := by §" [eq_self]',
                "axiom ax_after_simp_quote : False",
                'syntax "qq[" ident "][" ident "]" interpolatedStr(term) : term',
                'def multiBrk := qq[a][b]"{ \'\\\"\' }"',
                "axiom ax_after_multi_brk : False",
                'syntax ident "qq=>" interpolatedStr(term) : term',
                'def trailingInterp := x qq=>"{ \'\\\"\' }"',
                "axiom ax_after_trailing_interp : False",
                'def plainArrow := fun _ => "{not_interp"',
                "axiom ax_after_plain_arrow : False",
                'def qualLog := do Lean.logInfo "{ \'\\\"\' }"',
                "axiom ax_after_qual_log : False",
                'def bangAtom := throwErrorAt !x "{ \'\\\"\' }"',
                "axiom ax_after_bang_atom : False",
            ]
        ) + "\n"
        scrubbed = property_utils.scrub_lean_code(src)
        self.assertEqual(len(scrubbed.splitlines()), len(src.splitlines()))
        for expected in (
            "axiom ax_after_simp_quote : False",
            "axiom ax_after_multi_brk : False",
            "axiom ax_after_trailing_interp : False",
            "axiom ax_after_plain_arrow : False",
            "axiom ax_after_qual_log : False",
            "axiom ax_after_bang_atom : False",
        ):
            self.assertIn(expected, scrubbed)

    def test_scrub_lean_code_tracks_numbers_slash_tokens_aesop_and_scoped_tokens(self) -> None:
        src = "\n".join(
            [
                'syntax:max " -open " term : term',
                'def uDiv := `(term| { x //-open "a" })',
                "axiom ax_div_slash : False",
                'syntax:max " #\\\"a\\\" " : term',
                'syntax:max term " ~r" term : term',
                'def uTildeR := `(term| 1 ~r#"a")',
                "axiom ax_tilde_r : False",
                'def uNum1 := `(term| 1a\'"\'open")',
                "axiom ax_num_1a : False",
                'def uNumHex := `(term| 0xfg\'"\'open")',
                "axiom ax_num_hex : False",
                'def uNumSci1 := `(term| 1.5e2a\'"\'open")',
                "axiom ax_num_sci1 : False",
                'def uNumSci2 := `(term| 1e-2a\'"\'open")',
                "axiom ax_num_sci2 : False",
                'def uAesop1 : IO Unit := do aesop_trace![steps] "hello {\'\\\"\'}"',
                "axiom ax_aesop_bang : False",
                'def uAesop2 : IO Unit := do aesop_trace[steps] "world {\'\\\"\'}"',
                "axiom ax_aesop_brk : False",
                'def uComp := `(term| f ∘\'"\'open")',
                "axiom ax_comp_prime : False",
                'def uPreim := `(term| f ⁻¹\'"\'open")',
                "axiom ax_preim_prime : False",
                'binder_predicate x " ≺\' " y:term => `(True)',
                'def uBp := `(term| ∃ x ≺\'"\'open", True)',
                "axiom ax_binder_pred : False",
                "def TLOAD : Nat := 6",
                "def TSTORE : Nat := 3",
                "def unscopedDiv : Nat := TLOAD/TSTORE",
                "def unscopedBlock : Nat := D/- real comment\naxiom ax_in_real_comment : False\n-/ + 1",
                "axiom ax_after_real_comment : False",
                "section ScopedProbe",
                "open scoped BitVec in",
                'def uBvCmd := `(term| 1#\'"\'open")',
                "def cAfterOpenIn : Char := '#' -- \"",
                "axiom ax_after_open_in : False",
                "def uBvTerm := open scoped BitVec in `(term| x#'\"'open\")",
                "def cAfterTermOpenIn : Char := '#' -- \"",
                "axiom ax_after_term_open_in : False",
                "open scoped FirstOrder",
                'def uFo := `(term| x =\'"\'open")',
                "axiom ax_fo_eq : False",
                "open scoped Dioph",
                'def uDioph := `(term| x D/-open "a")',
                "axiom ax_dioph_slash : False",
                "end ScopedProbe",
                "def afterSecBlock : Nat := D/- restored comment\naxiom ax_hidden_in_restored_comment : False\n-/ + 1",
                "axiom ax_after_section_restore : False",
            ]
        ) + "\n"
        scrubbed = property_utils.scrub_lean_code(src)
        self.assertEqual(len(scrubbed.splitlines()), len(src.splitlines()))
        for expected in (
            "axiom ax_div_slash : False",
            "axiom ax_tilde_r : False",
            "axiom ax_num_1a : False",
            "axiom ax_num_hex : False",
            "axiom ax_num_sci1 : False",
            "axiom ax_num_sci2 : False",
            "axiom ax_aesop_bang : False",
            "axiom ax_aesop_brk : False",
            "axiom ax_comp_prime : False",
            "axiom ax_preim_prime : False",
            "axiom ax_binder_pred : False",
            "axiom ax_after_real_comment : False",
            "axiom ax_after_open_in : False",
            "axiom ax_after_term_open_in : False",
            "axiom ax_fo_eq : False",
            "axiom ax_dioph_slash : False",
            "axiom ax_after_section_restore : False",
        ):
            self.assertIn(expected, scrubbed)
        self.assertNotIn("ax_in_real_comment", scrubbed)
        self.assertNotIn("ax_hidden_in_restored_comment", scrubbed)


if __name__ == "__main__":
    unittest.main()
