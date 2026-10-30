#!/usr/bin/env python3
"""Tests for scripts/check_union_coverage.py and scripts/generate_print_axioms.py."""

from __future__ import annotations

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_union_coverage
import generate_print_axioms


class UnionCoverageTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "Verity").mkdir()
        (self.root / "Compiler").mkdir()
        (self.root / "Contracts").mkdir()
        (self.root / "scripts").mkdir()

        self.write("Verity.lean", "import Verity.Core\n")
        self.write("Verity/Core.lean", "import Init\n")
        self.write("Compiler/A.lean", "import Verity.Core\n")
        self.write("Compiler/Main.lean", "import Compiler.A\n")
        self.write("Contracts/Token.lean", "import Verity.Core\n")
        self.write("Contracts/TokenSmoke.lean", "import Contracts.Token\n")
        self.write(
            "scripts/VerityUnionAxioms.lean",
            "import AxiomAudit\nimport Verity\nimport Compiler.A\nimport Contracts.Token\n",
        )

    def write(self, rel: str, text: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def test_current_repo_tree_is_covered(self) -> None:
        _, verified, _, roots = check_union_coverage.discover_population(
            check_union_coverage.ROOT
        )
        self.assertGreaterEqual(len(verified), 490)
        self.assertGreater(len(roots), 0)
        for required in (
            "Compiler.SolidityImport.Import",
            "Compiler.Proofs.IRGeneration.Expr",
            "Contracts.LocalObligationTrustSurface",
            "Contracts.RawLogTrustSurface",
            "Verity.Proofs.CheckedExternalCallConsumer",
            "Verity.Proofs.Model.CommonExternalCallEquivalence",
            "Verity.Proofs.Model.GeneratedEntrypointRegistry",
        ):
            self.assertIn(required, verified)
        self.assertEqual(
            check_union_coverage.check_union_coverage(check_union_coverage.ROOT),
            len(verified),
        )

    def test_synthetic_transitive_coverage(self) -> None:
        self.assertEqual(check_union_coverage.check_union_coverage(self.root), 4)

    def test_dropped_root_import_fails(self) -> None:
        self.write(
            "scripts/VerityUnionAxioms.lean",
            "import AxiomAudit\nimport Verity\nimport Compiler.A\n",
        )
        with self.assertRaisesRegex(
            ValueError, r"outside VerityUnionAxioms\.lean.*Contracts\.Token"
        ):
            check_union_coverage.check_union_coverage(self.root)

    def test_commented_import_does_not_cover(self) -> None:
        self.write(
            "scripts/VerityUnionAxioms.lean",
            "import Verity\nimport Compiler.A\n/- nested /- comment -/\nimport Contracts.Token\n-/\n",
        )
        with self.assertRaisesRegex(
            ValueError, r"outside VerityUnionAxioms\.lean.*Contracts\.Token"
        ):
            check_union_coverage.check_union_coverage(self.root)

    def test_non_verified_import_in_union_fails(self) -> None:
        self.write(
            "scripts/VerityUnionAxioms.lean",
            "import Verity\nimport Compiler.A\nimport Compiler.Main\nimport Contracts.Token\n",
        )
        with self.assertRaisesRegex(
            ValueError, r"VerityUnionAxioms\.lean imports non-verified local module: Compiler\.Main"
        ):
            check_union_coverage.check_union_coverage(self.root)

    def test_verified_importing_non_verified_leaks_and_fails(self) -> None:
        self.write("Compiler/A.lean", "import Verity.Core\nimport Compiler.Main\n")
        with self.assertRaisesRegex(
            ValueError,
            r"verified modules import non-verified local modules: Compiler\.A -> Compiler\.Main",
        ):
            check_union_coverage.check_union_coverage(self.root)

    def test_multiline_and_quoted_excluded_import_leaks_and_fails(self) -> None:
        self.write(
            "Compiler/A.lean",
            "module\n\nimport Verity.Core\npublic\nimport\n  «Compiler».«Main»\npublic section\n",
        )
        with self.assertRaisesRegex(
            ValueError,
            r"verified modules import non-verified local modules: Compiler\.A -> Compiler\.Main",
        ):
            check_union_coverage.check_union_coverage(self.root)

    def test_new_verified_module_is_detected(self) -> None:
        self.write("Contracts/Vault.lean", "import Verity.Core\n")
        with self.assertRaisesRegex(
            ValueError, r"outside VerityUnionAxioms\.lean.*Contracts\.Vault"
        ):
            check_union_coverage.check_union_coverage(self.root)

    def test_print_axioms_coverage_is_checked_when_present(self) -> None:
        self.write("PrintAxioms.lean", "import AxiomAudit\nimport Verity\n")
        with self.assertRaisesRegex(
            ValueError, r"outside PrintAxioms\.lean.*Compiler\.A"
        ):
            check_union_coverage.check_union_coverage(self.root)

    def test_string_literal_import_decoy_cannot_hide_verified_root(self) -> None:
        self.write("Verity/B.lean", "import Verity.Core\n")
        self.write(
            "Verity/A.lean",
            'import Verity.Core\ndef decoy : String := "\\nimport Verity.B\\n"\n',
        )
        _, _, _, roots = check_union_coverage.discover_population(self.root)
        self.assertIn("Verity.A", roots)
        self.assertIn("Verity.B", roots)
        self.write(
            "scripts/VerityUnionAxioms.lean",
            "import AxiomAudit\nimport Verity\nimport Verity.A\nimport Compiler.A\nimport Contracts.Token\n",
        )
        with self.assertRaisesRegex(
            ValueError, r"outside VerityUnionAxioms\.lean.*Verity\.B"
        ):
            check_union_coverage.check_union_coverage(self.root)

    def test_string_literal_import_decoy_in_union_file_does_not_cover(self) -> None:
        self.write(
            "scripts/VerityUnionAxioms.lean",
            'import AxiomAudit\nimport Verity\nimport Compiler.A\ndef decoy : String := "\\nimport Contracts.Token\\n"\n',
        )
        with self.assertRaisesRegex(
            ValueError, r"outside VerityUnionAxioms\.lean.*Contracts\.Token"
        ):
            check_union_coverage.check_union_coverage(self.root)


class GeneratePrintAxiomsTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "Verity").mkdir()
        (self.root / "Compiler").mkdir()
        (self.root / "Contracts").mkdir()
        (self.root / "scripts").mkdir()

    def write(self, rel: str, text: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def test_extract_theorems_handles_indented_mutual_private_sorry_and_skips_dollar(
        self,
    ) -> None:
        sample = self.root / "Verity" / "Sample.lean"
        sample.write_text(
            "\n".join(
                [
                    "namespace Verity.Sample",
                    "theorem top_ok : True := trivial",
                    "private lemma hidden_helper : True := trivial",
                    "section Inner",
                    "  theorem",
                    "      split_header_ok : True := trivial",
                    "  @[simp] private theorem",
                    "      split_private_ok : True := trivial",
                    "end Inner",
                    "verity_contract Demo where",
                    "  interfaces",
                    "    interface IToken where",
                    "      function balanceOf(Address) view returns (Uint256)",
                    "    end",
                    "theorem after_interface_end : True := trivial",
                    'def strDecoy : String := "\\ntheorem fake_in_string : False := sorry\\n"',
                    "mutual",
                    "  @[simp] theorem mut_a : True := trivial",
                    "  lemma mut_b : True := by",
                    "    sorry",
                    "end",
                    "theorem $macro_placeholder : True := trivial",
                    "/- theorem commented_out : True := trivial -/",
                    "end Sample",
                    "end Verity",
                ]
            )
            + "\n",
            encoding="utf-8",
        )
        extracted = generate_print_axioms.extract_theorems(sample)
        self.assertEqual(
            extracted,
            [
                ("Verity.Sample.top_ok", False, False),
                ("Verity.Sample.hidden_helper", True, False),
                ("Verity.Sample.split_header_ok", False, False),
                ("Verity.Sample.split_private_ok", True, False),
                ("Verity.Sample.after_interface_end", False, False),
                ("Verity.Sample.mut_a", False, False),
                ("Verity.Sample.mut_b", False, True),
            ],
        )

    def test_extract_theorems_not_blinded_by_double_quote_char_literal(self) -> None:
        sample = self.root / "Verity" / "QuoteChar.lean"
        sample.write_text(
            "\n".join(
                [
                    "namespace Verity.QuoteChar",
                    "def c1 : Char := '\"'",
                    "theorem after_quote_char : True := trivial",
                    "def c2 : Char := '\"'",
                    "end QuoteChar",
                    "end Verity",
                ]
            )
            + "\n",
            encoding="utf-8",
        )
        self.assertEqual(
            generate_print_axioms.extract_theorems(sample),
            [("Verity.QuoteChar.after_quote_char", False, False)],
        )

    def test_generate_and_check_roundtrip_on_synthetic_tree(self) -> None:
        self.write(
            "Verity/Core.lean",
            "namespace Verity\ntheorem core_ok : True := trivial\nend Verity\n",
        )
        self.write(
            "Compiler/Pass.lean",
            "import Verity.Core\nnamespace Compiler\nlemma pass_ok : True := trivial\nend Compiler\n",
        )
        self.write(
            "Compiler/Main.lean",
            "import Compiler.Pass\ndef main : IO Unit := pure ()\n",
        )

        print_content = generate_print_axioms.generate(self.root)
        union_content = generate_print_axioms.generate_union_axioms(self.root)

        self.assertIn("import AxiomAudit", print_content)
        self.assertIn("import Compiler.Pass", print_content)
        self.assertNotIn("import Compiler.Main", print_content)
        non_comment = "\n".join(
            ln
            for ln in print_content.splitlines()
            if not ln.lstrip().startswith("--")
        )
        self.assertNotIn("collectAxioms", non_comment)
        self.assertNotIn("collectMemo", non_comment)
        self.assertIn("unionCheckM env (unionLabel pfxs) roots modules allowed", print_content)
        self.assertIn("Verity.core_ok", print_content)
        self.assertIn("Compiler.pass_ok", print_content)
        self.assertIn("reportPrintAxiomsForRootsM", print_content)

        (self.root / "PrintAxioms.lean").write_text(print_content, encoding="utf-8")
        (self.root / "scripts" / "VerityUnionAxioms.lean").write_text(
            union_content, encoding="utf-8"
        )
        self.assertEqual(check_union_coverage.check_union_coverage(self.root), 2)

        old_root = generate_print_axioms.ROOT
        old_out = generate_print_axioms.OUTPUT
        old_union = generate_print_axioms.UNION_OUTPUT
        try:
            generate_print_axioms.ROOT = self.root
            generate_print_axioms.OUTPUT = self.root / "PrintAxioms.lean"
            generate_print_axioms.UNION_OUTPUT = (
                self.root / "scripts" / "VerityUnionAxioms.lean"
            )
            out = io.StringIO()
            with redirect_stdout(out):
                rc = generate_print_axioms.main(["--check"])
            self.assertEqual(rc, 0)

            (self.root / "scripts" / "VerityUnionAxioms.lean").unlink()
            err = io.StringIO()
            with redirect_stdout(out), redirect_stderr(err):
                rc_missing = generate_print_axioms.main(["--check"])
            self.assertEqual(rc_missing, 1)
        finally:
            generate_print_axioms.ROOT = old_root
            generate_print_axioms.OUTPUT = old_out
            generate_print_axioms.UNION_OUTPUT = old_union


if __name__ == "__main__":
    unittest.main()
