#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_theorem_citations as guard

PROOFS = """
namespace Pkg.Proofs

/-- docstring mentioning theorem fake_in_comment -/
theorem real_sound : True := trivial

@[simp] private theorem attr_sound : True := trivial

def obligation_preserves : Prop := True

section Inner
lemma inner_lemma : True := trivial
end Inner

mutual
def evenish : Nat → Bool
  | _ => true
end

theorem after_mutual_sound : True := trivial

end Pkg.Proofs

theorem _root_.Top.rooted_sound : True := trivial
"""

MACRO = """
def reserved : Array String := #["entrypointRegistry_cases", "entrypointRegistry_preserves"]
"""


class TheoremCitationTests(unittest.TestCase):
    def _repo(self, files: dict[str, str]) -> Path:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        base = {"Pkg/Proofs.lean": PROOFS, "Verity/Macro/Translate.lean": MACRO}
        base.update(files)
        for rel, text in base.items():
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(textwrap.dedent(text), encoding="utf-8")
        guard._lean_sources.cache_clear()
        return root

    def _errors(self, files: dict[str, str]) -> list[str]:
        return guard.check(self._repo(files))

    # ---- declaration index -------------------------------------------------

    def test_index_is_namespace_and_scope_aware(self) -> None:
        decls = guard.collect_declarations(self._repo({}))
        for name in ("real_sound", "attr_sound", "inner_lemma", "after_mutual_sound"):
            self.assertEqual(decls[f"Pkg.Proofs.{name}"].kind, "theorem" if name != "inner_lemma" else "lemma")
        self.assertEqual(decls["Pkg.Proofs.obligation_preserves"].kind, "def")
        self.assertEqual(decls["Top.rooted_sound"].kind, "theorem")
        self.assertNotIn("Pkg.Proofs.fake_in_comment", decls)

    # ---- Lean catalog sites ------------------------------------------------

    def test_catalog_accepts_existing_theorems(self) -> None:
        errors = self._errors({"Pkg/Catalog.lean": """
            def entry := { theoremRef := "Pkg.Proofs.real_sound" }
            def burn := { refutationTheorem := "Pkg.Proofs.inner_lemma" }
            def rule := { proofId := proofRefName "Top.rooted_sound" }
            def verifiedAccelTheoremAllowlist : List String :=
              [ "Pkg.Proofs.attr_sound"
              , "Pkg.Proofs.after_mutual_sound" ]
            """})
        self.assertEqual(errors, [])

    def test_catalog_rejects_missing_theorem_ref(self) -> None:
        errors = self._errors({"Pkg/Catalog.lean": 'def e := { theoremRef := "Pkg.Proofs.missing_sound" }\n'})
        self.assertEqual(len(errors), 1)
        self.assertIn("Pkg/Catalog.lean:1 (theoremRef)", errors[0])
        self.assertIn("not a declaration", errors[0])

    def test_catalog_rejects_def_cited_as_proof(self) -> None:
        errors = self._errors({"Pkg/Catalog.lean":
            'def r := { proofId := proofRefName "Pkg.Proofs.obligation_preserves" }\n'})
        self.assertEqual(len(errors), 1)
        self.assertIn("is a def", errors[0])

    def test_catalog_requires_full_name(self) -> None:
        errors = self._errors({"Pkg/Catalog.lean": 'def e := { theoremRef := "real_sound" }\n'})
        self.assertEqual(len(errors), 1)
        self.assertIn("exists as `Pkg.Proofs.real_sound`", errors[0])

    def test_allowlist_entries_are_checked(self) -> None:
        errors = self._errors({"Pkg/Catalog.lean": """
            def fooTheoremAllowlist : List String :=
              [ "Pkg.Proofs.real_sound"
              , "Pkg.Proofs.bundle_sound" ]
            """})
        self.assertEqual(len(errors), 1)
        self.assertIn("(theorem allowlist)", errors[0])
        self.assertIn("bundle_sound", errors[0])

    def test_commented_out_catalog_entries_and_test_modules_are_ignored(self) -> None:
        errors = self._errors({
            "Pkg/Catalog.lean": '-- def e := { theoremRef := "Pkg.Proofs.missing_sound" }\n',
            "Pkg/CatalogTest.lean": 'def e := { theoremRef := "Pkg.Proofs.missing_sound" }\n',
        })
        self.assertEqual(errors, [])

    # ---- documentation sites -----------------------------------------------

    def test_doc_accepts_suffix_names_of_theorems(self) -> None:
        errors = self._errors({"docs/A.md":
            "The kernel proves `real_sound`, and the lemma `Proofs.inner_lemma` holds.\n"})
        self.assertEqual(errors, [])

    def test_doc_rejects_missing_theorem_in_list(self) -> None:
        errors = self._errors({"docs/A.md":
            "This file proves `real_sound` and `no_such_thing`, see `other_name`.\n"})
        self.assertEqual(len(errors), 1)
        self.assertIn("docs/A.md:1", errors[0])
        self.assertIn("no_such_thing", errors[0])

    def test_doc_rejects_trailing_theorem_word_and_def(self) -> None:
        errors = self._errors({"site/B.mdx": "Use the `obligation_preserves` theorem here.\n"})
        self.assertEqual(len(errors), 1)
        self.assertIn("is a def", errors[0])

    def test_doc_ignores_non_theorem_shaped_and_untriggered_names(self) -> None:
        errors = self._errors({"docs/A.md": (
            "The theorem `SomeType` is a type; see `missing_but_untriggered`.\n"
            "Run `verity_contract` with `--deny-unsafe`.\n")})
        self.assertEqual(errors, [])

    def test_doc_artifacts_directory_is_excluded(self) -> None:
        errors = self._errors({"artifacts/review.md": "It proves `historical_claim_sound`.\n"})
        self.assertEqual(errors, [])

    def test_doc_macro_generated_theorem_needs_a_verity_contract(self) -> None:
        contract = "verity_contract Vault where\n  storage\n"
        ok = self._errors({
            "Contracts/Vault.lean": contract,
            "docs/A.md": "the generated `Vault.entrypointRegistry_preserves` theorem\n",
        })
        self.assertEqual(ok, [])
        bad = self._errors({
            "Contracts/Vault.lean": contract,
            "docs/A.md": "the generated `Bank.entrypointRegistry_preserves` theorem\n",
        })
        self.assertEqual(len(bad), 1)

    def test_macro_generated_list_must_match_macro_source(self) -> None:
        errors = self._errors({"Verity/Macro/Translate.lean": "def reserved : Array String := #[]\n"})
        self.assertEqual(len(errors), 2)
        self.assertTrue(all("MACRO_GENERATED_THEOREMS" in e for e in errors))

    # ---- repository regression ---------------------------------------------

    def test_spill_pass_citation_class_is_caught(self) -> None:
        """The G1 defect fixed by #2906: a catalog entry citing a theorem that never existed."""
        errors = self._errors({"Pkg/Catalog.lean": """
            def g1 := { assurance := .kernelVerified
                        theoremRef := "Pkg.Proofs.reuseBlockTemps_sound" }
            """})
        self.assertEqual(len(errors), 1)
        self.assertIn("reuseBlockTemps_sound", errors[0])


if __name__ == "__main__":
    unittest.main()
