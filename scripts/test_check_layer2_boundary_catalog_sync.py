from __future__ import annotations

import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import docsync


class Layer2BoundaryCatalogSyncTests(unittest.TestCase):
    def _write_fixture_tree(self, root: Path, *, good_docs: bool) -> None:
        artifact = root / "artifacts" / "layer2_boundary_catalog.json"
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.write_text(
            json.dumps(
                {
                    "current_theorem": {
                        "helper_ir_goal_ready_variant": (
                            "Compiler.Proofs.IRGeneration.Contract."
                            "compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal"
                        ),
                        "helper_ir_closed_variant": (
                            "Compiler.Proofs.IRGeneration.Contract."
                            "compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed"
                        ),
                    },
                    "theorem_target": {
                        "intended_claim": "proof_complete_macro_lowered_verity_contract_image",
                        "excludes_arbitrary_lean_compilation_models": True,
                    },
                    "supported_spec_split": {
                        "helper_boundary": {
                            "current_fail_closed_gate": "SupportedBodyInterface.stmtList",
                            "blocking_seams": [
                                {"name": "legacy_stmt_fragment_witness"}
                            ],
                            "compiled_target_compatibility_subset": {
                                "goal_surface": (
                                    "Compiler.Proofs.IRGeneration.IRInterpreter."
                                    "InterpretIRWithInternalsZeroConservativeExtensionGoal"
                                ),
                                "dispatch_goal_surface": (
                                    "Compiler.Proofs.IRGeneration.IRInterpreter."
                                    "InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal"
                                ),
                                "goal_composition_surface": (
                                    "Compiler.Proofs.IRGeneration.IRInterpreter."
                                    "interpretIRWithInternalsZeroConservativeExtensionGoal_of_dispatchGoal"
                                ),
                                "goal_decomposition_surface": (
                                    "Compiler.Proofs.IRGeneration.IRInterpreter."
                                    "InterpretIRWithInternalsZeroConservativeExtensionInterfaces"
                                ),
                                "interface_builder_surface": (
                                    "Compiler.Proofs.IRGeneration.IRInterpreter."
                                    "interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtCompatibility"
                                ),
                                "stmt_subgoal_surface": (
                                    "Compiler.Proofs.IRGeneration.IRInterpreter."
                                    "InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals"
                                ),
                                "stmt_subgoal_closed_surface": (
                                    "Compiler.Proofs.IRGeneration.IRInterpreter."
                                    "interpretIRWithInternalsZeroConservativeExtensionStmtSubgoals_closed"
                                ),
                                "expr_stmt_dedicated_builtin_classifier": (
                                    "Compiler.Proofs.IRGeneration.IRInterpreter."
                                    "exprStmtUsesDedicatedBuiltinSemantics"
                                ),
                            },
                            "compiled_target_proof_surface": {
                                "source": (
                                    "Compiler.Proofs.IRGeneration.IRInterpreter."
                                    "evalIRExprWithInternals"
                                ),
                            },
                            "source_helper_goal_surface": {
                                "direct_body_goal": (
                                    "Compiler.Proofs.IRGeneration.GenericInduction."
                                    "SupportedFunctionBodyWithHelpersIRPreservationGoal"
                                ),
                                "direct_body_goal_helper_ir": (
                                    "Compiler.Proofs.IRGeneration.GenericInduction."
                                    "SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal"
                                ),
                            },
                        }
                    },
                }
            ),
            encoding="utf-8",
        )

        catalog = json.loads(artifact.read_text(encoding="utf-8"))
        expected = docsync.get_entry("layer2_boundary_catalog").expected_snippets(catalog)
        docs = {
            label: "\n".join(snippets) + "\n" for label, snippets in expected.items()
        }
        if not good_docs:
            docs["ROADMAP"] = "stale roadmap\n"

        for label, rel in {
            "ROADMAP": Path("docs/ROADMAP.md"),
            "VERIFICATION_STATUS": Path("docs/VERIFICATION_STATUS.md"),
            "COMPILER_PROOFS_README": Path("Compiler/Proofs/README.md"),
        }.items():
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(docs[label], encoding="utf-8")

    def _run_check(self, *, good_docs: bool) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture_tree(root, good_docs=good_docs)

            stdout = io.StringIO()
            stderr = io.StringIO()
            with redirect_stdout(stdout), redirect_stderr(stderr):
                rc = docsync.run_entry("layer2_boundary_catalog", root=root)
            return rc, stdout.getvalue() + stderr.getvalue()

    def test_matching_docs_pass(self) -> None:
        rc, output = self._run_check(good_docs=True)
        self.assertEqual(rc, 0, output)
        self.assertIn("layer2 boundary catalog sync passed", output)

    def test_missing_doc_phrase_fails(self) -> None:
        rc, output = self._run_check(good_docs=False)
        self.assertEqual(rc, 1)
        self.assertIn("docs/ROADMAP.md is out of sync", output)

    def test_repository_docs_are_currently_in_sync(self) -> None:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            rc = docsync.run_entry("layer2_boundary_catalog")
        output = stdout.getvalue() + stderr.getvalue()
        self.assertEqual(rc, 0, output)


if __name__ == "__main__":
    unittest.main()
