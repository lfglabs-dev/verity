#!/usr/bin/env python3
from __future__ import annotations

import contextlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import property_utils
import verification_metrics


class VerificationMetricsTests(unittest.TestCase):
    def test_get_axiom_and_sorry_counts_ignore_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Verity").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "Commented.lean").write_text(
                "\n".join(
                    [
                        "-- axiom fakeAxiom",
                        "/-",
                        "axiom fakeInBlock",
                        "sorry",
                        "-/",
                        'def quoted := "axiom fakeInString"',
                        'def quoted2 := "sorry"',
                        "axiom realAxiom : True",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            (root / "Verity" / "Proof.lean").write_text(
                "\n".join(
                    [
                        "-- sorry",
                        "theorem realSorry : True := by",
                        "  sorry",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            old_root = verification_metrics.ROOT
            try:
                verification_metrics.ROOT = root
                self.assertEqual(verification_metrics.get_axiom_count(), 1)
                total_sorry, proof_sorry = verification_metrics.get_sorry_count()
                self.assertEqual(total_sorry, 1)
                self.assertEqual(proof_sorry, 1)
            finally:
                verification_metrics.ROOT = old_root

    def test_get_manifest_counts_rejects_duplicate_json_keys(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            manifest = Path(tmpdir) / "property_manifest.json"
            manifest.write_text(
                '{\n  "Counter": ["ok"],\n  "Counter": ["dup"]\n}\n',
                encoding="utf-8",
            )
            old_manifest = property_utils.MANIFEST
            try:
                property_utils.MANIFEST = manifest
                with self.assertRaises(SystemExit) as ctx:
                    verification_metrics.get_manifest_counts()
                self.assertIn("duplicate object key", str(ctx.exception))
            finally:
                property_utils.MANIFEST = old_manifest

    def test_infrastructure_sorrys_excluded_from_proof_sorry(self) -> None:
        """Sorrys in INFRASTRUCTURE_FILES count toward total but not proof_sorry."""
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            # Create the infrastructure file with sorrys
            infra = (
                root
                / "Compiler"
                / "Proofs"
                / "YulGeneration"
                / "Backends"
                / "EvmYulLeanBridgeLemmas.lean"
            )
            infra.parent.mkdir(parents=True, exist_ok=True)
            infra.write_text("sorry\nsorry\nsorry\n", encoding="utf-8")

            # Create a normal file with a sorry (should count as proof sorry)
            normal = root / "Compiler" / "Proofs" / "Normal.lean"
            normal.write_text("sorry\n", encoding="utf-8")

            (root / "Verity").mkdir(parents=True, exist_ok=True)

            old_root = verification_metrics.ROOT
            try:
                verification_metrics.ROOT = root
                total, proof = verification_metrics.get_sorry_count()
                self.assertEqual(total, 4, "all 4 sorrys counted in total")
                self.assertEqual(proof, 1, "only non-infrastructure sorry is proof_sorry")
            finally:
                verification_metrics.ROOT = old_root

    def test_infrastructure_sorrys_zero_when_no_infra_file(self) -> None:
        """Without infrastructure files, all sorrys count as proof sorrys."""
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Verity").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "Proof.lean").write_text("sorry\nsorry\n", encoding="utf-8")

            old_root = verification_metrics.ROOT
            try:
                verification_metrics.ROOT = root
                total, proof = verification_metrics.get_sorry_count()
                self.assertEqual(total, 2)
                self.assertEqual(proof, 2)
            finally:
                verification_metrics.ROOT = old_root

    def test_load_metrics_from_artifact_rejects_boolean_numeric_field(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            artifact = Path(tmpdir) / "verification_status.json"
            payload = self._fixture_metrics()
            payload["proofs"]["axioms"] = True
            artifact.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "proofs\\.axioms must be an integer, got bool"):
                verification_metrics.load_metrics_from_artifact(artifact)

    def test_load_metrics_from_artifact_rejects_missing_schema_version(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            artifact = Path(tmpdir) / "verification_status.json"
            payload = self._fixture_metrics()
            del payload["schema_version"]
            artifact.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "root: missing required keys: schema_version"):
                verification_metrics.load_metrics_from_artifact(artifact)

    def test_load_metrics_from_artifact_rejects_unknown_top_level_key(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            artifact = Path(tmpdir) / "verification_status.json"
            payload = self._fixture_metrics()
            payload["extra"] = 1
            artifact.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "root: unknown keys: extra"):
                verification_metrics.load_metrics_from_artifact(artifact)

    @staticmethod
    def _fixture_metrics(*, axioms: object = 0) -> dict:
        return {
            "schema_version": 1,
            "theorems": {
                "total": 1, "categories": 1, "per_contract": {"Counter": 1}, "covered": 1,
                "coverage_percent": 100, "excluded": 0, "proven": 1, "stdlib": 0,
                "non_stdlib_total": 1,
            },
            "tests": {
                "foundry_functions": 1, "suites": 1, "property_functions": 1,
                "differential_total": 1,
            },
            "proofs": {"axioms": axioms, "sorry": 0},
            "codebase": {"core_lines": 1, "example_contracts": 1},
            "toolchain": {"lean": "lean", "solc": "0.8.33"},
        }

    def _with_collected(self, payload: dict):
        saved = verification_metrics.collect_metrics
        verification_metrics.collect_metrics = lambda: payload
        self.addCleanup(setattr, verification_metrics, "collect_metrics", saved)

    def test_current_metrics_rejects_invalid_schema(self) -> None:
        self._with_collected(self._fixture_metrics(axioms=True))
        with self.assertRaisesRegex(ValueError, "proofs\\.axioms must be an integer, got bool"):
            verification_metrics.current_metrics()

    def test_generate_verification_status_writes_loadable_output(self) -> None:
        import generate_verification_status

        payload = self._fixture_metrics()
        self._with_collected(payload)
        with tempfile.TemporaryDirectory() as tmpdir:
            output = Path(tmpdir) / "out" / "verification_status.json"
            with contextlib.redirect_stdout(io.StringIO()):
                generate_verification_status.main(["--output", str(output)])
            self.assertEqual(verification_metrics.load_metrics_from_artifact(output), payload)

    def test_metrics_json_is_not_tracked(self) -> None:
        """The metrics JSON is a build output: git must neither track it nor show it as new."""
        root = verification_metrics.ROOT
        if not (root / ".git").exists():
            self.skipTest("not a git checkout")
        rel = "artifacts/verification_status.json"
        tracked = subprocess.run(
            ["git", "-C", str(root), "ls-files", "--error-unmatch", rel],
            capture_output=True, text=True, check=False,
        )
        self.assertNotEqual(tracked.returncode, 0, f"{rel} must not be committed")
        ignored = subprocess.run(
            ["git", "-C", str(root), "check-ignore", "-q", rel], check=False
        )
        self.assertEqual(ignored.returncode, 0, f"{rel} must be git-ignored")


if __name__ == "__main__":
    unittest.main()
