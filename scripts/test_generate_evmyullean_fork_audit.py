#!/usr/bin/env python3
"""Tests for generate_evmyullean_fork_audit.py."""
from __future__ import annotations

import json
import hashlib
import sys
import tempfile
import unittest
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import generate_evmyullean_fork_audit as audit


def _manifest(url: str, rev: str, input_rev: str) -> dict[str, object]:
    return {
        "packages": [
            {
                "name": "evmyul",
                "url": url,
                "rev": rev,
                "inputRev": input_rev,
            }
        ]
    }


class ForkAuditValidationTests(unittest.TestCase):
    def test_validate_audit_rejects_unsupported_category(self) -> None:
        fork_audit = deepcopy(audit.FORK_AUDIT)
        fork_audit["commits"][0]["category"] = "unreviewed"
        with patch.object(audit, "FORK_AUDIT", fork_audit):
            with self.assertRaisesRegex(RuntimeError, "unsupported category"):
                audit._validate_audit()

    def test_validate_audit_requires_pinned_commit_to_match_audited_tip(self) -> None:
        fork_audit = deepcopy(audit.FORK_AUDIT)
        fork_audit["pinned_commit"] = fork_audit["commits"][0]["sha"]
        with patch.object(audit, "FORK_AUDIT", fork_audit):
            with self.assertRaisesRegex(RuntimeError, "must match the audited fork tip"):
                audit._validate_audit()

    def test_validate_audit_accepts_explicit_evidenced_scope(self) -> None:
        audit._validate_audit()

    def test_unapproved_semantic_change_is_rejected(self) -> None:
        record = deepcopy(audit.FORK_AUDIT)
        record["commits"][0]["semantic_change"] = True
        record["commits"][0]["category"] = "semantic-change"
        with patch.object(audit, "FORK_AUDIT", record):
            with self.assertRaisesRegex(RuntimeError, "unscoped semantic changes"):
                audit._validate_audit()

    def test_semantic_changes_cannot_be_hidden_as_nonsemantic(self) -> None:
        for sha in audit.APPROVED_SEMANTIC_CHANGES:
            with self.subTest(sha=sha):
                record = deepcopy(audit.FORK_AUDIT)
                next(c for c in record["commits"] if c["sha"] == sha)["semantic_change"] = False
                with patch.object(audit, "FORK_AUDIT", record):
                    with self.assertRaisesRegex(RuntimeError, "semantic_change must be True"):
                        audit._validate_audit()

    def test_semantic_category_cannot_be_hidden(self) -> None:
        record = deepcopy(audit.FORK_AUDIT)
        next(c for c in record["commits"] if c["semantic_change"])["category"] = "visibility"
        with patch.object(audit, "FORK_AUDIT", record):
            with self.assertRaisesRegex(RuntimeError, "category disagrees"):
                audit._validate_audit()

    def test_scope_cannot_grow_from_metadata(self) -> None:
        record = deepcopy(audit.FORK_AUDIT)
        record["semantic_scope"]["approved_commits"].append(record["commits"][0]["sha"])
        with patch.object(audit, "FORK_AUDIT", record):
            with self.assertRaisesRegex(RuntimeError, "exactly the approved changes"):
                audit._validate_audit()

    def test_conformance_transfer_claim_is_rejected(self) -> None:
        record = deepcopy(audit.FORK_AUDIT)
        record["semantic_scope"]["upstream_conformance_transfers"] = True
        with patch.object(audit, "FORK_AUDIT", record):
            with self.assertRaisesRegex(RuntimeError, "deny conformance transfer"):
                audit._validate_audit()

    def test_evidence_hash_drift_is_rejected(self) -> None:
        record = deepcopy(audit.FORK_AUDIT)
        record["semantic_scope"]["evidence_sha256"] = "0" * 64
        with patch.object(audit, "FORK_AUDIT", record):
            with self.assertRaisesRegex(RuntimeError, "evidence identity mismatch"):
                audit._validate_audit()

    def _reject_tampered_evidence(self, mutate, diagnostic: str) -> None:
        record = deepcopy(audit.FORK_AUDIT)
        original = audit.ROOT / record["semantic_scope"]["evidence"]
        evidence = json.loads(original.read_text())
        mutate(evidence)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            doc = root / record["semantic_scope"]["document"]
            doc.parent.mkdir(parents=True)
            doc.write_text("scope fixture")
            target = root / record["semantic_scope"]["evidence"]
            target.parent.mkdir(parents=True)
            target.write_text(json.dumps(evidence))
            record["semantic_scope"]["evidence_sha256"] = hashlib.sha256(target.read_bytes()).hexdigest()
            with patch.object(audit, "ROOT", root), patch.object(audit, "FORK_AUDIT", record):
                with self.assertRaisesRegex(RuntimeError, diagnostic):
                    audit._validate_audit()

    def test_partial_exact_head_validation_is_rejected(self) -> None:
        self._reject_tampered_evidence(lambda e: e["validation"]["checks"].pop(), "complete exact-tip")

    def test_missing_real_case_is_rejected(self) -> None:
        self._reject_tampered_evidence(lambda e: e["reference"]["rows"].pop(), "all four independent")

    def test_mutation_compile_failure_is_not_detection(self) -> None:
        self._reject_tampered_evidence(
            lambda e: e["mutations"]["rows"][0].update(detected=[], replay=[]), "runtime failures")

    def test_mutation_replay_must_match(self) -> None:
        self._reject_tampered_evidence(
            lambda e: e["mutations"]["rows"][0].update(replay=["different"]), "identical replay")

    def test_empty_runtime_success_is_rejected(self) -> None:
        self._reject_tampered_evidence(lambda e: e["runtime"].update(output=[]), "strict native success")

    def test_native_source_identity_disagreement_is_rejected(self) -> None:
        self._reject_tampered_evidence(
            lambda e: e["runtime"]["identity"].update({"EvmYul/EVM/Semantics.lean": "0" * 64}),
            "inconsistent native source identities")

    def test_cross_check_manifest_pin_checks_all_tracked_manifests(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            main_manifest = root / "lake-manifest.json"
            package_manifest = root / "packages" / "verity-compiler" / "lake-manifest.json"
            package_manifest.parent.mkdir(parents=True)
            expected_url = audit.FORK_AUDIT["fork_url"] + ".git"
            expected_rev = audit.FORK_AUDIT["pinned_commit"]
            main_manifest.write_text(
                json.dumps(_manifest(expected_url, expected_rev, expected_rev)),
                encoding="utf-8",
            )
            package_manifest.write_text(
                json.dumps(_manifest(expected_url, "0" * 40, expected_rev)),
                encoding="utf-8",
            )
            with patch.object(audit, "ROOT", root), \
                 patch.object(audit, "LAKE_MANIFESTS", [main_manifest, package_manifest]):
                with self.assertRaisesRegex(RuntimeError, "packages/verity-compiler/lake-manifest.json pins"):
                    audit._cross_check_manifest_pin()

    def test_cross_check_manifest_pin_checks_input_rev(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = root / "lake-manifest.json"
            expected_url = audit.FORK_AUDIT["fork_url"] + ".git"
            expected_rev = audit.FORK_AUDIT["pinned_commit"]
            manifest.write_text(
                json.dumps(_manifest(expected_url, expected_rev, "0" * 40)),
                encoding="utf-8",
            )
            with patch.object(audit, "ROOT", root), \
                 patch.object(audit, "LAKE_MANIFESTS", [manifest]):
                with self.assertRaisesRegex(RuntimeError, "inputRev"):
                    audit._cross_check_manifest_pin()


if __name__ == "__main__":
    unittest.main()
