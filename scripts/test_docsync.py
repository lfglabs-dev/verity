#!/usr/bin/env python3
"""Unit tests for the unified schema-driven doc-sync engine (scripts/docsync.py, #1987)."""

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


class JsonArtifactDocTableConditionTests(unittest.TestCase):
    def test_passes_when_extracted_rows_match_target_docs(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "artifacts").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            (root / "artifacts" / "sample.json").write_text(
                json.dumps({"total": 36, "proved": 36}),
                encoding="utf-8",
            )
            (root / "docs" / "STATUS.md").write_text(
                "# Status\n\n| Metric | Value |\n| --- | --- |\n| Proved | 36 / 36 |\n",
                encoding="utf-8",
            )
            cond = docsync.JsonArtifactDocTableCondition(
                artifact_rel="artifacts/sample.json",
                targets={"STATUS": "docs/STATUS.md"},
                row_extractor=lambda data: [f"| Proved | {data['proved']} / {data['total']} |"],
                pass_message="sample table sync passed",
            )
            stdout = io.StringIO()
            with redirect_stdout(stdout):
                rc = cond.check(root)
            self.assertEqual(rc, 0)
            self.assertIn("sample table sync passed", stdout.getvalue())

    def test_fails_when_row_missing_from_markdown_doc(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "artifacts").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            (root / "artifacts" / "sample.json").write_text(
                json.dumps({"total": 36, "proved": 36}),
                encoding="utf-8",
            )
            (root / "docs" / "STATUS.md").write_text(
                "# Status\n\n| Proved | 35 / 36 |\n",
                encoding="utf-8",
            )
            cond = docsync.JsonArtifactDocTableCondition(
                artifact_rel="artifacts/sample.json",
                targets={"STATUS": "docs/STATUS.md"},
                row_extractor=lambda data: {"STATUS": [f"| Proved | {data['proved']} / {data['total']} |"]},
            )
            stderr = io.StringIO()
            with redirect_stderr(stderr):
                rc = cond.check(root)
            self.assertEqual(rc, 1)
            self.assertIn("docs/STATUS.md is out of sync with artifacts/sample.json", stderr.getvalue())

    def test_fails_when_artifact_missing(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            cond = docsync.JsonArtifactDocTableCondition(
                artifact_rel="artifacts/missing.json",
                targets={"STATUS": "docs/STATUS.md"},
            )
            stderr = io.StringIO()
            with redirect_stderr(stderr):
                rc = cond.check(root)
            self.assertEqual(rc, 1)
            self.assertIn("Missing: artifacts/missing.json", stderr.getvalue())


class ScriptDelegatedConditionTests(unittest.TestCase):
    def test_registry_contains_all_consolidated_entries(self) -> None:
        expected = {
            "axiomatized_primitive_boundary",
            "bridge_coverage",
            "builtin_bridge_matrix",
            "builtin_list",
            "docs_workflow",
            "interpreter_feature_boundary_catalog",
            "interpreter_feature_summary",
            "layer2_boundary",
            "layer2_boundary_catalog",
            "linear_memory_boundary",
            "low_level_call_boundary",
            "property_manifest",
            "struct_mapping_surface",
            "verify_sync",
        }
        self.assertEqual(set(docsync.REGISTRY.keys()), expected)
        self.assertIs(docsync.REGISTRY, docsync.ENTRIES)

    def test_delegated_entries_pass_on_repository_root(self) -> None:
        for name in (
            "interpreter_feature_summary",
            "builtin_bridge_matrix",
            "bridge_coverage",
            "builtin_list",
            "docs_workflow",
            "property_manifest",
            "verify_sync",
        ):
            stdout = io.StringIO()
            stderr = io.StringIO()
            with redirect_stdout(stdout), redirect_stderr(stderr):
                rc = docsync.run_entry(name)
            self.assertEqual(rc, 0, msg=f"{name} failed: {stderr.getvalue()}")

    def test_cli_list_and_check_all(self) -> None:
        list_out = io.StringIO()
        with redirect_stdout(list_out):
            rc = docsync.main(["--list"])
        self.assertEqual(rc, 0)
        listed = [line.strip() for line in list_out.getvalue().splitlines() if line.strip()]
        self.assertEqual(listed, sorted(docsync.REGISTRY.keys()))

        check_out = io.StringIO()
        check_err = io.StringIO()
        with redirect_stdout(check_out), redirect_stderr(check_err):
            rc = docsync.main(["--check"])
        self.assertEqual(rc, 0, msg=check_err.getvalue())


if __name__ == "__main__":
    unittest.main()
