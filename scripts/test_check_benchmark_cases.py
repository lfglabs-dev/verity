#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_benchmark_cases


class CheckBenchmarkCasesTests(unittest.TestCase):
    def test_no_benchmark_metadata_is_ok(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            self.assertEqual(check_benchmark_cases.check_benchmark_cases(Path(tmpdir)), [])

    def test_overlaid_formal_audit_case_requires_started_status_and_upstream_commit(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            case = root / "Benchmark" / "Cases" / "UnlinkXyz" / "Pool"
            case.mkdir(parents=True)
            (case / "FormalAudit.lean").write_text("example : True := trivial\n", encoding="utf-8")
            (case / "case.yaml").write_text(
                "proof_status: not_started\naudit_target_commit: not-a-sha\n",
                encoding="utf-8",
            )

            errors = check_benchmark_cases.check_benchmark_cases(root)

        self.assertIn("Benchmark/Cases/UnlinkXyz/Pool/case.yaml: missing upstream_commit", errors)
        self.assertIn(
            "Benchmark/Cases/UnlinkXyz/Pool/case.yaml: FormalAudit.lean exists but proof_status is not_started",
            errors,
        )
        self.assertIn(
            "Benchmark/Cases/UnlinkXyz/Pool/case.yaml: audit_target_commit must be a 7-40 character git hex prefix",
            errors,
        )

    def test_valid_case_passes(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            case = root / "Benchmark" / "Cases" / "UnlinkXyz" / "Pool"
            case.mkdir(parents=True)
            (case / "FormalAudit.lean").write_text("example : True := trivial\n", encoding="utf-8")
            (case / "case.yaml").write_text(
                "proof_status: proved\nupstream_commit: 7617b3e\naudit_target_commit: 7617b3e\n",
                encoding="utf-8",
            )

            self.assertEqual(check_benchmark_cases.check_benchmark_cases(root), [])

    def test_standalone_benchmark_cases_layout_is_checked(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            case = root / "cases" / "unlink_xyz" / "pool"
            case.mkdir(parents=True)
            (case / "case.yaml").write_text(
                "proof_status: proved\nupstream_commit: 7617b3e\n",
                encoding="utf-8",
            )

            self.assertEqual(check_benchmark_cases.check_benchmark_cases(root), [])


if __name__ == "__main__":
    unittest.main()
