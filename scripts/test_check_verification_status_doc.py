#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_verification_status_doc
import sync_verification_status_doc

METRICS = {
    "schema_version": 1,
    "theorems": {
        "total": 7,
        "categories": 2,
        "per_contract": {"Counter": 2, "ReentrancyExample": 5},
        "covered": 3,
        "coverage_percent": 43,
        "excluded": 1,
        "proven": 7,
        "stdlib": 0,
        "non_stdlib_total": 7,
    },
    "tests": {
        "foundry_functions": 10,
        "suites": 2,
        "property_functions": 3,
        "differential_total": 10000,
    },
    "proofs": {"axioms": 1, "sorry": 0},
    "codebase": {"core_lines": 1, "example_contracts": 2},
    "toolchain": {"lean": "lean", "solc": "0.8.33"},
}
COVERED = {"Counter": {"a"}, "ReentrancyExample": {"r1", "r2"}}
EXCLUSIONS = {"Counter": {"b"}}

COMMITTED = textwrap.dedent(
    """\
    # Verification Status

    <!-- BEGIN GENERATED LAYER 1 COUNTS -->
    | Contract | Status | Location |
    |----------|--------|----------|
    | Counter | Complete | `Contracts/Counter/Proofs/` |
    | ReentrancyExample | Complete | `Contracts/ReentrancyExample/Contract.lean` |
    | CryptoHash | No specs | `Contracts/CryptoHash/Contract.lean` |
    <!-- END GENERATED LAYER 1 COUNTS -->

    ## Property Test Coverage

    <!-- BEGIN GENERATED PROPERTY COVERAGE -->
    <!-- END GENERATED PROPERTY COVERAGE -->

    0 `sorry` remaining across `Compiler/**/*.lean` and `Verity/**/*.lean` proof modules.
    """
)


class VerificationStatusDocTests(unittest.TestCase):
    def _run_check(self, status_body: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            status = Path(tmpdir) / "VERIFICATION_STATUS.md"
            status.write_text(status_body, encoding="utf-8")
            module = check_verification_status_doc
            saved = (module.STATUS_DOC, module.current_metrics, module.collect_covered, module.load_exclusions)
            module.STATUS_DOC = status
            module.current_metrics = lambda: METRICS
            module.collect_covered = lambda: COVERED
            module.load_exclusions = lambda: EXCLUSIONS
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    try:
                        module.main()
                        return 0, stderr.getvalue()
                    except ValueError as exc:
                        print(exc, file=sys.stderr)
                        return 1, stderr.getvalue()
            finally:
                module.STATUS_DOC, module.current_metrics, module.collect_covered, module.load_exclusions = saved

    def test_committed_doc_without_counts_passes(self) -> None:
        rc, stderr = self._run_check(COMMITTED)
        self.assertEqual(rc, 0, stderr)

    def test_committed_count_bearing_line_fails(self) -> None:
        body = COMMITTED.replace(
            "<!-- BEGIN GENERATED PROPERTY COVERAGE -->\n",
            "**Status**: 43% coverage (3/7), 1 remaining exclusions all proof-only\n\n"
            "<!-- BEGIN GENERATED PROPERTY COVERAGE -->\n",
        )
        rc, stderr = self._run_check(body)
        self.assertEqual(rc, 1)
        self.assertIn("committed coverage status summary", stderr)

    def test_filled_generated_section_fails(self) -> None:
        body = COMMITTED.replace(
            "<!-- END GENERATED PROPERTY COVERAGE -->",
            "Coverage is good.\n<!-- END GENERATED PROPERTY COVERAGE -->",
        )
        rc, stderr = self._run_check(body)
        self.assertEqual(rc, 1)
        self.assertIn("must be empty", stderr)

    def test_missing_contract_row_fails(self) -> None:
        body = COMMITTED.replace("| CryptoHash | No specs | `Contracts/CryptoHash/Contract.lean` |\n", "")
        rc, stderr = self._run_check(body)
        self.assertEqual(rc, 1)
        self.assertIn("Layer 1 contract table", stderr)

    def test_rendered_copy_states_current_counts(self) -> None:
        rendered = sync_verification_status_doc.render_status_doc(COMMITTED, METRICS, COVERED, EXCLUSIONS)
        check_verification_status_doc.check_rendered(rendered, METRICS, COVERED, EXCLUSIONS)
        self.assertIn("| Counter | 2 | Complete | `Contracts/Counter/Proofs/` |", rendered)
        self.assertIn("| **Total** | **7** |", rendered)
        self.assertIn("| Counter | 50% (1/2) | 1 proof-only |", rendered)
        self.assertIn("- **Covered**: 3", rendered)
        self.assertNotIn("GENERATED PROPERTY COVERAGE", rendered)

    def test_rendered_copy_with_stale_metrics_fails(self) -> None:
        rendered = sync_verification_status_doc.render_status_doc(COMMITTED, METRICS, COVERED, EXCLUSIONS)
        stale = rendered.replace("- **Covered**: 3", "- **Covered**: 2")
        with self.assertRaisesRegex(ValueError, "covered bullet says 2, expected 3"):
            check_verification_status_doc.check_rendered(stale, METRICS, COVERED, EXCLUSIONS)


if __name__ == "__main__":
    unittest.main()
