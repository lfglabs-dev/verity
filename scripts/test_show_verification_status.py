#!/usr/bin/env python3
from __future__ import annotations

import io
import json
import sys
import unittest
from contextlib import redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import show_verification_status

METRICS = {
    "schema_version": 1,
    "theorems": {"total": 7, "per_contract": {"Counter": 2}},
    "tests": {"foundry_functions": 10},
}


class ShowVerificationStatusTests(unittest.TestCase):
    def _run(self, argv: list[str]) -> str:
        saved = show_verification_status.current_metrics
        show_verification_status.current_metrics = lambda: METRICS
        try:
            out = io.StringIO()
            with redirect_stdout(out):
                show_verification_status.main(argv)
            return out.getvalue()
        finally:
            show_verification_status.current_metrics = saved

    def test_default_output_is_dotted_key_lines(self) -> None:
        self.assertEqual(
            self._run([]).splitlines(),
            [
                "schema_version: 1",
                "theorems.total: 7",
                "theorems.per_contract.Counter: 2",
                "tests.foundry_functions: 10",
            ],
        )

    def test_json_output_round_trips(self) -> None:
        self.assertEqual(json.loads(self._run(["--json"])), METRICS)


if __name__ == "__main__":
    unittest.main()
