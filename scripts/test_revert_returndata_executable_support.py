#!/usr/bin/env python3
"""Regression guard for executable `revertReturndata` support claims."""

from __future__ import annotations

import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MATRIX = ROOT / "artifacts" / "interpreter_feature_matrix.json"
COMMON = ROOT / "Contracts" / "Common.lean"


class RevertReturndataExecutableSupportTests(unittest.TestCase):
    def test_noop_intrinsic_is_not_claimed_as_executable_support(self) -> None:
        matrix = json.loads(MATRIX.read_text(encoding="utf-8"))
        entry = next(
            item for item in matrix["stmt_features"]
            if item["feature"] == "revertReturndata"
        )
        noop = "def revertReturndata : Contract Unit := pure ()" in COMMON.read_text(encoding="utf-8")
        if noop:
            self.assertNotEqual(entry["SourceInterpreter_basic"], "supported")
            self.assertNotEqual(entry["SourceInterpreter_fuel"], "supported")


if __name__ == "__main__":
    unittest.main()
