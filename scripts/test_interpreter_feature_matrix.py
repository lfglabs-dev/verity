from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from interpreter_feature_matrix import load_feature_matrix


class InterpreterFeatureMatrixTests(unittest.TestCase):
    def test_load_feature_matrix_accepts_retired_spec_interpreter_keys(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "interpreter_feature_matrix.json"
            path.write_text(
                json.dumps(
                    {
                        "interpreters": {
                            "SpecInterpreter_basic": {"entry": "oldBasic"},
                            "SpecInterpreter_fuel": {"entry": "oldFuel"},
                        },
                        "default_execution_path": "SpecInterpreter_fuel",
                        "expr_features": [
                            {
                                "feature": "literal",
                                "SpecInterpreter_basic": "supported",
                                "SpecInterpreter_fuel": "supported",
                            }
                        ],
                        "stmt_features": [],
                    }
                ),
                encoding="utf-8",
            )

            matrix = load_feature_matrix(path)

        self.assertEqual(matrix["default_execution_path"], "SourceInterpreter_fuel")
        self.assertIn("SourceInterpreter_basic", matrix["interpreters"])
        self.assertIn("SourceInterpreter_fuel", matrix["interpreters"])
        self.assertNotIn("SpecInterpreter_basic", matrix["interpreters"])
        self.assertEqual(matrix["expr_features"][0]["SourceInterpreter_basic"], "supported")
        self.assertEqual(matrix["expr_features"][0]["SourceInterpreter_fuel"], "supported")


if __name__ == "__main__":
    unittest.main()
