#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_foundry_yul_dirs as check


class FoundryYulDirsTests(unittest.TestCase):
    def _run(self, files: dict[str, str]) -> tuple[list[str], int]:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for rel, body in files.items():
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(body)
            return check.offending_lines(root), check.main(["--root", str(root)])

    def test_artifacts_yul_fallback_is_reported(self) -> None:
        lines, status = self._run({"test/yul/Base.sol": 'return "artifacts/yul";\n'})
        self.assertEqual(status, 1)
        self.assertEqual(lines, ['test/yul/Base.sol:1: return "artifacts/yul";'])

    def test_compiler_yul_and_other_artifacts_dirs_are_fine(self) -> None:
        lines, status = self._run({
            "test/A.t.sol": 'string dir = "compiler/yul";\n'
                            'string m = "artifacts/struct-bytes-member-mutant";\n'
                            'string g = "artifacts/yul_identity_gap_matrix.json";\n',
            "test/B.t.sol": '/// never the committed `artifacts/yul` snapshots\n',
            "scripts/x.py": '"artifacts/yul"\n',
        })
        self.assertEqual((lines, status), ([], 0))


if __name__ == "__main__":
    unittest.main()
