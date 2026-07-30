from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_macro_roundtrip_fuzz_coverage as check


class MacroRoundTripFuzzCoverageTests(unittest.TestCase):
    def test_missing_contract_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            contract, artifacts = root / "Contract.lean", root / "artifacts"
            contract.write_text(
                "import Compiler\nverity_contract Missing where\n", encoding="utf-8"
            )
            artifacts.mkdir()
            self.assertEqual(check._check_coverage([contract], artifacts), 1)

    def test_matching_contract_passes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            contract, artifacts = root / "Contract.lean", root / "artifacts"
            contract.write_text(
                "import Compiler\nverity_contract Covered where\n", encoding="utf-8"
            )
            artifacts.mkdir()
            (artifacts / "PropertyCovered.t.sol").write_text("", encoding="utf-8")
            self.assertEqual(check._check_coverage([contract], artifacts), 0)


if __name__ == "__main__":
    unittest.main()
