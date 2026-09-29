#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_storage_layout import (
    check_spec_edsl_consistency,
    extract_spec_slots,
)


class CheckStorageLayoutSpecEdslConsistencyTests(unittest.TestCase):
    def test_extract_spec_slots_supports_storage_helper_forms(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            contract_dir = Path(tmpdir) / "ERC721"
            contract_dir.mkdir()
            spec_file = contract_dir / "Spec.lean"
            spec_file.write_text(
                "def constructor_spec (s s' : ContractState) : Prop :=\n"
                "  storageAddrStorage2UpdateSpec 0 1 2\n"
                "    (fun _ => default)\n"
                "    (fun _ => 0)\n"
                "    (fun _ => 0)\n"
                "    sameStorageMapsContext\n"
                "    s s'\n",
                encoding="utf-8",
            )
            rows, errors = extract_spec_slots(spec_file)

        self.assertEqual(errors, [])
        self.assertEqual(
            rows,
            [("slot0", "address", 0), ("slot1", "uint256", 1), ("slot2", "uint256", 2)],
        )

    def test_check_spec_edsl_consistency_reports_missing_spec_slots(self) -> None:
        errors = check_spec_edsl_consistency(
            edsl={"Owned": [("owner", "Address", 0)]},
            spec={"Owned": [("slot1", "uint256", 1)]},
        )

        self.assertEqual(
            errors,
            [
                "Spec-EDSL: Owned.slot1 (uint256) in Spec but not in EDSL",
                "Spec-EDSL: Owned.slot0 (address) in EDSL but not in Spec",
            ],
        )


    def test_check_spec_edsl_consistency_skips_smoke_contracts(self) -> None:
        errors = check_spec_edsl_consistency(
            edsl={"FooSmoke": [("x", "Uint256", 0)]},
            spec={"FooSmoke": [("slot1", "uint256", 1)]},
        )
        self.assertEqual(errors, [])


if __name__ == "__main__":
    unittest.main()
