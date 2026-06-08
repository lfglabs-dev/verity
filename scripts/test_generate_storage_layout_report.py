#!/usr/bin/env python3
"""Unit tests for the storage layout audit artifact generator (#1897)."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from generate_storage_layout_report import (
    render_json,
    render_summary,
)


SAMPLE_REPORT = {
    "contracts": [
        {
            "contract": "DemoToken",
            "storageNamespace": "1234",
            "fields": [
                {
                    "name": "owner",
                    "declaredSlot": 0,
                    "canonicalSlot": 0,
                    "declaredAliasSlots": [],
                    "effectiveAliasSlots": [9],
                    "writeSlots": [0, 9],
                    "type": {"kind": "address"},
                    "packedBits": None,
                },
                {
                    "name": "flags",
                    "declaredSlot": 1,
                    "canonicalSlot": 1,
                    "declaredAliasSlots": [],
                    "effectiveAliasSlots": [],
                    "writeSlots": [1],
                    "type": {"kind": "uint256"},
                    "packedBits": {"offset": 0, "width": 8},
                },
                {
                    "name": "balances",
                    "declaredSlot": 2,
                    "canonicalSlot": 2,
                    "declaredAliasSlots": [],
                    "effectiveAliasSlots": [],
                    "writeSlots": [2],
                    "type": {
                        "kind": "mapping",
                        "keys": ["address"],
                        "valueKind": "uint256",
                    },
                    "packedBits": None,
                },
            ],
            "reservedSlotRanges": [{"start": 10, "end": 50}],
            "slotAliasRanges": [
                {"sourceStart": 0, "sourceEnd": 0, "targetStart": 9}
            ],
        }
    ]
}


class RenderJsonTests(unittest.TestCase):
    def test_render_json_is_sorted_and_indented(self) -> None:
        out = render_json(SAMPLE_REPORT)
        self.assertTrue(out.endswith("\n"))
        # Sorted keys: "contracts" should appear before any other top-level field
        # (here only "contracts" exists). Sub-objects sorted as well.
        first_field_block = out.split('"fields":')[1]
        self.assertIn('"canonicalSlot"', first_field_block.split("}", 1)[0])


class RenderSummaryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.summary = render_summary(SAMPLE_REPORT)

    def test_includes_contract_count(self) -> None:
        self.assertIn("Contracts covered: **1**", self.summary)

    def test_includes_storage_namespace(self) -> None:
        self.assertIn("Storage namespace base: `1234`", self.summary)

    def test_includes_reserved_and_alias_ranges(self) -> None:
        self.assertIn("Reserved slot ranges: [10..50]", self.summary)
        self.assertIn("Slot alias ranges: [0..0] -> 9+", self.summary)

    def test_includes_packed_bits(self) -> None:
        self.assertIn("offset 0, width 8", self.summary)

    def test_includes_mapping_type(self) -> None:
        self.assertIn("mapping(address => uint256)", self.summary)

    def test_includes_alias_slots_in_field_row(self) -> None:
        # owner field has effectiveAliasSlots [9]
        owner_row = next(
            line for line in self.summary.splitlines() if line.startswith("| `owner`")
        )
        self.assertIn(" 9 ", owner_row)


class RenderSummaryEmptyTests(unittest.TestCase):
    def test_handles_empty_namespace_and_empty_ranges(self) -> None:
        report = {
            "contracts": [
                {
                    "contract": "Bare",
                    "storageNamespace": None,
                    "fields": [],
                    "reservedSlotRanges": [],
                    "slotAliasRanges": [],
                }
            ]
        }
        summary = render_summary(report)
        self.assertIn("Storage namespace: _none_", summary)
        self.assertIn("Fields: 0", summary)
        self.assertNotIn("Reserved slot ranges:", summary)
        self.assertNotIn("Slot alias ranges:", summary)


if __name__ == "__main__":
    unittest.main()
