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


class NonAliasClaimsTests(unittest.TestCase):
    """Bugbot #1967: the certificate must surface overlapping write slot
    sets as `writeSetsOverlap` rather than asserting a false
    `distinctScalarSlots` claim. The summary must also include each
    family's effective write slot set so auditors can confirm the
    conflict."""

    def _render(self, claims: list[dict]) -> str:
        report = {
            "contracts": [
                {
                    "contract": "Demo",
                    "storageNamespace": None,
                    "fields": [],
                    "reservedSlotRanges": [],
                    "slotAliasRanges": [],
                    "storageFamilies": [
                        {"name": "a", "kind": "scalar", "rootSlot": 0,
                         "keccakPreimage": None, "structWordRange": None},
                        {"name": "b", "kind": "scalar", "rootSlot": 1,
                         "keccakPreimage": None, "structWordRange": None},
                    ],
                    "nonAliasClaims": claims,
                }
            ]
        }
        return render_summary(report)

    def test_distinct_scalar_slots_kept_distinct(self) -> None:
        summary = self._render([
            {
                "a": "a", "b": "b",
                "aSlot": 0, "bSlot": 1,
                "aWriteSlots": [0], "bWriteSlots": [1],
                "justification": "distinctScalarSlots",
            },
        ])
        # Look for the per-claim rendering, not the documentation header.
        claims_section = summary.split("**Non-alias claims**", 1)[1]
        self.assertIn("`distinctScalarSlots`", claims_section)
        self.assertIn("`a` (writes 0)", claims_section)
        self.assertIn("`b` (writes 1)", claims_section)
        self.assertNotIn("`writeSetsOverlap`", claims_section)

    def test_overlapping_write_slots_surfaced_as_conflict(self) -> None:
        summary = self._render([
            {
                "a": "a", "b": "b",
                "aSlot": 0, "bSlot": 1,
                "aWriteSlots": [0, 5], "bWriteSlots": [1, 5],
                "justification": "writeSetsOverlap",
            },
        ])
        claims_section = summary.split("**Non-alias claims**", 1)[1]
        self.assertIn("`writeSetsOverlap`", claims_section)
        self.assertIn("shared write slot: [5]", claims_section)
        self.assertNotIn("`distinctScalarSlots`", claims_section)


if __name__ == "__main__":
    unittest.main()
