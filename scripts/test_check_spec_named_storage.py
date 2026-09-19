#!/usr/bin/env python3
"""Tests for the spec named-storage gate."""

from __future__ import annotations

import contextlib
import io
import tempfile
import unittest
from pathlib import Path

import check_spec_named_storage

NAMED_SPEC = '''\
namespace Contracts.VaultFromSolidity.Spec
/-- Never write `s.readSlot 0` or `ContractState.readMap s 2 a` here. -/
def solvent (v : Storage) : Prop := v.totalAssets = v.totalSupply
def balanceOf_spec (account : Address) (result : Uint256) (v : Storage) : Prop :=
  result = v.shareBalances account
def depositFits (amount : Uint256) (v : Storage) : Prop :=
  v.totalAssets.val + amount.val ≤ Verity.Core.MAX_UINT256
def label : String := "readMap 2"
def storage2 (v : Storage) := v.totalSupply
def readSlotted (v : Storage) := v.totalSupply
end Contracts.VaultFromSolidity.Spec
'''

RAW_SPEC = '''\
namespace Contracts.VaultFromSolidity.Spec
def solvent (s : ContractState) : Prop := s.readSlot 0 = s.readSlot 1
def balance (s : Storage) (a : Address) := ContractState.readMap s 2 a
def raw (s : Storage) := s.storage (1)
def ghost (s : Storage) := s.knownAddresses
end Contracts.VaultFromSolidity.Spec
'''

# Each of these addressed storage by number while passing the first version of
# the gate, which only looked for a numeric literal right after a short list of
# accessor names on the same line.
BYPASSES = (
    ("def f (v : Storage) := v.readMapUint 3 k", "raw `ContractState` accessor `readMapUint`"),
    ("def f (v : Storage) := v.readTransient 1", "raw `ContractState` accessor `readTransient`"),
    ("def f (v : Storage) := v.readSlot\n    0", "raw `ContractState` accessor `readSlot`"),
    ("def f (s : Storage) := ContractState.readSlot (s) 2", "`ContractState` named directly"),
    ("def f (s : Storage) := s.readSlot <| 0", "raw `ContractState` accessor `readSlot`"),
    ("def f (s : Storage) := (s.storage) 0", "raw `ContractState` accessor `storage`"),
    ("def f (s : Storage) := s.readSlot totalAssetsSlot.slot", "raw `ContractState` accessor `readSlot`"),
    ("def f (s : Storage) := s.storageWords key", "raw storage field `storageWords`"),
    ("def f (s : Storage) := s.1 0", "positional projection `.1`"),
    ("def f (s : Storage) := Storage.casesOn s fun w _ _ => w", "structure eliminator `Storage.casesOn`"),
    ("def f (s : Storage) := Verity.ContractState.readSlot s 0", "`ContractState` named directly"),
)


class SpecNamedStorageTests(unittest.TestCase):
    def run_gate(self, spec: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            for rel in check_spec_named_storage.SPEC_FILES:
                target = root / rel
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(spec, encoding="utf-8")
            old_root = check_spec_named_storage.ROOT
            output = io.StringIO()
            try:
                check_spec_named_storage.ROOT = root
                with contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
                    status = check_spec_named_storage.main()
            finally:
                check_spec_named_storage.ROOT = old_root
            return status, output.getvalue()

    def test_accessors_come_from_core(self) -> None:
        accessors = check_spec_named_storage.RAW_ACCESSORS
        for name in ("readSlot", "writeSlot", "readMap", "writeMap", "readMapUint",
                     "readTransient", "storage", "storageMap", "readArray"):
            self.assertIn(name, accessors)
        self.assertNotIn("Contract", accessors)
        self.assertEqual(check_spec_named_storage.raw_accessors("def readSlot := 0\n"), frozenset())

    def test_named_spec_passes(self) -> None:
        status, output = self.run_gate(NAMED_SPEC)
        self.assertEqual(status, 0, output)

    def test_raw_slot_spec_fails(self) -> None:
        status, output = self.run_gate(RAW_SPEC)
        self.assertEqual(status, 1)
        self.assertEqual(
            check_spec_named_storage.find_violations(RAW_SPEC),
            [
                (2, "raw `ContractState` accessor `readSlot`"),
                (2, "raw `ContractState` accessor `readSlot`"),
                (2, "`ContractState` named directly"),
                (3, "raw `ContractState` accessor `readMap`"),
                (3, "`ContractState` named directly"),
                (4, "raw `ContractState` accessor `storage`"),
                (5, "`knownAddresses` ghost bookkeeping"),
            ],
        )
        self.assertIn("Spec.lean:2:", output)

    def test_bypasses_are_rejected(self) -> None:
        for spec, message in BYPASSES:
            with self.subTest(spec=spec):
                messages = [m for _, m in check_spec_named_storage.find_violations(spec)]
                self.assertIn(message, messages)
                self.assertEqual(self.run_gate(spec)[0], 1)

    def test_missing_opted_in_file_fails(self) -> None:
        old_root = check_spec_named_storage.ROOT
        output = io.StringIO()
        with tempfile.TemporaryDirectory() as tmpdir:
            try:
                check_spec_named_storage.ROOT = Path(tmpdir)
                with contextlib.redirect_stderr(output):
                    status = check_spec_named_storage.main()
            finally:
                check_spec_named_storage.ROOT = old_root
        self.assertEqual(status, 1)
        self.assertIn("opted-in spec file is missing", output.getvalue())


if __name__ == "__main__":
    unittest.main()
