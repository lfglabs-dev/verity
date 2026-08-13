#!/usr/bin/env python3
"""Storage-lens API freeze gate (C5 step 1).

The C5 storage-representation flip (one word-addressed `Nat -> Uint256` map
with Solidity-layout slot derivation) requires that every read/write of
`Verity.ContractState`'s storage channels go through the canonical lens API
(`readSlot`/`writeSlot`/`writeMap`/... in `Verity/Core.lean`) instead of raw
record updates like `{ s with storageMap := ... }`.

This gate is a RATCHET: raw storage-channel record-update sites are counted
per file and frozen at the current baseline below.  Any NEW raw site fails
the check; migrating sites down requires shrinking the baseline (the script
prints the expected new entry).  The goal is a monotonically shrinking
baseline until only `Verity/Core.lean` remains, at which point the flip
(C5 step 3) can swap the representation under stable lens names.

Scope notes:
- The six channels unique to `ContractState` (`contractStorage`,
  `storageAddr`, `storageMap`, `storageMapUint`, `storageMap2`,
  `storageArray`) are checked repo-wide.
- `storage :=` / `transientStorage :=` are only checked under `Verity/` and
  `Contracts/`: under `Compiler/` those field names also belong to
  `IRState`/`DenoteState`-style records, which are proof-side runtime states,
  not the source `ContractState`.  Raw `ContractState` writes under
  `Compiler/` on those two fields are therefore NOT caught by this gate
  (known v1 boundary; they are enumerated in the baseline where they use a
  unique channel).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

UNIQUE_CHANNELS = (
    "contractStorage",
    "storageAddr",
    "storageMap",
    "storageMapUint",
    "storageMap2",
    "storageArray",
)
SHARED_CHANNELS = ("storage", "transientStorage")

UNIQUE_RE = re.compile(
    r"(?<![\w.])(?:«)?(" + "|".join(UNIQUE_CHANNELS) + r")(?:»)?\s*:=")
SHARED_RE = re.compile(
    r"(?<![\w.])(?:«)?(" + "|".join(SHARED_CHANNELS) + r")(?:»)?\s*:=")

SCAN_DIRS = ("Verity", "Contracts", "Compiler")
SHARED_SCAN_DIRS = ("Verity", "Contracts")

# file (relative to repo root) -> frozen raw-site count.  Burn this down;
# never grow it.  `Verity/Core.lean` hosts the lens implementations and the
# canonical `defaultState`/`emitEvent`-style literals; it is the only file
# meant to keep raw access after the migration completes.
BASELINE = {
    # Lens implementations + defaultState (the permanent residue).
    "Verity/Core.lean": 26,
    # Denotational bulk writes (multi-slot / packed): need bulk lenses
    # before they can migrate (C5 step 2).
    "Verity/Core/Model/Denote.lean": 26,
    "Verity/Core/Free/TypedIR.lean": 7,
    # Bridge lemma statements equating monad ops with the raw update form;
    # restated via lenses when the simp attribute moves to `storage_simps`.
    "Verity/Proofs/Stdlib/Automation.lean": 3,
    "Verity/Proofs/Stdlib/MappingAutomation.lean": 3,
    "Verity/Specs/Common/Sum.lean": 1,
    # Contract proofs spelling out full post-state record literals, and test
    # fixtures constructing initial states by raw literal; both migrate in
    # C5 step 2 (proofs onto `storage_simps`, fixtures onto lens chains).
    "Contracts/Common.lean": 5,
    "Contracts/ERC20/Proofs/Basic.lean": 16,
    "Contracts/Interpreter.lean": 7,
    "Contracts/Ledger/Proofs/Basic.lean": 32,
    "Contracts/Owned/Proofs/Basic.lean": 8,
    "Contracts/OwnedCounter/Proofs/Basic.lean": 24,
    "Contracts/ReentrancyExample/Contract.lean": 7,
    "Contracts/SafeCounter/Proofs/Basic.lean": 16,
    "Contracts/SimpleToken/Proofs/Basic.lean": 16,
    "Contracts/Smoke/Storage.lean": 5,
    "Contracts/TypedIRTests.lean": 79,
    "Compiler/CompilationModelFeatureTest.lean": 3,
    "Compiler/Proofs/IRGeneration/SourceSemantics.lean": 8,
    "Compiler/Proofs/IRGeneration/SourceSemanticsFeatureTest.lean": 1,
    "Compiler/Proofs/Storage/StructArrayStorage.lean": 1,
    "Compiler/Proofs/StorageBounds.lean": 1,
    "Compiler/TypedIRCompilerCorrectness.lean": 9,
}


def count_sites(path: Path) -> int:
    rel = path.relative_to(ROOT).as_posix()
    text = path.read_text(encoding="utf-8")
    # Strip line comments to avoid counting documentation.
    text = re.sub(r"--[^\n]*", "", text)
    count = len(UNIQUE_RE.findall(text))
    if rel.split("/", 1)[0] in SHARED_SCAN_DIRS:
        count += len(SHARED_RE.findall(text))
    return count


def main() -> int:
    if "--print-baseline" in sys.argv:
        for top in SCAN_DIRS:
            for path in sorted((ROOT / top).rglob("*.lean")):
                if ".lake" in path.parts:
                    continue
                count = count_sites(path)
                if count:
                    print(f'    "{path.relative_to(ROOT).as_posix()}": {count},')
        return 0
    failures = []
    seen = {}
    for top in SCAN_DIRS:
        for path in sorted((ROOT / top).rglob("*.lean")):
            if ".lake" in path.parts:
                continue
            rel = path.relative_to(ROOT).as_posix()
            count = count_sites(path)
            if count:
                seen[rel] = count
            allowed = BASELINE.get(rel, 0)
            if count > allowed:
                failures.append((rel, count, allowed))
    for rel, allowed in BASELINE.items():
        actual = seen.get(rel, 0)
        if actual < allowed:
            failures.append((rel, actual, allowed))
    if failures:
        print("storage-lens freeze gate FAILED (C5 step 1):")
        for rel, count, allowed in failures:
            if count > allowed:
                print(f"  {rel}: {count} raw storage-channel update sites "
                      f"(baseline {allowed}).")
                print("    New raw `{ s with storage... := ... }` sites are "
                      "frozen out: use the ContractState lens API "
                      "(readSlot/writeSlot/writeMap/... in Verity/Core.lean).")
            else:
                print(f"  {rel}: {count} sites but baseline says {allowed} — "
                      f"thanks for migrating! Update BASELINE in "
                      f"scripts/check_storage_lens_freeze.py to {count} "
                      f"(or remove the entry if 0).")
        return 1
    print("OK: storage-lens freeze holds "
          f"({sum(seen.values())} baselined raw sites across {len(seen)} files).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
