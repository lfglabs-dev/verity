#!/usr/bin/env python3
"""Storage-lens API freeze gate (C5 step 1).

The C5 storage-representation flip (one word-addressed `StorageKey -> Uint256` map
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
- `storageWords` is checked repo-wide. It is the canonical word backing
  field and may only be updated by the implementations in `Verity/Core.lean`.
- `storage :=` / `transientStorage :=` are checked under `Verity/` and
  `Contracts/`, and are additionally checked in `Compiler/` when the record
  receiver is statically declared as `ContractState`. Compiler has unrelated
  IR runtime records with the same field names, which this small type-aware
  filter deliberately leaves out rather than freezing a false-positive
  baseline.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

UNIQUE_CHANNELS = (
    "storageWords",
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
    # The sole canonical word-map implementation boundary. This includes the
    # single default-state literal plus the lens implementations (including
    # bulk lenses); no caller outside this file may update `storageWords`.
    "Verity/Core.lean": 21,
    # IRState fixture literals (field-name collision false positives).
    "Contracts/TypedIRTests.lean": 3,
}

RECORD_UPDATE_RE = re.compile(
    r"\{\s*([A-Za-z_][\w']*)\s+with\s+(?:«)?(storage|transientStorage)(?:»)?\s*:=",
    re.MULTILINE,
)
CONTRACT_STATE_BINDING_RE = re.compile(
    r"(?:\(|\{|,)\s*([A-Za-z_][\w']*)\s*:\s*(?:Verity\.)?ContractState\b"
)
CONTRACT_STATE_ASCRIPTION_RE = re.compile(
    r"\{\s*([A-Za-z_][\w']*)\s+with\s+(?:«)?(?:storage|transientStorage)(?:»)?\s*:=[\s\S]{0,400}?\}\s*:\s*(?:Verity\.)?ContractState\b"
)


def count_sites(path: Path) -> int:
    rel = path.relative_to(ROOT).as_posix()
    text = path.read_text(encoding="utf-8")
    # Strip line comments to avoid counting documentation.
    text = re.sub(r"--[^\n]*", "", text)
    count = len(UNIQUE_RE.findall(text))
    top = rel.split("/", 1)[0]
    if top in SHARED_SCAN_DIRS:
        count += len(SHARED_RE.findall(text))
    elif top == "Compiler":
        # `storage` and `transientStorage` are also fields of Compiler's IR
        # states. Count only record updates whose receiver is known to be a
        # source `ContractState`, plus explicitly ascribed ContractState
        # literals. This catches the source-world bypass without inventing a
        # baseline for every IR-state update in Compiler proofs.
        source_names = set(CONTRACT_STATE_BINDING_RE.findall(text))
        source_names.update(CONTRACT_STATE_ASCRIPTION_RE.findall(text))
        count += sum(
            receiver in source_names
            for receiver, _field in RECORD_UPDATE_RE.findall(text)
        )
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
