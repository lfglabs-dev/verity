#!/usr/bin/env python3
"""Named-storage gate for human-facing specs.

A spec should say `v.totalAssets`, not `s.readSlot 0`: a wrong slot number
silently points the promise at another variable, and the reader has to trust a
comment to know what the number means. Opted-in spec files therefore must not
touch `ContractState` directly at all: no raw accessor (`readSlot`, `readMap`,
`readMapUint`, `readTransient`, ...), no raw storage field, no `ContractState`
mention, no positional projection, and no Verity ghost `knownAddresses`
bookkeeping. Names come from a generated storage view (see
`Contracts/VaultFromSolidity/Importer/Importer.lean`); `Storage` is a
kernel-checked structure whose `view` reads through `<var>Slot` handles, so
the gate rejects the accessor names wherever they appear rather than trying
to spot a numeric slot argument after them.

The raw accessor list is read from `Verity/Core.lean` (every definition in the
`ContractState` namespace plus the storage-backing fields), so a new accessor
is covered without editing this file.

The gate is opt-in per file: handwritten contracts still state specs over raw
slots and are not listed yet.

Usage:
    python3 scripts/check_spec_named_storage.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT, scrub_lean_code

SPEC_FILES = (
    "Contracts/VaultFromSolidity/Spec.lean",
    "Contracts/SolidityImportSmoke/Inheritance/Spec.lean",
)

CORE_LEAN = "Verity/Core.lean"

# Fields of `ContractState` that back storage or its ghost bookkeeping.
STORAGE_FIELDS = ("storageWords", "storageArray", "knownAddresses")

# Ways to take a `Storage`/`ContractState` value apart without naming a field.
STRUCTURE_ESCAPES = ("mk", "rec", "recOn", "casesOn", "noConfusion")

_DEF_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:def|abbrev|theorem|instance)\s+([A-Za-z_][\w'?!]*)",
    re.M,
)


def raw_accessors(core_text: str) -> frozenset[str]:
    """Every name defined inside `namespace ContractState` in `core_text`."""
    names: set[str] = set()
    depth = 0
    for line in scrub_lean_code(core_text).splitlines():
        stripped = line.strip()
        if stripped == "namespace ContractState":
            depth += 1
            continue
        if stripped == "end ContractState":
            depth = max(depth - 1, 0)
            continue
        if depth and (match := _DEF_RE.match(line)):
            names.add(match.group(1))
    return frozenset(names)


RAW_ACCESSORS = raw_accessors((ROOT / CORE_LEAN).read_text(encoding="utf-8"))


def _identifier_re(names: tuple[str, ...] | frozenset[str]) -> re.Pattern[str]:
    alternatives = "|".join(re.escape(name) for name in sorted(names))
    return re.compile(r"(?<![\w'])(?:" + alternatives + r")(?![\w'?!])")


ACCESSOR_RE = _identifier_re(RAW_ACCESSORS)
FIELD_RE = _identifier_re(STORAGE_FIELDS)
CONTRACT_STATE_RE = re.compile(r"(?<![\w'])ContractState(?![\w'])")
STRUCTURE_ESCAPE_RE = re.compile(
    r"(?<![\w'])(?:Storage|ContractState)\.(?:" + "|".join(STRUCTURE_ESCAPES) + r")(?![\w'])"
)
# `v.1`, `(view s).2`: positional projections out of the storage view.
PROJECTION_RE = re.compile(r"(?<=[A-Za-z_')\]])\.\d+")


def find_violations(text: str) -> list[tuple[int, str]]:
    """Return `(line, message)` for every raw storage reference in Lean `text`."""
    violations: list[tuple[int, str]] = []
    for line_no, line in enumerate(scrub_lean_code(text).splitlines(), 1):
        for match in ACCESSOR_RE.finditer(line):
            violations.append((line_no, f"raw `ContractState` accessor `{match.group(0)}`"))
        for match in FIELD_RE.finditer(line):
            if match.group(0) == "knownAddresses":
                violations.append((line_no, "`knownAddresses` ghost bookkeeping"))
            else:
                violations.append((line_no, f"raw storage field `{match.group(0)}`"))
        if CONTRACT_STATE_RE.search(line):
            violations.append((line_no, "`ContractState` named directly"))
        for match in STRUCTURE_ESCAPE_RE.finditer(line):
            violations.append((line_no, f"structure eliminator `{match.group(0)}`"))
        for match in PROJECTION_RE.finditer(line):
            violations.append((line_no, f"positional projection `{match.group(0)}`"))
    return violations


def main() -> int:
    errors: list[str] = []
    if not RAW_ACCESSORS:
        errors.append(f"{CORE_LEAN}: found no definitions in `namespace ContractState`")
    for rel in SPEC_FILES:
        path = ROOT / rel
        if not path.is_file():
            errors.append(f"{rel}: opted-in spec file is missing")
            continue
        for line_no, message in find_violations(path.read_text(encoding="utf-8")):
            errors.append(f"{rel}:{line_no}: {message}; use the named storage view instead")
    if errors:
        print("Spec named-storage check failed:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1
    print(f"Spec named-storage check passed ({len(SPEC_FILES)} opted-in spec files).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
