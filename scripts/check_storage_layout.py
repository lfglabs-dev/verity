#!/usr/bin/env python3
"""Validate storage layout consistency between the EDSL and Spec layers.

Extracts storage slot definitions from:
1. EDSL layer: Contracts/*/<Contract>.lean  (StorageSlot or macro storage definitions)
2. Spec layer: Contracts/*/Spec.lean        (literal storage slot accesses)

Checks:
- No intra-contract slot collisions within either layer
- Spec slot/type usage matches the EDSL for every contract with both layers
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT, strip_lean_comments

# Regex for EDSL/Spec StorageSlot definitions:
#   def <name> : StorageSlot <type> := ⟨<slot>⟩
STORAGE_SLOT_RE = re.compile(
    r"def\s+(\w+)\s*:\s*StorageSlot\s+(.+?)\s*:=\s*⟨(\d+)⟩"
)

MACRO_STORAGE_LINE_RE = re.compile(
    r"^\s*(\w+)\s*:\s*(.+?)\s*:=\s*slot\s+(\d+)\s*$", re.MULTILINE
)

# Regex for Lean namespace:
#   namespace <name>
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)", re.MULTILINE)

# Spec slot references in Contracts/*/Spec.lean:
#   s.storage <slot>, s'.storage <slot>
#   s.storageAddr <slot>, s'.storageAddr <slot>
#   s.storageMap <slot> <addr>, s'.storageMap <slot> <addr>
SPEC_UINT_SLOT_RE = re.compile(r"\bs'?\.(?:storage)\s+(\d+)\b")
SPEC_ADDR_SLOT_RE = re.compile(r"\bs'?\.(?:storageAddr)\s+(\d+)\b")
SPEC_MAPPING_SLOT_RE = re.compile(r"\bs'?\.(?:storageMap)\s+(\d+)\b")
SPEC_MAPPING_UINT_SLOT_RE = re.compile(r"\bs'?\.(?:storageMapUint)\s+(\d+)\b")
SPEC_MAPPING2_SLOT_RE = re.compile(r"\bs'?\.(?:storageMap2)\s+(\d+)\b")
SPEC_HELPER_SLOT_PATTERNS: tuple[tuple[re.Pattern[str], tuple[str, ...]], ...] = (
    (re.compile(r"\bstorageUpdateSpec\s+(\d+)\b"), ("uint256",)),
    (re.compile(r"\bstorageAddrUpdateSpec\s+(\d+)\b"), ("address",)),
    (re.compile(r"\bstorageAddrStorageUpdateSpec\s+(\d+)\s+(\d+)\b"), ("address", "uint256")),
    (re.compile(r"\bstorageAddrStorage2UpdateSpec\s+(\d+)\s+(\d+)\s+(\d+)\b"), ("address", "uint256", "uint256")),
    (re.compile(r"\bstorage2UpdateSpec\s+(\d+)\s+(\d+)\b"), ("uint256", "uint256")),
    (re.compile(r"\bstorageMapUpdateSpec\s+(\d+)\b"), ("mapping",)),
    (re.compile(r"\bstorageMapAndStorageUpdateSpec\s+(\d+)\s+\w+\s+\w+\s+(\d+)\b"), ("mapping", "uint256")),
    (re.compile(r"\bstorageMap2UpdateSpec\s+(\d+)\b"), ("mapping2",)),
)


def extract_macro_contract_slots(contract_name: str) -> list[tuple[str, str, int]]:
    """Extract storage field declarations from a `Contracts/<Name>/<Name>.lean` file."""
    path = ROOT / "Contracts" / contract_name / f"{contract_name}.lean"
    if not path.exists():
        return []

    content = strip_lean_comments(path.read_text())
    storage_match = re.search(r"\bstorage\b", content)
    if not storage_match:
        return []

    end_markers = [
        pos
        for pos in (
            content.find("\n  constructor", storage_match.end()),
            content.find("\n  function", storage_match.end()),
            content.find("\nend ", storage_match.end()),
        )
        if pos != -1
    ]
    storage_end = min(end_markers) if end_markers else len(content)
    storage_block = content[storage_match.end() : storage_end]

    fields: list[tuple[str, str, int]] = []
    for m in MACRO_STORAGE_LINE_RE.finditer(storage_block):
        field_name, field_type, slot_num = m.group(1), m.group(2).strip(), int(m.group(3))
        fields.append((field_name, field_type, slot_num))
    return fields


def extract_edsl_slots(filepath: Path) -> dict[str, list[tuple[str, str, int]]]:
    """Extract StorageSlot definitions from a Lean file.

    Returns dict mapping namespace/contract to list of (name, type, slot_number).
    """
    content = strip_lean_comments(filepath.read_text())
    namespace = filepath.parent.name if filepath.parent.name != "Contracts" else filepath.stem
    for m in NAMESPACE_RE.finditer(content):
        ns = m.group(1).split(".")[-1]
        if ns != "Contracts":
            namespace = ns

    slots = []
    for m in STORAGE_SLOT_RE.finditer(content):
        name, ty, slot_num = m.group(1), m.group(2).strip(), int(m.group(3))
        slots.append((name, ty, slot_num))

    if slots:
        return {namespace: slots}
    macro_slots = extract_macro_contract_slots(namespace)
    if macro_slots:
        return {
            namespace: [
                (normalize_field_name(name), ty, slot_num)
                for name, ty, slot_num in macro_slots
            ]
        }
    return {}


def extract_spec_slots(
    filepath: Path,
) -> tuple[list[tuple[str, str, int]], list[str]]:
    """Extract literal slot/type usage from a Spec.lean file.

    Returns:
      - list of (name, type, slot_number) where name is synthetic "slot<N>"
      - list of consistency errors found inside the spec file itself
    """
    content = strip_lean_comments(filepath.read_text())
    contract = filepath.parent.name

    by_slot: dict[int, set[str]] = {}
    for m in SPEC_UINT_SLOT_RE.finditer(content):
        by_slot.setdefault(int(m.group(1)), set()).add("uint256")
    for m in SPEC_ADDR_SLOT_RE.finditer(content):
        by_slot.setdefault(int(m.group(1)), set()).add("address")
    for m in SPEC_MAPPING_SLOT_RE.finditer(content):
        by_slot.setdefault(int(m.group(1)), set()).add("mapping")
    for m in SPEC_MAPPING_UINT_SLOT_RE.finditer(content):
        by_slot.setdefault(int(m.group(1)), set()).add("mapping_uint")
    for m in SPEC_MAPPING2_SLOT_RE.finditer(content):
        by_slot.setdefault(int(m.group(1)), set()).add("mapping2")
    for pattern, kinds in SPEC_HELPER_SLOT_PATTERNS:
        for m in pattern.finditer(content):
            for group_index, kind in enumerate(kinds, start=1):
                by_slot.setdefault(int(m.group(group_index)), set()).add(kind)

    entries: list[tuple[str, str, int]] = []
    errors: list[str] = []
    for slot in sorted(by_slot.keys()):
        kinds = by_slot[slot]
        if len(kinds) > 1:
            errors.append(
                f"[Spec] {contract}: slot {slot} used with multiple kinds: {sorted(kinds)}"
            )
        kind = sorted(kinds)[0]
        entries.append((f"slot{slot}", kind, slot))
    return entries, errors


def normalize_type(ty: str) -> str:
    """Normalize type names for comparison across layers."""
    raw = ty.strip()
    # Strip balanced outer parentheses for EDSL types like "(Address → Uint256)"
    stripped = raw
    if stripped.startswith("(") and stripped.endswith(")"):
        stripped = stripped[1:-1].strip()
    mapping = {
        # EDSL types (from StorageSlot definitions)
        "Uint256": "uint256",
        "Address": "address",
        "Address → Uint256": "mapping",
        "Uint256 → Uint256": "mapping_uint",
        "Address → Address → Uint256": "mapping2",
        # Compiler types (from FieldType variants)
        "mapping": "mapping",
        "mappingTyped (.simple .address)": "mapping",
        "mappingTyped (.simple .uint256)": "mapping_uint",
        "mappingTyped (.nested .address .address)": "mapping2",
        "mappingTyped (.nested .address .uint256)": "mapping2",
        "mappingTyped (.nested .uint256 .address)": "mapping2",
        "mappingTyped (.nested .uint256 .uint256)": "mapping2",
    }
    # Try raw first (for Compiler types like "mappingTyped (...)"), then stripped
    return mapping.get(raw, mapping.get(stripped, stripped.lower()))


def normalize_field_name(name: str) -> str:
    """Normalize storage field names across legacy and macro-generated surfaces."""
    return name[:-4] if name.endswith("Slot") else name


def check_intra_collisions(
    contract: str, slots: list[tuple[str, str, int]], layer: str
) -> list[str]:
    """Check for slot number collisions within a single contract."""
    errors = []
    slot_map: dict[int, str] = {}
    for name, _ty, slot_num in slots:
        if slot_num in slot_map:
            errors.append(
                f"[{layer}] {contract}: Slot {slot_num} collision between "
                f"'{slot_map[slot_num]}' and '{name}'"
            )
        else:
            slot_map[slot_num] = name
    return errors


def check_spec_edsl_consistency(
    edsl: dict[str, list[tuple[str, str, int]]],
    spec: dict[str, list[tuple[str, str, int]]],
) -> list[str]:
    """Check Spec slot/type usage matches the EDSL for contracts with both layers.

    Smoke contracts (`*Smoke`) exercise macro features and are exempt.
    """
    errors: list[str] = []

    for contract in sorted(set(edsl) & set(spec)):
        if contract.endswith("Smoke"):
            continue
        edsl_slots = {(slot, normalize_type(ty)) for _name, ty, slot in edsl[contract]}
        spec_slots = {(slot, normalize_type(ty)) for _name, ty, slot in spec[contract]}

        for slot, ty in sorted(spec_slots):
            if (slot, ty) not in edsl_slots:
                errors.append(
                    f"Spec-EDSL: {contract}.slot{slot} ({ty}) in Spec but not in EDSL"
                )
        for slot, ty in sorted(edsl_slots):
            if (slot, ty) not in spec_slots:
                errors.append(
                    f"Spec-EDSL: {contract}.slot{slot} ({ty}) in EDSL but not in Spec"
                )
    return errors


def generate_report(edsl: dict[str, list[tuple[str, str, int]]], fmt: str = "text") -> str:
    """Generate a storage layout report."""
    lines = []

    if fmt == "markdown":
        lines.append("## Storage Layout Report")
        lines.append("")
        for contract in sorted(edsl):
            lines.append(f"### {contract}")
            lines.append("")
            lines.append("| Slot | Field | Type |")
            lines.append("|------|-------|------|")
            for name, ty, slot in sorted(edsl[contract], key=lambda x: x[2]):
                lines.append(f"| {slot} | `{name}` | `{ty}` |")
            lines.append("")
    else:
        lines.append("=" * 60)
        lines.append("STORAGE LAYOUT REPORT")
        lines.append("=" * 60)
        for contract in sorted(edsl):
            lines.append("")
            lines.append(f"  {contract}")
            for name, ty, slot in sorted(edsl[contract], key=lambda x: x[2]):
                lines.append(f"    Slot {slot}: {name} ({ty})")
    return "\n".join(lines)


def main():
    errors: list[str] = []

    # 1. Extract EDSL slots from Contracts (use directory name as contract name)
    edsl_all: dict[str, list[tuple[str, str, int]]] = {}
    contracts_dir = ROOT / "Contracts"
    for contract_dir in sorted(contracts_dir.iterdir()):
        if not contract_dir.is_dir():
            continue
        lean_file = contract_dir / f"{contract_dir.name}.lean"
        if not lean_file.exists():
            continue
        result = extract_edsl_slots(lean_file)
        # Use directory name as contract name
        for _key, slots in result.items():
            if slots:
                edsl_all[contract_dir.name] = slots

    # 2. Extract Spec slots from literal state accesses in Spec.lean files
    spec_all: dict[str, list[tuple[str, str, int]]] = {}
    for contract_dir in sorted(contracts_dir.iterdir()):
        if not contract_dir.is_dir():
            continue
        spec_file = contract_dir / "Spec.lean"
        if not spec_file.exists():
            continue
        contract_name = contract_dir.name
        slots, spec_errors = extract_spec_slots(spec_file)
        errors.extend(spec_errors)
        if slots:
            spec_all[contract_name] = slots

    # 3. Check intra-contract collisions
    for contract, slots in edsl_all.items():
        errors.extend(check_intra_collisions(contract, slots, "EDSL"))
    for contract, slots in spec_all.items():
        errors.extend(check_intra_collisions(contract, slots, "Spec"))

    # 4. Check Spec-EDSL consistency
    errors.extend(check_spec_edsl_consistency(edsl_all, spec_all))

    # 5. Report
    fmt = "markdown" if "--format=markdown" in sys.argv else "text"

    if errors:
        print("Storage layout validation FAILED.\n")
        for e in errors:
            print(f"  ERROR: {e}")
        print()
        sys.exit(1)

    print("Storage layout validation passed.\n")
    print(generate_report(edsl_all, fmt))


if __name__ == "__main__":
    main()
