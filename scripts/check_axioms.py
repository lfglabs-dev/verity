#!/usr/bin/env python3
"""Validate AXIOMS.md sync and parse PrintAxioms output.

Usage:
    python3 scripts/check_axioms.py
    python3 scripts/check_axioms.py --log axiom-output.log
    lake env lean PrintAxioms.lean 2>&1 | python3 scripts/check_axioms.py --report
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

from property_utils import ROOT, die, report_errors, scrub_lean_code

_IDENT_SEG_RE = r"(?:«[^»]+»|[A-Za-z_][A-Za-z0-9_']*)"
_DOTTED_IDENT_RE = rf"{_IDENT_SEG_RE}(?:\.{_IDENT_SEG_RE})*"
AXIOM_KW_RE = re.compile(r"(?<![A-Za-z0-9_.'«»])axiom(?![A-Za-z0-9_.'«»])")
AXIOM_INLINE_DECL_RE = re.compile(
    rf"(?<![A-Za-z0-9_.'«»])axiom\s+(?P<name>{_DOTTED_IDENT_RE})"
)
AXIOM_SPLIT_NAME_RE = re.compile(rf"^\s*(?P<name>{_DOTTED_IDENT_RE})")
AUX_AXIOM_SUFFIX_RE = re.compile(
    r"(?:^|\.)_native\.(?:native_decide|bv_decide)\.ax(?:_[0-9]+)+$"
)
DEFAULT_AXIOM_ROOTS = ("Compiler", "Verity", "Contracts", "Benchmark")

LEAN_BUILTIN_AXIOMS = frozenset([
    "propext",
    "Quot.sound",
    "Classical.choice",
    "Lean.ofReduceBool",
    # native_decide implicitly trusts native codegen even when #print axioms only records
    # Lean.ofReduceBool for the current generated proof terms.
    "Lean.trustCompiler",
])

DOCUMENTED_AXIOMS = frozenset([
    "Compiler.Proofs.solidityMappingSlot_injective",
])

FORBIDDEN_AXIOMS = frozenset([
    "sorryAx",
])

NATIVE_DECIDE_AXIOM_RE = re.compile(
    r"^(?P<origin>.+)\._native\.native_decide\.ax(?:_[0-9]+)+$"
)
BV_DECIDE_AXIOM_RE = re.compile(
    r"^(?P<origin>.+)\._native\.bv_decide\.ax(?:_[0-9]+)+$"
)

# Lean 4.31 generates per-proof axiom names for these pre-Phase-0b native_decide
# theorems in the verified population (`bv_decide` has zero origins in the
# verified population). Keep origins explicit: accepting the suffix alone would
# let an unrelated dependency disguise an ordinary axiom as generated code.
# Phase 0b+1 eliminates these origins.
NATIVE_DECIDE_AXIOM_ORIGINS = frozenset([
    "Compiler.ERC20MinimalNativeWitness.lowerRuntimeContractNative_ok",
    "Compiler.ERC20MinimalNativeWitness.lowerRuntimeContractNative_eq",
    "Compiler.SimpleStorageNativeWitness.lowerRuntimeContractNative_ok",
    "Compiler.SimpleStorageNativeWitness.lowerRuntimeContractNative_eq",
    "Compiler.VaultMinimalNativeWitness.lowerRuntimeContractNative_ok",
    "Compiler.VaultMinimalNativeWitness.lowerRuntimeContractNative_eq",
    "Verity.Core.Free.witness_abiHeadParamShapes_compile",
    "Verity.Core.Uint16.ofUint256_toUint256",
    "Verity.keccak256_nat_empty",
    "Verity.keccak256_lit_empty_val",
])

BV_DECIDE_AXIOM_ORIGINS: frozenset[str] = frozenset()


def is_lean_builtin_axiom(name: str) -> bool:
    """Recognize Lean builtins, including 4.31's explicit per-proof auxiliary names."""
    if name in LEAN_BUILTIN_AXIOMS:
        return True
    match = NATIVE_DECIDE_AXIOM_RE.fullmatch(name)
    if match is not None:
        return match.group("origin") in NATIVE_DECIDE_AXIOM_ORIGINS
    bv_match = BV_DECIDE_AXIOM_RE.fullmatch(name)
    return bv_match is not None and bv_match.group("origin") in BV_DECIDE_AXIOM_ORIGINS


def parse_axiom_entries(axioms_md_text: str) -> list[tuple[str, str, int]]:
    """Extract ``(axiom_name, relative_path, claimed_line)`` entries from AXIOMS.md."""
    blocks = re.findall(
        r"### \d+\.\s+`([^`]+)`(?:[^\n]*)\n\n"
        r"\*\*Location\*\*:\s*`([^:]+):(\d+)`",
        axioms_md_text,
    )
    return [(name, rel_path, int(line)) for name, rel_path, line in blocks]


def parse_active_axiom_count(axioms_md_text: str) -> int | None:
    """Extract trust-summary active axiom count from AXIOMS.md, if present."""
    match = re.search(r"^- Active axioms:\s*(\d+)\s*$", axioms_md_text, flags=re.MULTILINE)
    if match is None:
        return None
    return int(match.group(1))


def _unquote_lean_ident(raw: str) -> str:
    return raw.replace("«", "").replace("»", "")


def _is_forbidden_aux_axiom_decl_name(name: str) -> bool:
    return (
        NATIVE_DECIDE_AXIOM_RE.fullmatch(name) is not None
        or BV_DECIDE_AXIOM_RE.fullmatch(name) is not None
        or AUX_AXIOM_SUFFIX_RE.search(name) is not None
    )


def scan_lean_file_axioms(text: str, rel_path: str) -> list[tuple[str, int]]:
    """Extract ``(unquoted_name, decl_line_1based)`` for every ``axiom`` in *text*.

    Handles indented declarations inside ``section``/``namespace`` blocks, arbitrary
    prefixes (``@[simp]``, ``noncomputable``, ``set_option ... in``, ``private``/``protected``),
    guillemet-escaped identifiers (``«...»``), and split-line ``axiom\\n  name`` forms.
    Fails closed via ``die`` if a standalone ``axiom`` keyword cannot be paired with a
    valid declaration name.
    """
    scrubbed_lines = scrub_lean_code(text).splitlines()
    results: list[tuple[str, int]] = []
    i = 0
    while i < len(scrubbed_lines):
        line = scrubbed_lines[i]
        kw_matches = list(AXIOM_KW_RE.finditer(line))
        if not kw_matches:
            i += 1
            continue
        for kw in kw_matches:
            tail = line[kw.start() :]
            inline = AXIOM_INLINE_DECL_RE.match(tail)
            if inline is not None:
                results.append((_unquote_lean_ident(inline.group("name")), i + 1))
                continue
            if line[kw.end() :].strip():
                die(f"Malformed axiom declaration at {rel_path}:{i + 1}")
            j = i + 1
            while j < len(scrubbed_lines) and not scrubbed_lines[j].strip():
                j += 1
            if j >= len(scrubbed_lines):
                die(f"Incomplete axiom declaration at {rel_path}:{i + 1}")
            split = AXIOM_SPLIT_NAME_RE.match(scrubbed_lines[j])
            if split is None:
                die(f"Malformed split-line axiom declaration at {rel_path}:{i + 1}")
            results.append((_unquote_lean_ident(split.group("name")), i + 1))
        i += 1
    return results


def discover_repo_axioms(roots: tuple[str, ...] = DEFAULT_AXIOM_ROOTS) -> dict[str, tuple[str, int]]:
    """Return all Lean axiom declarations as ``{name: (relative_path, line)}``."""
    discovered: dict[str, tuple[str, int]] = {}
    for subdir in roots:
        base_dir = ROOT / subdir
        if not base_dir.exists():
            continue
        for lean_file in sorted(base_dir.rglob("*.lean")):
            raw_text = lean_file.read_text(encoding="utf-8")
            rel_path = str(lean_file.relative_to(ROOT))
            for name, line_no in scan_lean_file_axioms(raw_text, rel_path):
                if _is_forbidden_aux_axiom_decl_name(name):
                    die(
                        f"Forbidden hand-written native_decide/bv_decide auxiliary axiom "
                        f"declaration {name!r} at {rel_path}:{line_no}"
                    )
                if name in discovered:
                    old_path, old_line = discovered[name]
                    die(
                        f"Duplicate axiom name {name!r}: "
                        f"{old_path}:{old_line} and {rel_path}:{line_no}"
                    )
                discovered[name] = (rel_path, line_no)
    return discovered


def run_location_check() -> int:
    axioms_md = ROOT / "docs" / "AXIOMS.md"
    if not axioms_md.exists():
        die("docs/AXIOMS.md not found")

    text = axioms_md.read_text(encoding="utf-8")
    axiom_blocks = parse_axiom_entries(text)
    # Zero axioms is valid — the project targets zero project-level axioms

    discovered_axioms = discover_repo_axioms()
    documented_names = {name for name, _, _ in axiom_blocks}
    discovered_names = set(discovered_axioms)

    errors: list[str] = []
    checked = 0

    for axiom_name, rel_path, claimed_line in axiom_blocks:
        source_file = ROOT / rel_path
        if not source_file.exists():
            errors.append(f"{axiom_name}: file {rel_path} not found")
            continue

        file_axioms = dict(scan_lean_file_axioms(source_file.read_text(encoding="utf-8"), rel_path))
        actual_line = file_axioms.get(axiom_name)

        if actual_line is None:
            errors.append(
                f"{axiom_name}: not found in {rel_path} "
                f"(AXIOMS.md claims line {claimed_line})"
            )
        elif actual_line != claimed_line:
            errors.append(
                f"{axiom_name}: AXIOMS.md says line {claimed_line} "
                f"but actually at line {actual_line} in {rel_path}"
            )
        else:
            print(f"  OK {axiom_name} at {rel_path}:{actual_line}")
            checked += 1

    missing_from_docs = sorted(discovered_names - documented_names)
    for axiom_name in missing_from_docs:
        rel_path, line = discovered_axioms[axiom_name]
        errors.append(
            f"{axiom_name}: declared in {rel_path}:{line} but missing from AXIOMS.md"
        )

    stale_doc_entries = sorted(documented_names - discovered_names)
    for axiom_name in stale_doc_entries:
        errors.append(f"{axiom_name}: listed in AXIOMS.md but no Lean axiom declaration exists")

    active_count = parse_active_axiom_count(text)
    if active_count is None:
        errors.append("AXIOMS.md: missing '- Active axioms: N' trust summary line")
    elif active_count != len(discovered_axioms):
        errors.append(
            f"AXIOMS.md trust summary says Active axioms: {active_count}, "
            f"but source has {len(discovered_axioms)}"
        )

    report_errors(errors, "Axiom location check failed")
    print(
        f"\nOK: {checked} documented axiom locations are accurate; "
        f"registry is complete and synchronized with {len(discovered_axioms)} source axioms"
    )
    return 0


def parse_axiom_output(text: str) -> dict[str, list[str]]:
    """Parse Lean ``#print axioms`` output into ``{theorem_name: [axioms]}``."""
    results: dict[str, list[str]] = {}

    for line in text.splitlines():
        line = line.strip()
        match = re.match(r"'(.+)' depends on axioms: \[(.+)\]", line)
        if match:
            name = match.group(1)
            axioms = [axiom.strip() for axiom in match.group(2).split(",")]
            results[name] = axioms
            continue

        match = re.match(r"'(.+)' does not depend on any axioms", line)
        if match:
            results[match.group(1)] = []

    return results


def classify_axioms(
    axiom_map: dict[str, list[str]],
) -> tuple[set[str], set[str], set[str], dict[str, list[str]]]:
    """Classify axioms into builtin, documented, forbidden, and unexpected.

    For Lean 4.31 generated per-proof auxiliary axioms (`<origin>._native.<kind>.ax_*`),
    if `<origin>` itself is present in ``axiom_map`` and does NOT list that auxiliary
    axiom among its own dependencies, the auxiliary axiom cannot have been emitted by
    `<origin>`'s proof and is rejected as unexpected (spoof protection).
    """
    all_axioms: set[str] = set()
    for axioms in axiom_map.values():
        all_axioms.update(axioms)

    spoofed_aux: set[str] = set()
    for axiom in all_axioms:
        match = NATIVE_DECIDE_AXIOM_RE.fullmatch(axiom) or BV_DECIDE_AXIOM_RE.fullmatch(axiom)
        if match is not None:
            origin = match.group("origin")
            if origin in axiom_map and axiom not in axiom_map[origin]:
                spoofed_aux.add(axiom)

    builtin = {
        axiom
        for axiom in all_axioms
        if axiom not in spoofed_aux and is_lean_builtin_axiom(axiom)
    }
    documented = all_axioms & DOCUMENTED_AXIOMS
    forbidden = all_axioms & FORBIDDEN_AXIOMS
    unexpected = all_axioms - builtin - documented - forbidden

    unexpected_usage: dict[str, list[str]] = {}
    for axiom in unexpected:
        unexpected_usage[axiom] = [
            theorem for theorem, axioms in axiom_map.items() if axiom in axioms
        ]

    return builtin, documented, forbidden, unexpected_usage


def generate_report(
    axiom_map: dict[str, list[str]],
    builtin: set[str],
    documented: set[str],
    forbidden: set[str],
    unexpected_usage: dict[str, list[str]],
) -> str:
    """Generate a human-readable axiom dependency report."""
    lines = ["# Axiom Dependency Report", ""]

    total = len(axiom_map)
    axiom_free = sum(1 for axioms in axiom_map.values() if not axioms)
    builtin_only = sum(
        1
        for axioms in axiom_map.values()
        if axioms and all(is_lean_builtin_axiom(axiom) for axiom in axioms)
    )
    uses_documented = sum(
        1 for axioms in axiom_map.values() if any(axiom in DOCUMENTED_AXIOMS for axiom in axioms)
    )

    lines.append(f"Total theorems checked: {total}")
    lines.append(f"Axiom-free (pure logic): {axiom_free}")
    lines.append(
        "Uses only Lean builtins "
        "(propext, Quot.sound, Classical.choice, Lean.ofReduceBool, "
        "Lean 4.31 generated per-proof native_decide axioms, Lean.trustCompiler): "
        f"{builtin_only}"
    )
    lines.append(f"Uses documented project axioms: {uses_documented}")
    lines.append("")

    lines.append("## Lean Builtin Axioms Used")
    for axiom in sorted(builtin - FORBIDDEN_AXIOMS):
        lines.append(f"  - {axiom}")
    lines.append("")

    lines.append("## Documented Project Axioms")
    for axiom in sorted(documented):
        users = [theorem for theorem, axioms in axiom_map.items() if axiom in axioms]
        lines.append(f"  - {axiom} (used by {len(users)} theorems)")
    lines.append("")

    if forbidden:
        lines.append("## FORBIDDEN AXIOMS DETECTED")
        for axiom in sorted(forbidden):
            users = [theorem for theorem, axioms in axiom_map.items() if axiom in axioms]
            lines.append(f"  - {axiom} (used by {len(users)} theorems)")
            for theorem in users[:10]:
                lines.append(f"      {theorem}")
        lines.append("")

    if unexpected_usage:
        lines.append("## UNEXPECTED AXIOMS DETECTED")
        for axiom, users in sorted(unexpected_usage.items()):
            lines.append(f"  - {axiom} (used by {len(users)} theorems)")
            for theorem in users[:10]:
                lines.append(f"      {theorem}")
        lines.append("")

    if not forbidden and not unexpected_usage:
        lines.append("## Result: PASS")
        lines.append("All theorems depend only on Lean builtins and documented project axioms.")
    else:
        lines.append("## Result: FAIL")
        lines.append("Unexpected or forbidden axioms detected.")

    return "\n".join(lines) + "\n"


def run_report_check(text: str) -> int:
    # Enforce source-level ban on hand-written `._native.(native_decide|bv_decide).ax_*`
    # declarations even when running in `--report`/`--log` mode.
    discover_repo_axioms()
    axiom_map = parse_axiom_output(text)
    if not axiom_map:
        print("WARNING: No #print axioms output found. Is the input empty?", file=sys.stderr)
        print("Parsed 0 theorems from input.", file=sys.stderr)
        return 1

    builtin, documented, forbidden, unexpected_usage = classify_axioms(axiom_map)
    report = generate_report(axiom_map, builtin, documented, forbidden, unexpected_usage)
    print(report)

    output_file = os.environ.get("AXIOM_REPORT_FILE")
    if output_file:
        Path(output_file).write_text(report, encoding="utf-8")
        print(f"Report written to {output_file}", file=sys.stderr)

    if forbidden or unexpected_usage:
        return 1
    return 0


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--locations", action="store_true", help="run AXIOMS.md location validation")
    mode.add_argument("--report", action="store_true", help="parse #print axioms output from stdin or --log")
    parser.add_argument("--log", type=Path, help="path to a PrintAxioms output log")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    if args.report or args.log is not None:
        if args.log is not None:
            text = args.log.read_text(encoding="utf-8")
        else:
            text = sys.stdin.read()
        return run_report_check(text)

    return run_location_check()


if __name__ == "__main__":
    raise SystemExit(main())
