#!/usr/bin/env python3
"""Check for Lean code hygiene issues.

Validates:
1. No debug commands (#eval, #check, #print, #reduce) in proof files
2. Exactly 0 allowUnsafeReducibility (legacy trust assumption removed)
3. Zero sorry in Lean code after scrubbing comments/strings
4. No native_decide in proof files outside smoke tests (kernel bypass)

Usage:
    python3 scripts/check_lean_hygiene.py
"""

from __future__ import annotations

import argparse
from collections.abc import Iterable, Sequence
from pathlib import Path
import re

from property_utils import ROOT, report_errors, scrub_lean_code

SORRY_RE = re.compile(r"\bsorry\b")
# Optional declaration modifiers that may precede ``theorem``/``lemma`` or
# declaration-boundary keywords (``def``, ``instance``, ...).  Any combination
# and order of these modifiers is accepted.
_MODIFIER_RE = r"(?:(?:private|protected|noncomputable|unsafe|partial|local|@\[[^\]]*\])\s+)*"
THEOREM_RE = re.compile(
    rf"^{_MODIFIER_RE}(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.']*)(?![A-Za-z0-9_.'])"
)
# Declaration-boundary keywords that start a new scope.  If the backward
# scan from a sorry hits one of these before finding a theorem/lemma,
# the sorry is outside any allowlisted declaration (e.g. in an example
# block) and should not be attributed to the prior theorem.
# Only *unindented* declarations count as boundaries; indented ones are
# local helpers inside a ``where`` clause and do not end the enclosing
# theorem scope.  The optional modifier prefix matches forms like
# ``noncomputable def``, ``protected def``, ``unsafe def``, etc.
BOUNDARY_RE = re.compile(
    rf"^{_MODIFIER_RE}(?:def|example|instance|abbrev|opaque|structure|class|inductive|section|namespace|end)\b"
    r"|^#"
)


def _find_enclosing_theorem(lines: list[str], sorry_idx: int) -> str | None:
    """Scan backwards from *sorry_idx* to find the enclosing theorem name.

    Stops at declaration boundaries (``example``, ``instance``, ``#``-commands,
    etc.) so that a ``sorry`` in a later block is not misattributed to a prior
    pinned theorem.
    """
    for j in range(sorry_idx, -1, -1):
        m = THEOREM_RE.match(lines[j])
        if m:
            return m.group(1)
        if BOUNDARY_RE.match(lines[j]):
            return None
    return None


def line_starts_with_command(line: str, cmd: str) -> bool:
    stripped = line.lstrip()
    return stripped == cmd or stripped.startswith(cmd + " ")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Check for Lean code hygiene issues.")
    parser.add_argument(
        "--forbid-constructor-compat",
        action="store_true",
        default=False,
        help="Forbid constructorCompat wrapper antipattern in contract proof files.",
    )
    args, _ = parser.parse_known_args(argv)
    return args


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    errors: list[str] = []

    # Check 1: No debug commands in proof files
    debug_commands = ["#eval", "#check", "#print", "#reduce"]
    proof_dirs = [ROOT / "Compiler" / "Proofs", ROOT / "Verity" / "Proofs", ROOT / "Contracts"]
    for proof_dir in proof_dirs:
        for lean_file in proof_dir.rglob("*.lean"):
            rel = lean_file.relative_to(ROOT)
            scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
            for i, line in enumerate(scrubbed_lines, 1):
                for cmd in debug_commands:
                    if line_starts_with_command(line, cmd):
                        errors.append(
                            f"{rel}:{i}: found {cmd} in proof file "
                            f"(debug command that slows builds)"
                        )

    # Check 2: Exactly 0 allowUnsafeReducibility (the prior single usage was
    # tied to the removed fuel-based executor after the EVMYulLean
    # transition).
    expected_unsafe = 0
    unsafe_count = 0
    unsafe_locations: list[str] = []
    for lean_file in ROOT.rglob("*.lean"):
        if ".lake" in str(lean_file):
            continue
        rel = lean_file.relative_to(ROOT)
        scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
        for i, line in enumerate(scrubbed_lines, 1):
            if "allowUnsafeReducibility" in line:
                unsafe_count += 1
                unsafe_locations.append(f"{rel}:{i}")

    if unsafe_count != expected_unsafe:
        errors.append(
            f"Expected {expected_unsafe} allowUnsafeReducibility, "
            f"found {unsafe_count}: {unsafe_locations}"
        )

    # Check 3: Fixed sorry baseline after the merged proof-reduction pass.
    # The bridge proof stack is now expected to be sorry-free; keep the
    # allowlist structure so future temporary carve-outs must be explicit.
    ALLOWED_SORRY_THEOREMS: dict[str, dict[str, int]] = {
    }
    sorry_count = 0
    sorry_locations: list[str] = []
    unexpected_sorry_locations: list[str] = []
    sorry_per_file: dict[str, int] = {}
    sorry_counts_per_theorem: dict[str, dict[str, int]] = {}
    for lean_file in ROOT.rglob("*.lean"):
        if ".lake" in str(lean_file):
            continue
        rel = lean_file.relative_to(ROOT)
        rel_str = str(rel)
        scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
        for i, line in enumerate(scrubbed_lines, 1):
            matches = list(SORRY_RE.finditer(line))
            for match in matches:
                sorry_count += 1
                loc = f"{rel}:{i}:{match.start() + 1}"
                sorry_locations.append(loc)
                if rel_str not in ALLOWED_SORRY_THEOREMS:
                    unexpected_sorry_locations.append(loc)
                    continue

                sorry_per_file[rel_str] = sorry_per_file.get(rel_str, 0) + 1
                thm = _find_enclosing_theorem(scrubbed_lines, i - 1)
                if thm:
                    theorem_counts = sorry_counts_per_theorem.setdefault(rel_str, {})
                    theorem_counts[thm] = theorem_counts.get(thm, 0) + 1
                else:
                    # sorry not inside any theorem/lemma/def — flag it
                    unexpected_sorry_locations.append(loc)

    if unexpected_sorry_locations:
        errors.append(
            f"Found sorry in non-allowlisted files: {unexpected_sorry_locations}"
        )

    for path, allowed_thm_counts in ALLOWED_SORRY_THEOREMS.items():
        actual = sorry_per_file.get(path, 0)
        allowed_total = sum(allowed_thm_counts.values())
        if actual > allowed_total:
            errors.append(
                f"{path}: found {actual} sorry (cap is {allowed_total})"
            )
        actual_thm_counts = sorry_counts_per_theorem.get(path, {})
        unexpected_thms = set(actual_thm_counts) - set(allowed_thm_counts)
        if unexpected_thms:
            errors.append(
                f"{path}: sorry in non-pinned theorems: "
                f"{sorted(unexpected_thms)} "
                f"(allowed: {sorted(allowed_thm_counts)})"
            )
        over_limit_thms = {
            theorem: count
            for theorem, count in actual_thm_counts.items()
            if count > allowed_thm_counts.get(theorem, 0)
        }
        if over_limit_thms:
            errors.append(
                f"{path}: sorry count exceeds pinned limit: "
                f"{sorted(over_limit_thms.items())} "
                f"(allowed: {sorted(allowed_thm_counts.items())})"
            )

    # Check 4: No native_decide in proof files (except tests/profiles)
    # native_decide bypasses the kernel and is acceptable in:
    #   - Smoke tests (string comparisons against generated code)
    #   - Feature/bridge tests (decidable equality checks across systems)
    #   - Arithmetic profiles (cross-system constant agreement)
    # It is NOT acceptable in mathematical preservation/correctness proofs.
    native_decide_count = 0
    for proof_dir in proof_dirs:
        for lean_file in proof_dir.rglob("*.lean"):
            rel = lean_file.relative_to(ROOT)
            stem = lean_file.stem
            if "Test" in stem or "Profile" in stem or "Smoke" in stem or "Smoke" in rel.parts:
                continue
            scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
            for i, line in enumerate(scrubbed_lines, 1):
                if "native_decide" in line:
                    native_decide_count += 1
                    errors.append(
                        f"{rel}:{i}: found native_decide in proof file "
                        f"(bypasses kernel — use decide or other tactics)"
                    )

    # Check 5: No new *Compat wrapper definitions in Contracts/*/Proofs/*.lean
    errors.extend(
        check_compat_wrappers_in_proofs(
            forbid_constructor_compat=args.forbid_constructor_compat
        )
    )
    if args.forbid_constructor_compat:
        errors.extend(scan_constructor_compat_antipattern())

    report_errors(errors, "Lean hygiene check failed")
    print(
        f"Lean hygiene check passed "
        f"(0 debug commands in proofs, {unsafe_count} allowUnsafeReducibility, "
        f"{sorry_count} sorry ({sorry_count - len(unexpected_sorry_locations)} allowed, {len(unexpected_sorry_locations)} unexpected), "
        f"0 native_decide in proofs)."
    )


ALLOWED_COMPAT_WRAPPERS_IN_PROOFS: dict[str, set[str]] = {
    "Contracts/ERC20/Proofs/Basic.lean": {"constructorCompat"},
}

COMPAT_WRAPPER_DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+)?(?:noncomputable\s+)?(?:def|abbrev)\s+([A-Za-z0-9_']*Compat)\b"
)

CONSTRUCTOR_COMPAT_RE = re.compile(r"\bconstructorCompat\b")


def scan_constructor_compat_antipattern(
    paths: Iterable[Path | str] | Path | str | None = None,
) -> list[str]:
    """Scan contract proof files for the `constructorCompat` wrapper antipattern."""
    findings: list[str] = []
    candidate_files: list[Path] = []
    if paths is None:
        contracts_dir = ROOT / "Contracts"
        if contracts_dir.exists():
            for lean_file in sorted(contracts_dir.rglob("*.lean")):
                rel = lean_file.relative_to(ROOT)
                if "Proofs" in rel.parts:
                    candidate_files.append(lean_file)
    else:
        raw_items = [paths] if isinstance(paths, (Path, str)) else list(paths)
        for item in raw_items:
            p = Path(item)
            if not p.is_absolute() and (ROOT / p).exists():
                p = ROOT / p
            if p.is_dir():
                dir_lean_files = [
                    f for f in sorted(p.rglob("*.lean")) if ".lake" not in f.parts
                ]
                proof_files = [f for f in dir_lean_files if "Proofs" in f.parts]
                candidate_files.extend(proof_files if proof_files else dir_lean_files)
            elif p.is_file():
                candidate_files.append(p)

    for lean_file in candidate_files:
        try:
            rel_str = str(lean_file.relative_to(ROOT)).replace("\\", "/")
        except ValueError:
            rel_str = str(lean_file).replace("\\", "/")
        scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
        for i, line in enumerate(scrubbed_lines, 1):
            if CONSTRUCTOR_COMPAT_RE.search(line):
                findings.append(
                    f"{rel_str}:{i}: found forbidden constructorCompat antipattern "
                    f"in contract proof file"
                )
    return findings


def check_compat_wrappers_in_proofs(forbid_constructor_compat: bool = False) -> list[str]:
    """Flag unapproved *Compat wrapper definitions inside Contracts/*/Proofs/*.lean."""
    compat_errors: list[str] = []
    contracts_dir = ROOT / "Contracts"
    if not contracts_dir.exists():
        return compat_errors
    for lean_file in sorted(contracts_dir.rglob("*.lean")):
        rel = lean_file.relative_to(ROOT)
        if "Proofs" not in rel.parts:
            continue
        rel_str = str(rel).replace("\\", "/")
        allowed = (
            set()
            if forbid_constructor_compat
            else ALLOWED_COMPAT_WRAPPERS_IN_PROOFS.get(rel_str, set())
        )
        scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
        for i, line in enumerate(scrubbed_lines, 1):
            match = COMPAT_WRAPPER_DECL_RE.match(line)
            if match:
                decl_name = match.group(1)
                if decl_name not in allowed:
                    compat_errors.append(
                        f"{rel_str}:{i}: found unapproved *Compat wrapper definition "
                        f"'{decl_name}' in proof file (prove directly against generated contract definitions)"
                    )
    return compat_errors


if __name__ == "__main__":
    main()
