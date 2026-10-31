#!/usr/bin/env python3
"""Generate PrintAxioms.lean and scripts/VerityUnionAxioms.lean from the verified population.

Scans the canonical verified-module population under ``Verity``, ``Compiler``,
and ``Contracts`` (discovered by ``scripts/check_union_coverage.py``), extracts
every public theorem/lemma (including indented declarations inside ``mutual`` and
``where`` blocks, skipping macro-splice placeholders containing ``$``), and emits:

1. ``scripts/VerityUnionAxioms.lean`` — imports ``AxiomAudit`` and the minimal
   verified root modules (transitively covering every verified module and zero
   non-verified local modules) and runs ``#union_axioms_of_modules`` over
   ``Verity, Compiler, Contracts``.
2. ``PrintAxioms.lean`` — imports ``AxiomAudit`` and the same verified root
   modules, verifies the whole-population union first, and then prints exact
   from-scratch per-theorem axiom lines (no ``collectAxioms``, no per-constant
   cycle cache) via ``Jaune.AxiomAudit.reportPrintAxiomsForRootsM``.

Usage:
    python3 scripts/generate_print_axioms.py          # overwrite generated files
    python3 scripts/generate_print_axioms.py --check  # verify both files are up-to-date
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_axioms import BV_DECIDE_AXIOM_ORIGINS, NATIVE_DECIDE_AXIOM_ORIGINS
from check_union_coverage import check_union_coverage, discover_population
from property_utils import scrub_lean_code

ROOT = SCRIPT_DIR.parent
OUTPUT = ROOT / "PrintAxioms.lean"
UNION_OUTPUT = ROOT / "scripts" / "VerityUnionAxioms.lean"

# Allowed axiom union across the verified population in Phase 0a (before Phase 0b+1
# removes `native_decide`/`bv_decide` origins and Phase 2 removes `solidityMappingSlot_injective`).
ALLOWED_POPULATION_AXIOMS: tuple[str, ...] = (
    "propext",
    "Classical.choice",
    "Quot.sound",
    "Compiler.Proofs.solidityMappingSlot_injective",
)

SORRY_RE_BODY = re.compile(r"\bsorry\b")
_DECL_PREFIX_RE = (
    r"(?:(?:@\[[^\]]*\]|private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*"
)
_INLINE_THEOREM_RE = re.compile(
    rf"^(?P<prefix>{_DECL_PREFIX_RE})(?P<kind>theorem|lemma)\s+(?P<name>[^\s:({{\[⦃]+)"
)
_SPLIT_THEOREM_RE = re.compile(rf"^(?P<prefix>{_DECL_PREFIX_RE})(?P<kind>theorem|lemma)$")
_SPLIT_NAME_RE = re.compile(r"^(?P<name>[^\s:({\[⦃]+)")


def _lean_string_array(items: list[str] | tuple[str, ...]) -> str:
    if not items:
        return "#[]"
    body = ",\n    ".join(f'"{item}"' for item in items)
    return f"#[\n    {body}\n  ]"


def _render_population_union_block() -> str:
    allowed = _lean_string_array(list(ALLOWED_POPULATION_AXIOMS))
    native_origins = _lean_string_array(sorted(NATIVE_DECIDE_AXIOM_ORIGINS))
    bv_origins = _lean_string_array(sorted(BV_DECIDE_AXIOM_ORIGINS))
    return (
        "open Jaune.AxiomAudit Lean Elab Command in\n"
        "run_cmd do\n"
        "  let env ← getEnv\n"
        "  let pfxs := #[`Verity, `Compiler, `Contracts]\n"
        "  let mr := moduleRootsOf env pfxs\n"
        "  let roots := mr.1\n"
        "  let modules := mr.2\n"
        f"  let allowed := {allowed}\n"
        f"  let allowedNativeOrigins := {native_origins}\n"
        f"  let allowedBvOrigins := {bv_origins}\n"
        "  match (← unionCheckM env (unionLabel pfxs) roots modules allowed allowedNativeOrigins allowedBvOrigins) with\n"
        '  | .error e => throwError "{e}"\n'
        "  | .ok r =>\n"
        "    logInfo (MessageData.ofFormat (Std.Format.text\n"
        '      (s!"UNION-AXIOMS \'{unionLabel pfxs}\': [{", ".intercalate r.axioms.toList}] "\n'
        '        ++ s!"roots={r.roots} modules={r.modules} visited={r.visited}")))\n'
    )


def file_to_module(path: Path, root: Path = ROOT) -> str:
    """Convert a file path to a Lean module name."""
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def extract_theorems(path: Path) -> list[tuple[str, bool, bool]]:
    """Extract ``(fully_qualified_name, is_private, is_sorry)`` triples from a Lean file.

    Matches top-level, indented, and split-header ``theorem``/``lemma`` declarations
    (including declarations inside ``mutual`` blocks), resolves segmented namespaces
    and sections/mutuals/macro ``interface ... where ... end`` blocks without stack
    desynchronisation, scrubs comments and string literals, and skips macro quotation
    placeholders whose names contain ``$``.
    """
    text = path.read_text(encoding="utf-8")
    scrubbed_text = scrub_lean_code(text)
    lines = scrubbed_text.splitlines()

    # Stack of `(kind, segment)` entries where `kind == "namespace"` contributes `segment`
    # to the active FQN prefix and `"section"` / `"mutual"` / `"interface"` track scope depth.
    scope_stack: list[tuple[str, str]] = []
    raw_results: list[tuple[str, bool, int]] = []

    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        if not stripped:
            i += 1
            continue

        if re.match(r"^interface\s+\S+\s+where$", stripped):
            scope_stack.append(("interface", ""))
            i += 1
            continue

        ns_match = re.match(r"^(?:noncomputable\s+)?namespace\s+(\S+)$", stripped)
        if ns_match:
            for seg in ns_match.group(1).split("."):
                scope_stack.append(("namespace", seg))
            i += 1
            continue

        sec_match = re.match(r"^(?:noncomputable\s+)?section(?:\s+(\S+))?$", stripped)
        if sec_match:
            sec_name = sec_match.group(1)
            if sec_name:
                for seg in sec_name.split("."):
                    scope_stack.append(("section", seg))
            else:
                scope_stack.append(("section", ""))
            i += 1
            continue

        if re.match(r"^(?:noncomputable\s+)?mutual$", stripped):
            scope_stack.append(("mutual", ""))
            i += 1
            continue

        end_match = re.match(r"^end(?:\s+(\S+))?$", stripped)
        if end_match:
            end_name = end_match.group(1)
            if end_name is None:
                if scope_stack:
                    scope_stack.pop()
            else:
                for seg in reversed(end_name.split(".")):
                    if scope_stack and scope_stack[-1][1] == seg:
                        scope_stack.pop()
            i += 1
            continue

        decl_match = _INLINE_THEOREM_RE.match(stripped)
        prefix_text: str | None = None
        raw_name: str | None = None
        step = 1
        if decl_match:
            prefix_text = decl_match.group("prefix")
            raw_name = decl_match.group("name")
        else:
            split_match = _SPLIT_THEOREM_RE.match(stripped)
            if split_match and i + 1 < len(lines):
                next_match = _SPLIT_NAME_RE.match(lines[i + 1].strip())
                if next_match:
                    prefix_text = split_match.group("prefix")
                    raw_name = next_match.group("name")
                    step = 2

        if prefix_text is not None and raw_name is not None:
            is_private = bool(re.search(r"\bprivate\b", prefix_text))
            name = raw_name.rstrip(":")
            if "$" not in name:
                ns_parts = [seg for kind, seg in scope_stack if kind == "namespace" and seg]
                fqn = f"{'.'.join(ns_parts)}.{name}" if ns_parts else name
                raw_results.append((fqn, is_private, i))
            i += step
            continue

        i += 1

    results: list[tuple[str, bool, bool]] = []
    for idx, (fqn, is_private, start) in enumerate(raw_results):
        end = raw_results[idx + 1][2] if idx + 1 < len(raw_results) else len(lines)
        body = "\n".join(lines[start:end])
        is_sorry = bool(SORRY_RE_BODY.search(body))
        results.append((fqn, is_private, is_sorry))

    return results


def generate_union_axioms(root: Path = ROOT) -> str:
    """Generate ``scripts/VerityUnionAxioms.lean`` content."""
    _, verified, _, roots = discover_population(root)
    imports = "\n".join(["import AxiomAudit", *(f"import {mod}" for mod in roots)])
    return (
        "-- Auto-generated by scripts/generate_print_axioms.py\n"
        f"-- Whole-library from-scratch axiom union over all {len(verified)} verified modules\n"
        f"-- ({len(roots)} root imports, 0 non-verified local modules).\n"
        "-- Regenerate with: python3 scripts/generate_print_axioms.py\n\n"
        f"{imports}\n\n"
        f"{_render_population_union_block()}"
    )


def generate(root: Path = ROOT) -> str:
    """Generate the full ``PrintAxioms.lean`` content."""
    disk_map, verified, _, roots = discover_population(root)

    imports = ["import AxiomAudit", *(f"import {mod}" for mod in roots)]
    sections: list[str] = []
    public_count = 0
    private_count = 0
    sorry_count = 0
    seen_public: dict[str, str] = {}

    for module in sorted(verified):
        path = disk_map[module]
        theorems = extract_theorems(path)
        if not theorems:
            continue

        rel = path.relative_to(root).as_posix()
        lines = [f"-- {rel}"]
        for fqn, is_private, is_sorry in theorems:
            if is_private:
                private_count += 1
                lines.append(f"-- {fqn}  -- private")
            elif is_sorry:
                sorry_count += 1
                lines.append(f"-- {fqn}  -- sorry'd")
            else:
                if fqn in seen_public:
                    raise ValueError(
                        f"duplicate public theorem FQN {fqn} in {seen_public[fqn]} and {rel}"
                    )
                seen_public[fqn] = rel
                public_count += 1
                lines.append(fqn)
        sections.append("\n".join(lines))

    blob_body = (
        "\n\n".join(sections)
        .replace("\\", "\\\\")
        .replace('"', '\\"')
    )

    header = (
        "-- Auto-generated by scripts/generate_print_axioms.py\n"
        "-- Runs a fail-closed whole-population union check and an exact from-scratch\n"
        "-- per-theorem axiom audit (no Lean.collectAxioms, no cycle sentinel cache)\n"
        f"-- across all {len(verified)} verified modules ({len(roots)} root imports).\n"
        "-- Regenerate with: python3 scripts/generate_print_axioms.py\n"
    )

    union_block = _render_population_union_block()
    allowed_arr = _lean_string_array(list(ALLOWED_POPULATION_AXIOMS))
    native_origins_arr = _lean_string_array(sorted(NATIVE_DECIDE_AXIOM_ORIGINS))
    bv_origins_arr = _lean_string_array(sorted(BV_DECIDE_AXIOM_ORIGINS))
    runner = f'''
{union_block}
open Jaune.AxiomAudit Lean Elab Command in
private def verityAuditedTheoremBlob : String :=
"{blob_body}"

open Jaune.AxiomAudit Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := parseDottedNames verityAuditedTheoremBlob
  let allowed := {allowed_arr}
  let allowedNativeOrigins := {native_origins_arr}
  let allowedBvOrigins := {bv_origins_arr}
  match (← reportPrintAxiomsForRootsM env roots (some allowed) allowedNativeOrigins allowedBvOrigins) with
  | .error e => throwError "{{e}}"
  | .ok lines =>
    for line in lines do
      liftIO <| IO.println line
'''

    footer = (
        f"\n-- Total: {public_count + private_count + sorry_count} theorems/lemmas"
        f" ({public_count} public, {private_count} private, {sorry_count} sorry'd)\n"
    )

    return header + "\n" + "\n".join(imports) + "\n" + runner + footer


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    print_content = generate(ROOT)
    union_content = generate_union_axioms(ROOT)

    if "--check" in args:
        stale: list[Path] = []
        for target, expected in ((OUTPUT, print_content), (UNION_OUTPUT, union_content)):
            if not target.exists() or target.read_text(encoding="utf-8") != expected:
                stale.append(target)
        if stale:
            rendered = ", ".join(str(p.relative_to(ROOT)) for p in stale)
            print(f"ERROR: out of date: {rendered}. Regenerate with:")
            print("  python3 scripts/generate_print_axioms.py")
            return 1
        try:
            covered = check_union_coverage(ROOT)
        except (OSError, ValueError) as exc:
            print(f"ERROR: union coverage check failed: {exc}", file=sys.stderr)
            return 1
        print(
            f"OK: {OUTPUT.relative_to(ROOT)} and {UNION_OUTPUT.relative_to(ROOT)} "
            f"are up to date ({covered} verified modules covered)."
        )
        return 0

    OUTPUT.write_text(print_content, encoding="utf-8")
    UNION_OUTPUT.write_text(union_content, encoding="utf-8")
    print(f"Generated {OUTPUT.relative_to(ROOT)} and {UNION_OUTPUT.relative_to(ROOT)}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
