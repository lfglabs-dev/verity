#!/usr/bin/env python3
"""Validate that non-axiom trusted surfaces are documented.

The Lean kernel axiom registry is intentionally separate from Verity's broader
trusted surface. This checker covers mechanisms that do not create project
Lean axioms, but still matter for audit soundness:

* `native_decide`
* `@[implemented_by ...]`
* `partial def`
* explicit ECM assumption strings in `axioms := [...]`
"""

from __future__ import annotations

import re
from pathlib import Path

from property_utils import ROOT, report_errors, scrub_lean_code, strip_lean_comments

SCAN_ROOTS = ("Compiler", "Verity", "Contracts", "Benchmark")
DOC_PATHS = ("AXIOMS.md", "TRUST_ASSUMPTIONS.md")
DOC_DIRS = ("docs",)

LEAN424_STRING_BOUNDARY = Path("Compiler/CompilationModel/ReservedScratchNames.lean")
LEAN424_STRING_THEOREMS = (
    "compatScratch_startsWith_reserved",
    "compatScratch_not_internalImmutable",
)

ECM_AXIOM_STRING_RE = re.compile(r'"([^"]+)"')

MECHANISM_PATTERNS = (
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("@[implemented_by", re.compile(r"@\[\s*implemented_by\b")),
    ("partial def", re.compile(r"\bpartial\s+def\b")),
)


def _iter_lean_files(root: Path = ROOT) -> list[Path]:
    files: list[Path] = []
    for subdir in SCAN_ROOTS:
        base = root / subdir
        if base.exists():
            files.extend(sorted(base.rglob("*.lean")))
    return files


def _read_doc_corpus(root: Path = ROOT) -> str:
    chunks: list[str] = []
    for rel in DOC_PATHS:
        path = root / rel
        if path.exists():
            chunks.append(path.read_text(encoding="utf-8"))
    for rel in DOC_DIRS:
        base = root / rel
        if base.exists():
            for path in sorted(base.rglob("*.md")):
                chunks.append(path.read_text(encoding="utf-8"))
    return "\n".join(chunks)


def collect_trust_surface(root: Path = ROOT) -> tuple[dict[str, int], dict[str, tuple[str, int]]]:
    mechanisms = {name: 0 for name, _ in MECHANISM_PATTERNS}
    ecm_axioms: dict[str, tuple[str, int]] = {}

    for path in _iter_lean_files(root):
        raw_text = path.read_text(encoding="utf-8")
        text = scrub_lean_code(raw_text)
        text_without_comments = strip_lean_comments(raw_text)
        rel = str(path.relative_to(root))
        for name, pattern in MECHANISM_PATTERNS:
            mechanisms[name] += len(pattern.findall(text))
        for match in re.finditer(r"axioms\s*:=\s*\[(.*?)\]", text_without_comments, flags=re.DOTALL):
            line_no = text_without_comments.count("\n", 0, match.start()) + 1
            for axiom_name in ECM_AXIOM_STRING_RE.findall(match.group(1)):
                ecm_axioms.setdefault(axiom_name, (rel, line_no))

    return mechanisms, ecm_axioms


def check_lean424_string_boundary(root: Path = ROOT) -> list[str]:
    """Keep the Lean 4.24 native string facts in one explicit trust boundary."""
    errors: list[str] = []
    boundary = root / LEAN424_STRING_BOUNDARY
    if not boundary.is_file():
        return [f"missing Lean 4.24 string trust boundary: {LEAN424_STRING_BOUNDARY}"]

    boundary_text = scrub_lean_code(boundary.read_text(encoding="utf-8"))
    native_count = len(re.findall(r"\bnative_decide\b", boundary_text))
    if native_count != 2:
        errors.append(
            f"{LEAN424_STRING_BOUNDARY}: expected exactly 2 native_decide facts, "
            f"found {native_count}"
        )

    declarations: dict[str, list[str]] = {name: [] for name in LEAN424_STRING_THEOREMS}
    compiler_root = root / "Compiler"
    for path in sorted(compiler_root.rglob("*.lean")):
        text = scrub_lean_code(path.read_text(encoding="utf-8"))
        rel = str(path.relative_to(root))
        for name in LEAN424_STRING_THEOREMS:
            if re.search(rf"\b(?:theorem|lemma)\s+{re.escape(name)}\b", text):
                declarations[name].append(rel)

    expected_path = str(LEAN424_STRING_BOUNDARY)
    for name, locations in declarations.items():
        if locations != [expected_path]:
            errors.append(
                f"{name}: expected one declaration in {expected_path}, found {locations}"
            )

    proofs_root = root / "Compiler" / "Proofs"
    if proofs_root.is_dir():
        for path in sorted(proofs_root.rglob("*.lean")):
            rel = path.relative_to(root)
            stem = path.stem
            if "Test" in stem or "Profile" in stem or "Smoke" in stem or "Smoke" in rel.parts:
                continue
            text = scrub_lean_code(path.read_text(encoding="utf-8"))
            if re.search(r"\bnative_decide\b", text):
                errors.append(
                    f"{rel}: native_decide must remain outside non-test Compiler/Proofs"
                )

    return errors


def main() -> int:
    docs = _read_doc_corpus()
    mechanisms, ecm_axioms = collect_trust_surface()

    errors = check_lean424_string_boundary()
    for name, count in mechanisms.items():
        if count > 0 and name not in docs:
            errors.append(
                f"{name}: {count} occurrence(s) found in Lean sources but missing from trust docs"
            )

    for axiom_name, (rel, line) in sorted(ecm_axioms.items()):
        if axiom_name not in docs:
            errors.append(
                f"{axiom_name}: ECM assumption from {rel}:{line} is missing from trust docs"
            )

    report_errors(errors, "Trust-surface registry check failed")
    print(
        "OK: trust-surface registry documents "
        f"{len(ecm_axioms)} ECM assumption(s), "
        + ", ".join(f"{name}={count}" for name, count in mechanisms.items())
        + "; native_decide trusts builtin Lean.ofReduceBool + Lean.trustCompiler; "
        + f"Lean 4.24 string boundary={LEAN424_STRING_BOUNDARY} (2 facts)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
