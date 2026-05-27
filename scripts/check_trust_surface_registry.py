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


def main() -> int:
    docs = _read_doc_corpus()
    mechanisms, ecm_axioms = collect_trust_surface()

    errors: list[str] = []
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
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
