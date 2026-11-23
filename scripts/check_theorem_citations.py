#!/usr/bin/env python3
"""Fail closed when a proof-status citation names something that is not a theorem.

A citation is a place that offers a Lean theorem name as evidence that something is
proved. This check resolves every such name against the theorem and lemma declarations
in the repository's Lean sources and fails when it does not name one: a missing name, a
`def`, `structure` field or other non-theorem declaration all fail.

Citation sites:

1. Lean catalogs (every `*.lean` file outside test modules):
   - `theoremRef := "N"` and `refutationTheorem := "N"` string fields,
   - `proofRefName "N"` (rewrite-rule `proofId` and parity-pack proof references),
   - every string literal in the list of a `def ...TheoremAllowlist` / `...ProofAllowlist`.
   `N` must be the fully qualified name of a theorem or lemma.
2. Documentation (`*.md` and `*.mdx` outside `artifacts/`): a backticked name that follows
   "theorem", "lemma", "proves", "proved", "proven" or "proving" (optionally "that"/"the"
   and one qualifier such as "generic"), including the rest of a backticked list joined by
   commas, "and", "or" or "/", and a backticked name directly followed by "theorem" or
   "lemma". Only names whose last component looks like a Lean theorem name (starts with a
   lowercase letter and contains `_`) are checked. A name may be written with any suffix of
   its fully qualified name. A theorem generated per contract by the `verity_contract`
   macro (`entrypointRegistry_preserves`, `entrypointRegistry_cases`) resolves when its
   prefix, if any, names a `verity_contract`.

Blind spots (text-level check, no Lean elaboration):
- Declarations created by other macros or elaborators (`#gen_fn_spec`, `deriving`, `where`
  auxiliaries, `initialize`) are not in the index; citing one fails until it is added.
- Names from Lean core, Std, Mathlib or other packages are not indexed. Lean catalogs must
  cite repository theorems; documentation phrases that cite external names are only caught
  when the phrase matches (then they fail and must be reworded or qualified out of the
  phrase).
- `open`, `export` and `variable`-dependent name resolution are not modelled: a Lean catalog
  string must be the declaration's full name.
- It checks that the cited theorem exists, not what it states: a real theorem that does not
  support the claim at the citation site (a disconnected helper, an abstract model) passes.
- Documentation citations not phrased as above (tables, "see `X`", prose without a trigger
  word) and names without `_` in the last component are not checked.
- A theorem proved with `sorry` still counts as a theorem here (`check_lean_hygiene.py`
  rejects `sorry` separately).
"""

from __future__ import annotations

import argparse
import functools
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path

from property_utils import ROOT, report_errors, strip_lean_comments

THEOREM_KINDS = frozenset({"theorem", "lemma"})
EXCLUDED_DIRS = frozenset({".lake", ".git", "node_modules", "artifacts", "lake-packages", "build"})
MACRO_GENERATED_THEOREMS = ("entrypointRegistry_preserves", "entrypointRegistry_cases")
MACRO_SOURCE_DIR = Path("Verity") / "Macro"

_MODIFIERS = r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped)\s+)*"
_ATTRS = r"(?:@\[[^\]]*\]\s*)*"
_DECL_RE = re.compile(
    r"^\s*" + _ATTRS + _MODIFIERS
    + r"(theorem|lemma|def|abbrev|opaque|axiom|instance|structure|inductive|class)"
    + r"\s+([A-Za-z_«][^\s:({\[]*)"
)
_NAMESPACE_RE = re.compile(r"^\s*namespace\s+([^\s]+)\s*$")
_SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section\b")
_MUTUAL_RE = re.compile(r"^\s*mutual\s*$")
_END_RE = re.compile(r"^\s*end(?:\s+([^\s]+))?\s*$")
_VERITY_CONTRACT_RE = re.compile(r"^\s*verity_contract\s+([A-Za-z_][A-Za-z0-9_']*)", re.MULTILINE)

_QUALIFIED = r"[A-Za-z_][A-Za-z0-9_'.]*"
_FIELD_RE = re.compile(r'\b(theoremRef|refutationTheorem)\s*:=\s*"([^"]*)"')
_PROOF_REF_RE = re.compile(r'\bproofRefName\s+"([^"]*)"')
_ALLOWLIST_DEF_RE = re.compile(
    r"\bdef\s+([A-Za-z_][A-Za-z0-9_']*(?:TheoremAllowlist|ProofAllowlist))\b[^:=]*:\s*List\s+String\s*:=\s*\["
)
_STRING_RE = re.compile(r'"([^"]*)"')

_DOC_NAME = r"`([A-Za-z_][A-Za-z0-9_'.]*)`"
_DOC_LIST_TAIL = re.compile(r"\s*(?:,\s*(?:and\s+|or\s+)?|\s+and\s+|\s+or\s+|\s*/\s*)" + _DOC_NAME)
_DOC_LEAD_RE = re.compile(
    r"\b(?:theorems?|lemmas?|proves|proved|proven|proving)\s+"
    r"(?:(?:that|the)\s+)?"
    r"(?:(?:generated|generic|public|kernel|universal|exact|main|helper|bridge)\s+)?"
    + _DOC_NAME,
    re.IGNORECASE,
)
_DOC_TRAIL_RE = re.compile(_DOC_NAME + r"\s+(?:theorem|lemma)\b", re.IGNORECASE)


@dataclass(frozen=True)
class Decl:
    kind: str
    location: str


def _iter_files(root: Path, suffixes: tuple[str, ...]) -> list[Path]:
    out: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if d not in EXCLUDED_DIRS)
        for filename in sorted(filenames):
            if filename.endswith(suffixes):
                out.append(Path(dirpath) / filename)
    return out


@functools.lru_cache(maxsize=None)
def _lean_sources(root: Path) -> tuple[tuple[Path, str, str], ...]:
    """(relative path, raw text, comment-stripped text) of every Lean source under `root`."""
    out = []
    for path in _iter_files(root, (".lean",)):
        raw = path.read_text(encoding="utf-8", errors="replace")
        out.append((path.relative_to(root), raw, strip_lean_comments(raw)))
    return tuple(out)


def _is_test_module(rel: Path) -> bool:
    stem = rel.stem
    return stem.endswith("Test") or stem.endswith("Tests") or "Test" in rel.parts[:-1]


def collect_declarations(root: Path) -> dict[str, Decl]:
    """Index fully qualified declaration names (namespace-aware) of every Lean source."""
    decls: dict[str, Decl] = {}
    for rel, _raw, text in _lean_sources(root):
        scopes: list[tuple[str, str | None]] = []
        for lineno, line in enumerate(text.splitlines(), start=1):
            match = _NAMESPACE_RE.match(line)
            if match:
                scopes.append(("namespace", match.group(1)))
                continue
            if _SECTION_RE.match(line):
                scopes.append(("section", None))
                continue
            if _MUTUAL_RE.match(line):
                scopes.append(("mutual", None))
                continue
            if _END_RE.match(line):
                if scopes:
                    scopes.pop()
                continue
            match = _DECL_RE.match(line)
            if not match:
                continue
            kind, name = match.groups()
            name = name.rstrip(".")
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                prefix = ".".join(n for k, n in scopes if k == "namespace" and n)
                full = f"{prefix}.{name}" if prefix else name
            decls.setdefault(full, Decl(kind, f"{rel}:{lineno}"))
    return decls


@dataclass(frozen=True)
class Citation:
    location: str
    name: str
    exact: bool  # Lean catalogs must use the full name; docs may use a suffix.


def _allowlist_strings(text: str) -> list[tuple[int, str]]:
    found: list[tuple[int, str]] = []
    for match in _ALLOWLIST_DEF_RE.finditer(text):
        start = match.end()
        depth = 1
        i = start
        while i < len(text) and depth:
            if text[i] == '"':
                j = text.index('"', i + 1)
                found.append((text.count("\n", 0, i) + 1, text[i + 1:j]))
                i = j + 1
                continue
            if text[i] == "[":
                depth += 1
            elif text[i] == "]":
                depth -= 1
            i += 1
    return found


def collect_lean_citations(root: Path) -> list[Citation]:
    citations: list[Citation] = []
    for rel, _raw, text in _lean_sources(root):
        if _is_test_module(rel):
            continue
        for lineno, line in enumerate(text.splitlines(), start=1):
            for match in _FIELD_RE.finditer(line):
                citations.append(Citation(f"{rel}:{lineno} ({match.group(1)})", match.group(2), True))
            for match in _PROOF_REF_RE.finditer(line):
                citations.append(Citation(f"{rel}:{lineno} (proofRefName)", match.group(1), True))
        for lineno, value in _allowlist_strings(text):
            citations.append(Citation(f"{rel}:{lineno} (theorem allowlist)", value, True))
    return citations


def _looks_like_theorem_name(name: str) -> bool:
    last = name.rsplit(".", 1)[-1]
    return "_" in last and last[:1].islower()


def collect_doc_citations(root: Path) -> list[Citation]:
    citations: list[Citation] = []
    for path in _iter_files(root, (".md", ".mdx")):
        rel = path.relative_to(root)
        for lineno, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
            names: list[str] = []
            for match in _DOC_LEAD_RE.finditer(line):
                names.append(match.group(1))
                pos = match.end()
                while True:
                    tail = _DOC_LIST_TAIL.match(line, pos)
                    if not tail:
                        break
                    names.append(tail.group(1))
                    pos = tail.end()
            names.extend(m.group(1) for m in _DOC_TRAIL_RE.finditer(line))
            seen: set[str] = set()
            for name in names:
                name = name.rstrip(".")
                if name in seen or not _looks_like_theorem_name(name):
                    continue
                seen.add(name)
                citations.append(Citation(f"{rel}:{lineno}", name, False))
    return citations


def _macro_theorem_errors(root: Path) -> list[str]:
    sources = "".join(
        raw for rel, raw, _text in _lean_sources(root) if rel.parts[:2] == MACRO_SOURCE_DIR.parts
    )
    return [
        f"MACRO_GENERATED_THEOREMS lists `{name}`, but no `\"{name}\"` literal is in {MACRO_SOURCE_DIR}/"
        for name in MACRO_GENERATED_THEOREMS
        if f'"{name}"' not in sources
    ]


def _verity_contracts(root: Path) -> set[str]:
    names: set[str] = set()
    for _rel, _raw, text in _lean_sources(root):
        names.update(_VERITY_CONTRACT_RE.findall(text))
    return names


def check(root: Path) -> list[str]:
    decls = collect_declarations(root)
    by_last: dict[str, list[str]] = {}
    for full in decls:
        by_last.setdefault(full.rsplit(".", 1)[-1], []).append(full)
    contracts = _verity_contracts(root)

    def describe(full: str) -> str:
        decl = decls[full]
        return f"`{full}` is a {decl.kind} ({decl.location})"

    errors = _macro_theorem_errors(root)
    for cite in collect_lean_citations(root) + collect_doc_citations(root):
        name = cite.name
        if cite.exact:
            if name in decls and decls[name].kind in THEOREM_KINDS:
                continue
            if name in decls:
                errors.append(f"{cite.location}: cites `{name}`, which is not a theorem: {describe(name)}")
                continue
            near = [f for f in by_last.get(name.rsplit(".", 1)[-1], []) if decls[f].kind in THEOREM_KINDS]
            hint = f" (a theorem with this last component exists as `{near[0]}`)" if near else ""
            errors.append(f"{cite.location}: cites `{name}`, which is not a declaration in the source{hint}")
            continue
        last = name.rsplit(".", 1)[-1]
        matches = [f for f in by_last.get(last, []) if f == name or f.endswith("." + name)]
        if any(decls[f].kind in THEOREM_KINDS for f in matches):
            continue
        if last in MACRO_GENERATED_THEOREMS:
            prefix = name[: -len(last)].rstrip(".")
            if not prefix or prefix.rsplit(".", 1)[-1] in contracts:
                continue
        if matches:
            errors.append(
                f"{cite.location}: cites `{name}` as a theorem, but it is not one: "
                + "; ".join(describe(f) for f in matches)
            )
        else:
            errors.append(f"{cite.location}: cites `{name}` as a theorem, but no such declaration exists")
    return errors


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args(argv)
    errors = check(args.root)
    report_errors(errors, "Theorem citations that do not name a theorem in the source")
    print("Theorem citations: every catalog and documentation citation names a theorem.")


if __name__ == "__main__":
    main()
