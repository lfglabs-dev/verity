#!/usr/bin/env python3
"""Detect (and optionally prune) dead `private` Lean declarations.

A `private theorem` / `private lemma` / `private def` / `private abbrev` is
only visible inside its own file.  It is *dead* when no non-private part of
the file reaches it, directly or transitively through other private
declarations.  Dead private declarations are pure maintenance cost: they are
re-elaborated on every build but can never be used.

Reachability is computed over top-level command blocks:

- every private theorem/lemma/def/abbrev block is a node;
- a `mutual ... end` block whose declarations are all private is one node;
- everything else in the file (public declarations, `example`s, `attribute`
  commands, macros, ...) is a root;
- a private declaration carrying a non-trivial attribute (e.g. `@[simp]`)
  is a root, because `simp` and friends use it without naming it.

A block references a private declaration when any identifier component in the
block's comment-free code equals the last component of the declaration name.
This over-approximates uses (dot notation, `foo.eq_def`, `foo.induct`, local
variables that happen to share the name), so pruning errs on keeping code.

Usage:
    python3 scripts/check_dead_private_decls.py --check [FILES...]
    python3 scripts/check_dead_private_decls.py --fix [FILES...]

With no FILES, the default gated target list below is used.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

from property_utils import ROOT, strip_lean_comments

DEFAULT_TARGETS = [
    "Compiler/Proofs/EndToEnd/SimpleStorage.lean",
    "Compiler/Proofs/IRGeneration/SourceSemantics.lean",
    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness/Runtime.lean",
    "Compiler/Proofs/IRGeneration/GenericInduction/Helpers.lean",
    "Compiler/Proofs/IRGeneration/SupportedSpec.lean",
    "Compiler/Proofs/IRGeneration/FunctionBody/Stmt.lean",
    "Compiler/TypedIRCompiler.lean",
]

# Attributes that do not make a declaration usable without naming it.
HARMLESS_ATTRS = {
    "reducible",
    "irreducible",
    "semireducible",
    "inline",
    "noinline",
    "always_inline",
    "macro_inline",
    "specialize",
}

_MODIFIERS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
_ATTRS = r"(?P<attrs>(?:@\[[^\]]*\]\s*)*)"

# Column-0 tokens that start a new top-level command.
_COMMAND_RE = re.compile(
    r"^(?:@\[|#[a-z]|(?:theorem|lemma|def|abbrev|instance|example|structure|"
    r"inductive|class|opaque|axiom|private|protected|noncomputable|partial|"
    r"unsafe|namespace|section|end|open|mutual|set_option|attribute|variable|"
    r"universe|macro|macro_rules|syntax|elab|elab_rules|notation|infix|infixl|"
    r"infixr|prefix|postfix|local|scoped|import|initialize|builtin_initialize|"
    r"omit|include|export|add_decl_doc|register_simp_attr|"
    r"declare_syntax_cat)\b)"
)
_DECL_RE = re.compile(
    rf"^(?:set_option\s+\S+\s+\S+\s+in\s+)*{_ATTRS}(?P<mods>{_MODIFIERS})"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|example|structure|inductive|"
    r"class|opaque|axiom)\b\s*(?P<name>[^\s:({\[⦃]*)"
)
_SET_OPTION_IN_RE = re.compile(r"^set_option\s+\S+\s+\S+\s+in\s*$")
_ATTR_ONLY_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)+$")
# Unicode letters/digits/underscore (incl. Greek and subscripts) but not
# brackets or operators such as `⟨`, `←`, `·`.
_IDENT_RE = re.compile(r"[^\W\d][\w'!?.]*")
_PRUNABLE_KINDS = {"theorem", "lemma", "def", "abbrev"}


@dataclass
class Block:
    """A top-level command span `[start, end)` over 0-indexed lines."""

    start: int
    end: int
    names: list[str] = field(default_factory=list)
    private: bool = False
    pinned: bool = False


def _attr_names(attrs: str) -> list[str]:
    names: list[str] = []
    for group in re.findall(r"@\[([^\]]*)\]", attrs):
        for item in group.split(","):
            words = item.split()
            words = [w for w in words if w not in {"local", "scoped"}]
            if words:
                names.append(words[0])
    return names


def _is_pinned(attrs: str) -> bool:
    return any(a not in HARMLESS_ATTRS for a in _attr_names(attrs))


def _command_starts(orig: list[str], code: list[str]) -> list[int]:
    """Return the extended start line of every top-level command.

    An extended start absorbs the doc comment, attribute lines, and
    `set_option ... in` prefixes directly above the command (no blank line in
    between).  Module docs (`/-!`) are never absorbed.
    """
    heads: list[int] = []
    i = 0
    while i < len(code):
        line = code[i]
        if _COMMAND_RE.match(line):
            heads.append(i)
            # Collapse an attribute / `set_option ... in` prefix into the
            # command it decorates.
            while i + 1 < len(code) and (
                _ATTR_ONLY_RE.match(line.strip()) or _SET_OPTION_IN_RE.match(line.strip())
            ):
                i += 1
                line = code[i]
        i += 1

    starts: list[int] = []
    # Blank lines become a marker; inside a block comment the stripper blanks
    # the marker again, so `in_comment[j]` covers blank lines in doc comments.
    marked = "\n".join(line if line.strip() else "X" for line in orig)
    in_comment = [not line.strip() for line in strip_lean_comments(marked).split("\n")]
    prev_head = -1
    for h in heads:
        s = h
        while s - 1 > prev_head and in_comment[s - 1]:
            s -= 1
        # Do not swallow a module doc comment sitting above the command.
        for j in range(s, h):
            if orig[j].lstrip().startswith("/-!"):
                k = j
                while k < h and "-/" not in orig[k]:
                    k += 1
                s = k + 1
        starts.append(min(s, h))
        prev_head = h
    return starts


def parse_blocks(text: str) -> tuple[list[str], list[Block]]:
    """Split *text* into top-level blocks with declared names."""
    orig = text.split("\n")
    code = strip_lean_comments(text).split("\n")
    starts = _command_starts(orig, code)
    blocks: list[Block] = []
    if not starts or starts[0] > 0:
        blocks.append(Block(0, starts[0] if starts else len(orig)))
    for idx, s in enumerate(starts):
        nxt = starts[idx + 1] if idx + 1 < len(starts) else len(orig)
        # Trailing comments/blank lines that belong to no declaration code
        # (section headers, separators) are split off as a root block.
        last = s
        for j in range(s, nxt):
            if code[j].strip():
                last = j
        end = last + 1
        while end < nxt and not orig[end].strip():
            end += 1
        blocks.append(_classify(code, s, end))
        if end < nxt:
            blocks.append(Block(end, nxt))
    return orig, _merge_mutual(code, blocks)


def _classify(code: list[str], start: int, end: int) -> Block:
    block = Block(start, end)
    head = "\n".join(code[start:end]).lstrip()
    m = _DECL_RE.match(head)
    if not m:
        return block
    name = m.group("name")
    block.names = [name] if name else []
    block.private = (
        "private" in m.group("mods").split()
        and m.group("kind") in _PRUNABLE_KINDS
        and bool(name)
    )
    block.pinned = _is_pinned(m.group("attrs"))
    return block


def _head(code: list[str], block: Block) -> str:
    """Return the first non-blank code line of *block*, stripped."""
    for j in range(block.start, block.end):
        if code[j].strip():
            return code[j].strip()
    return ""


def _merge_mutual(code: list[str], blocks: list[Block]) -> list[Block]:
    """Fold every `mutual ... end` region into a single block."""
    merged: list[Block] = []
    i = 0
    while i < len(blocks):
        b = blocks[i]
        if _head(code, b) == "mutual":
            j = i + 1
            inner: list[Block] = []
            while j < len(blocks) and _head(code, blocks[j]) != "end":
                inner.append(blocks[j])
                j += 1
            end_block = blocks[j] if j < len(blocks) else blocks[-1]
            decls = [x for x in inner if x.names]
            group = Block(b.start, end_block.end)
            group.names = [n for x in decls for n in x.names]
            group.private = bool(decls) and all(x.private for x in decls)
            group.pinned = any(x.pinned for x in decls)
            merged.append(group)
            i = j + 1
            continue
        merged.append(b)
        i += 1
    return merged


def _short(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def _idents(code: str) -> set[str]:
    out: set[str] = set()
    for tok in _IDENT_RE.findall(code):
        out.update(part for part in tok.split(".") if part)
    return out


def find_dead(text: str) -> tuple[list[str], list[Block], list[Block]]:
    """Return `(lines, blocks, dead_blocks)` for *text*."""
    orig, blocks = parse_blocks(text)
    code = strip_lean_comments(text).split("\n")
    refs = [_idents("\n".join(code[b.start : b.end])) for b in blocks]
    by_short: dict[str, list[int]] = {}
    for idx, b in enumerate(blocks):
        if b.private:
            for n in b.names:
                by_short.setdefault(_short(n), []).append(idx)

    live = {idx for idx, b in enumerate(blocks) if not b.private or b.pinned}
    work = list(live)
    while work:
        idx = work.pop()
        own = {_short(n) for n in blocks[idx].names}
        for tok in refs[idx] - own:
            for tgt in by_short.get(tok, ()):
                if tgt not in live:
                    live.add(tgt)
                    work.append(tgt)
    dead = [b for idx, b in enumerate(blocks) if idx not in live]
    return orig, blocks, dead


def prune(text: str) -> tuple[str, list[str]]:
    """Return *text* with dead private blocks removed, plus removed names."""
    orig, _, dead = find_dead(text)
    drop: set[int] = set()
    for b in dead:
        drop.update(range(b.start, b.end))
    out: list[str] = []
    seam = False
    for i, line in enumerate(orig):
        if i in drop:
            seam = True
            continue
        # Collapse the blank run left behind at a removal seam only.
        if seam and not line.strip() and out and not out[-1].strip():
            continue
        seam = seam and not line.strip()
        out.append(line)
    return "\n".join(out), [n for b in dead for n in b.names]


def _resolve(paths: list[str]) -> list[Path]:
    return [(Path(p) if Path(p).is_absolute() else ROOT / p) for p in (paths or DEFAULT_TARGETS)]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="fail if dead private decls exist")
    mode.add_argument("--fix", action="store_true", help="remove dead private decls in place")
    parser.add_argument("files", nargs="*", help="Lean files (default: gated targets)")
    args = parser.parse_args(argv)

    total = 0
    for path in _resolve(args.files):
        text = path.read_text(encoding="utf-8")
        rel = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
        if args.fix:
            # Pruning is transitive in one pass; loop for block-merge safety.
            removed_all: list[str] = []
            while True:
                text, removed = prune(text)
                if not removed:
                    break
                removed_all.extend(removed)
            if removed_all:
                path.write_text(text, encoding="utf-8")
                print(f"{rel}: removed {len(removed_all)} dead private declaration(s)")
            continue
        orig, _, dead = find_dead(text)
        for b in dead:
            for n in b.names:
                print(f"{rel}:{b.start + 1}: dead private declaration `{n}`")
        total += sum(len(b.names) for b in dead)

    if args.fix:
        return 0
    if total:
        print(
            f"\n{total} dead private declaration(s) found. "
            "Run `python3 scripts/check_dead_private_decls.py --fix` to prune them.",
            file=sys.stderr,
        )
        return 1
    print("Dead private declaration check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
