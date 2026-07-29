#!/usr/bin/env python3
"""Check temporary Lean `sorry`/`admit` holes against MIGRATION_SORRIES.md."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "MIGRATION_SORRIES.md"
BEGIN = "<!-- MIGRATION_SORRIES_JSON_BEGIN -->"
END = "<!-- MIGRATION_SORRIES_JSON_END -->"
TOKEN = re.compile(r"\b(sorry|admit)\b")


def ledger_entries() -> list[dict[str, object]]:
    text = LEDGER.read_text(encoding="utf-8")
    try:
        blob = text.split(BEGIN, 1)[1].split(END, 1)[0]
        data = json.loads(re.search(r"```json\s*(.*?)\s*```", blob, re.S).group(1))
    except (IndexError, AttributeError, json.JSONDecodeError) as exc:
        raise ValueError(f"invalid machine-readable ledger: {exc}") from exc
    entries = data.get("entries")
    if not isinstance(entries, list):
        raise ValueError("ledger entries must be a JSON list")
    for entry in entries:
        required = {"file", "line", "declaration", "obligation_type", "reason", "dependents", "removal_condition"}
        if not isinstance(entry, dict) or required - entry.keys():
            raise ValueError(f"ledger entry missing required fields: {entry!r}")
    return entries


def code_only(text: str) -> str:
    """Blank Lean strings and comments while retaining line positions."""
    out: list[str] = []
    i = depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1; out.extend("  "); i += 2
            elif text.startswith("-/", i):
                depth -= 1; out.extend("  "); i += 2
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif in_string:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  "); i += 2
            elif text[i] == '"':
                in_string = False; out.append(" "); i += 1
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0: end = len(text)
            out.extend(" " * (end - i)); i = end
        elif text.startswith("/-", i):
            depth = 1; out.extend("  "); i += 2
        elif text[i] == '"':
            in_string = True; out.append(" "); i += 1
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def actual_holes() -> set[tuple[str, int, str]]:
    hits: set[tuple[str, int, str]] = set()
    for path in ROOT.rglob("*.lean"):
        if any(part in {".lake", "build"} for part in path.parts):
            continue
        source = path.read_text(encoding="utf-8")
        cleaned = code_only(source)
        for match in TOKEN.finditer(cleaned):
            line = cleaned.count("\n", 0, match.start()) + 1
            hits.add((path.relative_to(ROOT).as_posix(), line, match.group(1)))
    return hits


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--certify", action="store_true", help="require zero ledger entries and zero holes")
    args = parser.parse_args()
    try:
        entries = ledger_entries()
    except ValueError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 2
    ledger = {(str(e["file"]), int(e["line"]), str(e["obligation_type"])) for e in entries}
    found = actual_holes()
    missing = found - ledger
    stale = ledger - found
    if missing or stale or (args.certify and (found or entries)):
        for item in sorted(missing): print(f"FAIL: unledgered hole {item}", file=sys.stderr)
        for item in sorted(stale): print(f"FAIL: stale ledger entry {item}", file=sys.stderr)
        if args.certify: print("FAIL: certification requires zero temporary holes", file=sys.stderr)
        return 1
    print(f"OK: {len(found)} temporary hole(s) match MIGRATION_SORRIES.md")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
