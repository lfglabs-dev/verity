#!/usr/bin/env python3
"""Schema-driven sync engine: runs declarative rules to generate or check artifacts.

Usage:
    python3 scripts/sync_engine.py --rule <id>           # generate mode
    python3 scripts/sync_engine.py --rule <id> --check   # check mode (fail if stale)
    python3 scripts/sync_engine.py --list                # list available rules

Rules are defined in YAML files (default: scripts/rules/docsync.yaml).
Each rule specifies a Python extractor function whose return value is
serialized and written to a target file.
"""

from __future__ import annotations

import argparse
import difflib
import importlib
import json
import sys
from pathlib import Path
from typing import Any

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
ROOT = SCRIPTS_DIR.parent


def load_rules(yaml_path: Path) -> list[dict[str, Any]]:
    with yaml_path.open(encoding="utf-8") as fh:
        data = yaml.safe_load(fh)
    return data.get("rules", [])


def find_rule(rules: list[dict[str, Any]], rule_id: str) -> dict[str, Any]:
    for rule in rules:
        if rule["id"] == rule_id:
            return rule
    available = [r["id"] for r in rules]
    raise SystemExit(f"Rule '{rule_id}' not found. Available: {available}")


def run_extractor(rule: dict[str, Any]) -> Any:
    extractor = rule["extractor"]
    module_name = extractor["module"]
    function_name = extractor["function"]

    if str(SCRIPTS_DIR) not in sys.path:
        sys.path.insert(0, str(SCRIPTS_DIR))

    mod = importlib.import_module(module_name)
    fn = getattr(mod, function_name)
    kwargs = extractor.get("args") or {}
    return fn(**kwargs)


def serialize(data: Any, rule: dict[str, Any]) -> str:
    fmt = rule.get("output_format", "json")
    if fmt == "json":
        opts = rule.get("json_options") or {}
        indent = opts.get("indent", 2)
        sort_keys = opts.get("sort_keys", False)
        return json.dumps(data, indent=indent, sort_keys=sort_keys) + "\n"
    if fmt == "text":
        return str(data)
    raise ValueError(f"Unknown output_format: {fmt!r}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--rule", metavar="ID", help="Rule id to run")
    group.add_argument("--list", action="store_true", help="List all rules in the file")
    parser.add_argument(
        "--rules-file",
        type=Path,
        default=SCRIPTS_DIR / "rules" / "docsync.yaml",
        help="YAML rules file (default: scripts/rules/docsync.yaml)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Check mode: fail if target is stale rather than writing it",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Override output path (useful for side-by-side comparison)",
    )
    args = parser.parse_args()

    rules = load_rules(args.rules_file)

    if args.list:
        print(f"Rules in {args.rules_file}:")
        for rule in rules:
            cluster = rule.get("cluster", "—")
            print(f"  {rule['id']:40s}  [{cluster}]  {rule.get('description', '')}")
        return 0

    rule = find_rule(rules, args.rule)
    data = run_extractor(rule)
    rendered = serialize(data, rule)
    target = args.output or (ROOT / rule["target"])

    if args.check:
        if not target.exists():
            print(f"[{rule['id']}] Missing artifact: {target}", file=sys.stderr)
            return 1
        existing = target.read_text(encoding="utf-8")
        if existing == rendered:
            print(f"[{rule['id']}] {target.relative_to(ROOT)} is up to date")
            return 0
        diff = list(difflib.unified_diff(
            existing.splitlines(),
            rendered.splitlines(),
            fromfile=str(target.relative_to(ROOT)),
            tofile=f"generated (rule: {rule['id']})",
            lineterm="",
        ))
        for line in diff:
            print(line, file=sys.stderr)
        print(
            f"\n[{rule['id']}] {target.relative_to(ROOT)} is stale; "
            f"run: python3 scripts/sync_engine.py --rule {rule['id']}",
            file=sys.stderr,
        )
        return 1

    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(rendered, encoding="utf-8")
    try:
        label = target.relative_to(ROOT)
    except ValueError:
        label = target
    print(f"[{rule['id']}] wrote {label}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
