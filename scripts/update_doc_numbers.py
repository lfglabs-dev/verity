#!/usr/bin/env python3
"""Fill the generated quick-facts block of docs-site/public/llms.txt.

The committed llms.txt keeps the `<!-- BEGIN/END GENERATED QUICK FACTS -->`
markers with an empty body, so no committed file holds repository counts. The
docs build fills the block in its checkout (`docs-site/scripts/generate-derived.sh`,
run as `prebuild`) from `verification_metrics.current_metrics()`.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Any

from property_utils import ROOT
from verification_metrics import current_metrics

LLMS_TXT = ROOT / "docs-site" / "public" / "llms.txt"
BEGIN = "<!-- BEGIN GENERATED QUICK FACTS -->"
END = "<!-- END GENERATED QUICK FACTS -->"
QUICK_FACTS_RE = re.compile(rf"{re.escape(BEGIN)}\n?(.*?){re.escape(END)}", re.DOTALL)


def render_quick_facts(data: dict[str, Any]) -> str:
    """Return the filled quick-facts block, markers included."""
    theorems = data["theorems"]
    proofs = data["proofs"]
    tests = data["tests"]
    codebase = data["codebase"]
    lean_version = data["toolchain"]["lean"].split(":")[-1].lstrip("v")
    contract_count = len(theorems["per_contract"])
    return (
        f"{BEGIN}\n"
        f"- **Language**: Lean {lean_version}\n"
        f"- **Core Size**: {codebase['core_lines']} lines\n"
        f"- **Verified Contracts**: {contract_count} ({', '.join(theorems['per_contract'].keys())})\n"
        f"- **Theorems**: {theorems['total']} across {theorems['categories']} categories, "
        f"{theorems['proven']} fully proven\n"
        f"- **Axioms**: {proofs['axioms']} custom Lean axioms (see docs/AXIOMS.md)\n"
        f"- **Tests**: {tests['foundry_functions']} Foundry tests, "
        f"{tests['property_functions']} property tests\n"
        f"- **Build**: `lake build` verifies all proofs\n"
        f"- **Repository**: https://github.com/lfglabs-dev/verity\n"
        f"{END}"
    )


def quick_facts_body(text: str) -> str | None:
    """Return the body between the quick-facts markers, or None without markers."""
    match = QUICK_FACTS_RE.search(text)
    return None if match is None else match.group(1)


def update_llms_txt(data: dict[str, Any], llms: Path = LLMS_TXT) -> bool:
    """Fill the quick-facts block of *llms* in place; return whether it changed."""
    text = llms.read_text(encoding="utf-8")
    if quick_facts_body(text) is None:
        raise ValueError(f"{llms}: missing GENERATED QUICK FACTS markers")
    new_text = QUICK_FACTS_RE.sub(lambda _m: render_quick_facts(data), text, count=1)
    if new_text == text:
        return False
    llms.write_text(new_text, encoding="utf-8")
    return True


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--write",
        action="store_true",
        help="Fill the block (the default action; accepted for explicit build scripts).",
    )
    parser.add_argument("--llms", type=Path, default=LLMS_TXT, help="llms.txt path to fill.")
    args = parser.parse_args(argv)
    if update_llms_txt(current_metrics(), args.llms):
        print(f"Filled quick facts in {args.llms}")


if __name__ == "__main__":
    try:
        main()
    except ValueError as exc:
        print(exc, file=sys.stderr)
        raise SystemExit(1) from exc
