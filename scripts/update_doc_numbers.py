#!/usr/bin/env python3
"""Render docs-site/public/llms.txt from docs-site/llms.template.txt.

The committed template keeps the `<!-- BEGIN/END GENERATED QUICK FACTS -->`
markers with an empty body, so no committed file holds repository counts. The
docs build (`docs-site/scripts/generate-derived.sh`, run as `prebuild`) writes
the git-ignored `public/llms.txt` with the block filled from
`verification_metrics.current_metrics()`.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Any

from property_utils import ROOT
from verification_metrics import current_metrics

LLMS_TEMPLATE = ROOT / "docs-site" / "llms.template.txt"
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


def render_llms_txt(template: str, data: dict[str, Any], source: Path | str = LLMS_TEMPLATE) -> str:
    """Return *template* with its quick-facts block filled from *data*."""
    if quick_facts_body(template) is None:
        raise ValueError(f"{source}: missing GENERATED QUICK FACTS markers")
    return QUICK_FACTS_RE.sub(lambda _m: render_quick_facts(data), template, count=1)


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--write",
        action="store_true",
        help="Write the output (the default action; accepted for explicit build scripts).",
    )
    parser.add_argument("--template", type=Path, default=LLMS_TEMPLATE, help="Committed template.")
    parser.add_argument("--output", type=Path, default=LLMS_TXT, help="Rendered llms.txt (git-ignored).")
    args = parser.parse_args(argv)
    rendered = render_llms_txt(args.template.read_text(encoding="utf-8"), current_metrics(), args.template)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")


if __name__ == "__main__":
    try:
        main()
    except ValueError as exc:
        print(exc, file=sys.stderr)
        raise SystemExit(1) from exc
