#!/usr/bin/env python3
"""Generate the machine-readable trust-surface report.

Emits `artifacts/trust_surface_report.json`, the JSON counterpart of the
prose trust registry validated by `check_trust_surface_registry.py`: the
non-axiom trusted mechanisms (`native_decide`, `@[implemented_by]`,
`partial def`), the explicit ECM assumption strings with their source
locations, and the Lean 4.31 kernel string-fact boundary.  Downstream
consumers (dashboards, audit tooling, downstream repos) get the same
inventory the checker enforces, without scraping checker stdout.

Usage:
    python3 scripts/generate_trust_surface_report.py
    python3 scripts/generate_trust_surface_report.py --check
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from check_trust_surface_registry import (
    LEAN431_STRING_FACTS,
    LEAN431_STRING_THEOREMS,
    check_lean431_string_kernel_facts,
    collect_trust_surface,
)
from property_utils import ROOT

DEFAULT_OUTPUT = ROOT / "artifacts" / "trust_surface_report.json"


def build_report() -> dict:
    mechanisms, ecm_axioms = collect_trust_surface()
    lean431_errors = check_lean431_string_kernel_facts()
    return {
        "schema_version": 1,
        "generator": "scripts/generate_trust_surface_report.py",
        "mechanisms": {name: count for name, count in sorted(mechanisms.items())},
        "ecm_assumptions": [
            {"name": name, "file": rel, "line": line}
            for name, (rel, line) in sorted(ecm_axioms.items())
        ],
        "ecm_assumption_count": len(ecm_axioms),
        "lean431_string_kernel_facts": {
            "module": str(LEAN431_STRING_FACTS),
            "theorems": list(LEAN431_STRING_THEOREMS),
            "kernel_only": not lean431_errors,
        },
        "notes": (
            "native_decide trusts Lean.ofReduceBool or Lean 4.31 generated "
            "per-proof native_decide axioms + Lean.trustCompiler. Prose "
            "registry: AXIOMS.md, TRUST_ASSUMPTIONS.md (enforced by "
            "scripts/check_trust_surface_registry.py)."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Output artifact path (default: artifacts/trust_surface_report.json)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail if output artifact is missing or stale",
    )
    args = parser.parse_args()

    rendered = json.dumps(build_report(), sort_keys=True, indent=2) + "\n"

    if args.check:
        if not args.output.exists():
            print(f"Missing trust-surface artifact: {args.output}", file=sys.stderr)
            return 1
        if args.output.read_text(encoding="utf-8") != rendered:
            print(
                "Trust-surface report is stale. Regenerate with:\n"
                "  python3 scripts/generate_trust_surface_report.py",
                file=sys.stderr,
            )
            return 1
        print(f"Trust-surface report is up to date: {args.output}")
        return 0

    args.output.write_text(rendered, encoding="utf-8")
    print(f"Wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
