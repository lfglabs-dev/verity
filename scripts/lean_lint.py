#!/usr/bin/env python3
"""Consolidated Lean structure/hygiene lint runner (Cluster E).

One entrypoint over the lint rule modules, generalizing the
check_compiler_boundaries.py dispatcher pattern with `--only` / `--skip` /
`--list`. Each rule module keeps its own logic, output, and exit code; this
runner only selects and sequences them, so behavior is exactly equivalent to
invoking the legacy scripts directly (in particular check_lean_hygiene.py,
the sorry/native_decide gate, is invoked unmodified).

Extra arguments after `--` are forwarded to the rule (single `--only` only),
e.g. `lean_lint.py --only proof_length -- --format=markdown`.
"""

from __future__ import annotations

import argparse
import importlib
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

# rule name -> module implementing it (module.main() runs the legacy checker)
RULES: dict[str, str] = {
    "contract_structure": "check_contract_structure",
    "paths": "check_paths",
    "compilationmodel_split": "check_compilationmodel_split",
    "axioms": "check_axioms",
    "trust_surface_registry": "check_trust_surface_registry",
    "storage_layout": "check_storage_layout",
    "lean_hygiene": "check_lean_hygiene",
    "split_compiler_test_artifacts": "check_split_compiler_test_artifacts",
    "rewrite_proof_metadata": "check_rewrite_proof_metadata",
    "proof_length": "check_proof_length",
}


def run_rule(name: str, extra_args: list[str] | None = None) -> int:
    """Run one rule module's main(), preserving its exact exit semantics."""
    module_name = RULES[name]
    module = importlib.import_module(module_name)
    saved_argv = sys.argv
    sys.argv = [f"scripts/{module_name}.py", *(extra_args or [])]
    try:
        rc = module.main()
    except SystemExit as exc:
        code = exc.code
        rc = 0 if code is None else (code if isinstance(code, int) else 1)
    finally:
        sys.argv = saved_argv
    return 0 if rc is None else rc


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--only",
        action="append",
        choices=sorted(RULES.keys()),
        help="Run only the selected rule(s). Can be repeated.",
    )
    parser.add_argument(
        "--skip",
        action="append",
        choices=sorted(RULES.keys()),
        default=[],
        help="Skip the selected rule(s). Can be repeated.",
    )
    parser.add_argument("--list", action="store_true", help="List available rules")
    parser.add_argument(
        "rule_args",
        nargs="*",
        help="Arguments after `--` forwarded to the rule (requires exactly one --only)",
    )
    args = parser.parse_args(argv)

    if args.list:
        for name in RULES:
            print(name)
        return 0

    selected = [
        name
        for name in RULES
        if (args.only is None or name in args.only) and name not in args.skip
    ]

    if args.rule_args and len(selected) != 1:
        parser.error("forwarded rule arguments require exactly one --only rule")

    for name in selected:
        rc = run_rule(name, args.rule_args)
        if rc != 0:
            return rc
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
