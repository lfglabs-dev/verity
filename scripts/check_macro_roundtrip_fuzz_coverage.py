#!/usr/bin/env python3
"""Enforce generated Foundry fuzz coverage for every macro contract."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

import check_macro_property_test_generation as property_generation
import generate_macro_property_tests as generator
from property_utils import ROOT

def _check_coverage(sources: list[Path], fuzz_artifacts: Path) -> int:
    declared = set(generator.collect_contracts(sources))
    covered = {
        path.name.removeprefix("Property").removesuffix(".t.sol")
        for path in fuzz_artifacts.glob("Property*.t.sol")
    }
    expected = declared - property_generation.EXCLUDED_CONTRACTS
    failures = {
        "missing fuzz artifact": sorted(expected - covered),
        "unknown fuzz artifact": sorted(covered - expected),
    }
    if declared and not any(failures.values()):
        print("macro round-trip fuzz coverage OK")
        return 0
    print("macro round-trip fuzz coverage check failed:", file=sys.stderr)
    for label, names in failures.items():
        for name in names:
            print(f"  {label}: {name}", file=sys.stderr)
    if not declared:
        print("  no verity_contract declarations found", file=sys.stderr)
    return 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contracts-dir", default="Contracts")
    parser.add_argument("--fuzz-artifacts", default="artifacts/macro_property_tests")
    args = parser.parse_args(argv)
    contracts_dir = ROOT / args.contracts_dir
    fuzz_artifacts = ROOT / args.fuzz_artifacts
    if not contracts_dir.is_dir() or not fuzz_artifacts.is_dir():
        print("macro round-trip fuzz coverage inputs not found", file=sys.stderr)
        return 1
    sources = generator.discover_macro_contract_sources(contracts_dir)
    return _check_coverage(sources, fuzz_artifacts)


if __name__ == "__main__":
    raise SystemExit(main())
