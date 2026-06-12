#!/usr/bin/env python3
"""Consolidated property manifest / coverage pipeline (Cluster C).

Replaces the five thin property_utils consumers:
  check_property_manifest.py       -> `check --only manifest`
  check_property_coverage.py       -> `check --only coverage`
  check_property_manifest_sync.py  -> `check --only lean-sync`
  extract_property_manifest.py     -> `extract`
  report_property_coverage.py      -> `report`

`check` with no `--only` runs manifest + coverage + lean-sync in one pass
(single manifest load instead of three). Exit codes and messages are
identical to the legacy scripts.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from property_utils import (
    FILE_RE,
    ROOT,
    TEST_DIR,
    collect_covered,
    extract_manifest_from_proofs,
    extract_property_names,
    load_exclusions,
    load_manifest,
    report_errors,
)

MANIFEST_OUTPUT = ROOT / "test" / "property_manifest.json"

CHECKS = ("manifest", "coverage", "lean-sync")


def check_manifest(manifest: dict[str, set[str]]) -> None:
    """Property test files reference valid theorems from the manifest."""
    missing: list[str] = []
    empty_tags: list[str] = []

    for path in sorted(TEST_DIR.glob("Property*.t.sol")):
        match = FILE_RE.match(path.name)
        if not match:
            continue
        contract = match.group(1)
        if contract not in manifest:
            missing.append(f"{path}: no manifest entry for {contract}")
            continue
        names = extract_property_names(path)
        if not names:
            empty_tags.append(str(path))
            continue
        for name in names:
            if name not in manifest[contract]:
                missing.append(f"{path}: property '{name}' not found in manifest for {contract}")

    if empty_tags:
        missing.append("Property files missing Property tags: " + ", ".join(empty_tags))

    report_errors(missing, "Property manifest check failed")

    print("Property manifest check passed.")


def check_coverage(manifest: dict[str, set[str]]) -> None:
    """All theorems in the manifest have property tests (or are excluded)."""
    exclusions = load_exclusions()
    covered = collect_covered()

    errors: list[str] = []

    for contract, names in exclusions.items():
        if contract not in manifest:
            errors.append(f"Exclusion contract not in manifest: {contract}")
            continue
        unknown = names - manifest[contract]
        if unknown:
            errors.append(
                f"Exclusions for {contract} include unknown theorem(s): {', '.join(sorted(unknown))}"
            )

    for contract, names in manifest.items():
        covered_names = covered.get(contract, set())
        excluded_names = exclusions.get(contract, set())
        stale = covered_names & excluded_names
        if stale:
            errors.append(
                f"{contract}: exclusions list covered theorem(s): {', '.join(sorted(stale))}"
            )
        missing = names - covered_names - excluded_names
        if missing:
            errors.append(
                f"{contract}: missing property tests for {len(missing)} theorem(s): {', '.join(sorted(missing))}"
            )

    report_errors(errors, "Property coverage check failed")
    print("Property coverage check passed.")


def check_lean_sync(manifest: dict[str, set[str]]) -> None:
    """property_manifest.json is in sync with actual Lean proofs."""
    expected = extract_manifest_from_proofs()
    actual = {k: sorted(v) for k, v in manifest.items()}

    problems: list[str] = []
    for contract in sorted(set(expected.keys()) | set(actual.keys())):
        exp = expected.get(contract, [])
        act = actual.get(contract, [])
        if not exp and act:
            problems.append(f"{contract}: manifest has entries but proofs missing")
            continue
        if exp and not act:
            problems.append(f"{contract}: missing manifest entries (run extract_property_manifest.py)")
            continue
        missing = sorted(set(exp) - set(act))
        extra = sorted(set(act) - set(exp))
        if missing:
            problems.append(f"{contract}: missing {len(missing)} theorem(s) in manifest: {', '.join(missing)}")
        if extra:
            problems.append(f"{contract}: {len(extra)} extra theorem(s) in manifest: {', '.join(extra)}")

    report_errors(problems, "Property manifest out of sync (run extract_property_manifest.py)")
    print("Property manifest sync check passed.")


def run_check(only: list[str] | None) -> int:
    selected = only if only else list(CHECKS)
    manifest = load_manifest()
    runners = {
        "manifest": check_manifest,
        "coverage": check_coverage,
        "lean-sync": check_lean_sync,
    }
    for name in CHECKS:
        if name in selected:
            runners[name](manifest)
    return 0


def run_extract() -> int:
    manifest = extract_manifest_from_proofs()
    MANIFEST_OUTPUT.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


def run_report(fmt: str, fail_below: float | None) -> int:
    manifest = load_manifest()
    exclusions = load_exclusions()
    covered = collect_covered()

    # Calculate statistics per contract
    stats = {}
    total_properties = 0
    total_covered = 0
    total_exclusions = 0

    for contract in sorted(manifest.keys()):
        properties = manifest[contract]
        covered_props = covered.get(contract, set())
        excluded_props = exclusions.get(contract, set())

        count_total = len(properties)
        count_covered = len(covered_props)
        count_excluded = len(excluded_props)
        count_missing = count_total - count_covered - count_excluded
        coverage_pct = (count_covered / count_total * 100) if count_total > 0 else 0

        stats[contract] = {
            "total": count_total,
            "covered": count_covered,
            "excluded": count_excluded,
            "missing": count_missing,
            "coverage": coverage_pct,
        }

        total_properties += count_total
        total_covered += count_covered
        total_exclusions += count_excluded

    overall_coverage = (
        (total_covered / total_properties * 100) if total_properties > 0 else 0
    )

    # Output in requested format
    if fmt == "text":
        print_text_report(stats, total_properties, total_covered, total_exclusions, overall_coverage)
    elif fmt == "markdown":
        print_markdown_report(stats, total_properties, total_covered, total_exclusions, overall_coverage)
    elif fmt == "json":
        total_missing = total_properties - total_covered - total_exclusions
        report = {
            "overall": {
                "total": total_properties,
                "covered": total_covered,
                "excluded": total_exclusions,
                "missing": total_missing,
                "coverage": round(overall_coverage, 2),
            },
            "contracts": {
                contract: {
                    "total": s["total"],
                    "covered": s["covered"],
                    "excluded": s["excluded"],
                    "missing": s["missing"],
                    "coverage": round(s["coverage"], 2),
                }
                for contract, s in stats.items()
            },
        }
        print(json.dumps(report, indent=2))

    # Check coverage threshold
    if fail_below is not None and overall_coverage < fail_below:
        print(
            f"\n❌ Coverage {overall_coverage:.1f}% is below threshold {fail_below}%",
            file=sys.stderr,
        )
        return 1
    return 0


def print_text_report(stats, total_properties, total_covered, total_exclusions, overall_coverage):
    """Print coverage report in text format."""
    print("=" * 80)
    print("PROPERTY TEST COVERAGE REPORT")
    print("=" * 80)
    print()

    # Contract-by-contract breakdown
    for contract, s in stats.items():
        status_icon = "✅" if s["missing"] == 0 else "⚠️" if s["coverage"] >= 80 else "❌"
        print(f"{status_icon} {contract}")
        print(f"   Total:      {s['total']:3d} properties")
        print(f"   Covered:    {s['covered']:3d} ({s['coverage']:5.1f}%)")
        print(f"   Excluded:   {s['excluded']:3d} (proof-only)")
        if s["missing"] > 0:
            print(f"   Missing:    {s['missing']:3d} ⚠️")
        print()

    # Overall statistics
    print("=" * 80)
    print("OVERALL STATISTICS")
    print("=" * 80)
    print(f"Total Properties:     {total_properties:4d}")
    print(f"Covered Properties:   {total_covered:4d} ({overall_coverage:5.1f}%)")
    print(f"Excluded Properties:  {total_exclusions:4d} (proof-only)")
    print(f"Missing Properties:   {total_properties - total_covered - total_exclusions:4d}")
    print()

    # Summary
    if total_properties - total_covered - total_exclusions == 0:
        print("✅ All addressable properties are covered!")
    else:
        print(f"⚠️  {total_properties - total_covered - total_exclusions} properties still need coverage")


def print_markdown_report(stats, total_properties, total_covered, total_exclusions, overall_coverage):
    """Print coverage report in markdown format."""
    print("# Property Test Coverage Report")
    print()
    print("## Summary")
    print()
    print(f"- **Total Properties**: {total_properties}")
    print(f"- **Covered**: {total_covered} ({overall_coverage:.1f}%)")
    print(f"- **Excluded**: {total_exclusions} (proof-only)")
    print(f"- **Missing**: {total_properties - total_covered - total_exclusions}")
    print()
    print("## Contract Breakdown")
    print()
    print("| Contract | Total | Covered | Coverage | Excluded | Missing |")
    print("|----------|-------|---------|----------|----------|---------|")

    for contract, s in stats.items():
        status = "✅" if s["missing"] == 0 else "⚠️" if s["coverage"] >= 80 else "❌"
        print(
            f"| {status} {contract} | {s['total']} | {s['covered']} | "
            f"{s['coverage']:.1f}% | {s['excluded']} | {s['missing']} |"
        )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)

    check_parser = sub.add_parser("check", help="Run manifest/coverage/lean-sync checks")
    check_parser.add_argument(
        "--only",
        action="append",
        choices=CHECKS,
        help="Run only the selected check(s). Can be repeated.",
    )

    sub.add_parser("extract", help="Regenerate test/property_manifest.json from Lean proofs")

    report_parser = sub.add_parser("report", help="Coverage statistics report")
    report_parser.add_argument(
        "--format",
        choices=["text", "markdown", "json"],
        default="text",
        help="Output format (default: text)",
    )
    report_parser.add_argument(
        "--fail-below",
        type=float,
        help="Exit with code 1 if overall coverage is below this percentage",
    )

    args = parser.parse_args(argv)

    if args.command == "check":
        return run_check(args.only)
    if args.command == "extract":
        return run_extract()
    return run_report(args.format, args.fail_below)


if __name__ == "__main__":
    raise SystemExit(main())
