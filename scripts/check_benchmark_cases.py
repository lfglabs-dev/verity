#!/usr/bin/env python3
"""Validate optional benchmark-case metadata.

Core Verity checkouts do not normally contain `Benchmark/`; downstream
benchmark repos may vendor or overlay `Benchmark/`, while the standalone
benchmark repository keeps metadata under `cases/`. When present, each
`case.yaml` is a publication boundary and must identify the upstream target
commit. If a case has `FormalAudit.lean`, it must not still be marked
`proof_status: not_started`.
"""

from __future__ import annotations

import re
from pathlib import Path

from property_utils import ROOT, report_errors

KEY_VALUE_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_-]*)\s*:\s*(.*?)\s*$")


def parse_case_yaml(path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        match = KEY_VALUE_RE.match(line)
        if match:
            values[match.group(1)] = match.group(2).strip().strip("\"'")
    return values


def check_benchmark_cases(root: Path = ROOT) -> list[str]:
    case_files = sorted((root / "Benchmark").glob("Cases/**/case.yaml"))
    case_files += sorted((root / "cases").glob("**/case.yaml"))
    if not case_files:
        return []

    errors: list[str] = []
    for case_yaml in case_files:
        metadata = parse_case_yaml(case_yaml)
        case_dir = case_yaml.parent
        rel = case_yaml.relative_to(root)

        if not metadata.get("upstream_commit"):
            errors.append(f"{rel}: missing upstream_commit")

        if (case_dir / "FormalAudit.lean").exists():
            proof_status = metadata.get("proof_status")
            if proof_status == "not_started":
                errors.append(f"{rel}: FormalAudit.lean exists but proof_status is not_started")

        audit_target_commit = metadata.get("audit_target_commit")
        if audit_target_commit is not None and not re.fullmatch(r"[0-9a-fA-F]{7,40}", audit_target_commit):
            errors.append(f"{rel}: audit_target_commit must be a 7-40 character git hex prefix")

    return errors


def main() -> int:
    case_files = sorted((ROOT / "Benchmark").glob("Cases/**/case.yaml"))
    case_files += sorted((ROOT / "cases").glob("**/case.yaml"))
    if not case_files:
        print("OK: no benchmark case metadata found; benchmark metadata check skipped")
        return 0

    errors = check_benchmark_cases()
    report_errors(errors, "Benchmark case metadata check failed")
    print(f"OK: benchmark metadata check passed for {len(case_files)} case.yaml file(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
