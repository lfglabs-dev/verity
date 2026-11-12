#!/usr/bin/env python3
"""Validate docs workflow trigger paths and CI runner documentation sync."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from property_utils import ROOT
from workflow_jobs import strip_yaml_inline_comment, unquote_yaml_scalar

DOCS_WORKFLOW = ROOT / ".github" / "workflows" / "docs.yml"
WORKFLOWS_DIR = ROOT / ".github" / "workflows"
CI_RUNNERS_DOC = ROOT / "docs" / "CI_RUNNERS.md"
EXPECTED_PATHS = [
    ".github/workflows/docs.yml",
    "docs-site/**",
]


def _normalize_path(raw: str) -> str:
    value = raw.strip()
    if value.startswith("- "):
        value = value[2:].strip()
    if (value.startswith("'") and value.endswith("'")) or (
        value.startswith('"') and value.endswith('"')
    ):
        value = value[1:-1]
    return value


def _extract_list_block(text: str, pattern: str, label: str, workflow_path: Path) -> list[str]:
    match = re.search(pattern, text, re.MULTILINE)
    if not match:
        raise ValueError(f"Could not locate {label} in {workflow_path}")
    block = match.group("block")
    entries = [_normalize_path(line) for line in block.splitlines() if line.strip()]
    if not entries:
        raise ValueError(f"{label} is empty in {workflow_path}")
    return entries


def _extract_push_paths(text: str, workflow_path: Path) -> list[str]:
    return _extract_list_block(
        text,
        r"^  push:\n(?:^    .*\n)*?^    paths:\n(?P<block>(?:^      - .*\n)+)",
        "on.push.paths",
        workflow_path,
    )


def _extract_pr_paths(text: str, workflow_path: Path) -> list[str]:
    return _extract_list_block(
        text,
        r"^  pull_request:\n(?:^    .*\n)*?^    paths:\n(?P<block>(?:^      - .*\n)+)",
        "on.pull_request.paths",
        workflow_path,
    )


def _compare_lists(name_a: str, a: list[str], name_b: str, b: list[str]) -> list[str]:
    if a == b:
        return []
    errors = [f"{name_a} does not match {name_b}."]
    max_len = max(len(a), len(b))
    for i in range(max_len):
        va = a[i] if i < len(a) else "<missing>"
        vb = b[i] if i < len(b) else "<missing>"
        if va != vb:
            errors.append(f"  idx {i}: {name_a}={va!r}, {name_b}={vb!r}")
    return errors


def _extract_runs_on_targets(text: str) -> list[str]:
    targets: list[str] = []
    for match in re.finditer(r"^\s*runs-on:\s*(?P<value>.+?)\s*$", text, re.MULTILINE):
        raw = strip_yaml_inline_comment(match.group("value"))
        if not raw:
            continue
        value = unquote_yaml_scalar(raw)
        if value.startswith("${{"):
            continue
        if value not in targets:
            targets.append(value)
    return targets


def _extract_workflow_runs_on_targets(workflows_dir: Path) -> list[str]:
    targets: list[str] = []
    for workflow_file in sorted(workflows_dir.glob("*.yml")):
        for target in _extract_runs_on_targets(workflow_file.read_text(encoding="utf-8")):
            if target not in targets:
                targets.append(target)
    return targets


def check_ci_runners_doc_sync(
    runners_doc_path: Path | None = None,
    workflows_dir: Path | None = None,
) -> list[str]:
    doc_path = runners_doc_path if runners_doc_path is not None else CI_RUNNERS_DOC
    wf_dir = workflows_dir if workflows_dir is not None else WORKFLOWS_DIR
    if not doc_path.exists():
        return []
    doc_targets = _extract_runs_on_targets(doc_path.read_text(encoding="utf-8"))
    if not doc_targets:
        return [f"No runs-on targets documented in {doc_path}"]
    workflow_targets = _extract_workflow_runs_on_targets(wf_dir)
    if not workflow_targets:
        return []
    return _compare_lists(
        "docs/CI_RUNNERS.md runs-on targets",
        sorted(doc_targets),
        "workflow runs-on targets",
        sorted(workflow_targets),
    )


def check_docs_workflow_sync(
    workflow_path: Path = DOCS_WORKFLOW,
    runners_doc_path: Path | None = None,
    workflows_dir: Path | None = None,
) -> int:
    text = workflow_path.read_text(encoding="utf-8")
    push_paths = _extract_push_paths(text, workflow_path)
    pr_paths = _extract_pr_paths(text, workflow_path)

    errors: list[str] = []
    errors.extend(_compare_lists("on.push.paths", push_paths, "expected paths", EXPECTED_PATHS))
    errors.extend(_compare_lists("on.pull_request.paths", pr_paths, "expected paths", EXPECTED_PATHS))
    errors.extend(_compare_lists("on.push.paths", push_paths, "on.pull_request.paths", pr_paths))
    if runners_doc_path is not None or workflows_dir is not None or workflow_path == DOCS_WORKFLOW:
        default_doc = (
            runners_doc_path
            if runners_doc_path is not None
            else (CI_RUNNERS_DOC if CI_RUNNERS_DOC.exists() else ROOT / "docs" / "CI_RUNNERS.md")
        )
        default_wf_dir = (
            workflows_dir if workflows_dir is not None else workflow_path.parent
        )
        errors.extend(check_ci_runners_doc_sync(default_doc, default_wf_dir))

    if errors:
        print("docs workflow sync failed:", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1

    print(f"docs workflow paths OK ({workflow_path})")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--workflow",
        default=str(DOCS_WORKFLOW.relative_to(ROOT)),
        help="Path to docs workflow relative to repo root (default: .github/workflows/docs.yml).",
    )
    args = parser.parse_args()
    return check_docs_workflow_sync(ROOT / args.workflow)


if __name__ == "__main__":
    raise SystemExit(main())
