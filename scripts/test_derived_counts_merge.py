#!/usr/bin/env python3
"""Two branches that each add a Foundry test merge without touching a committed count.

Builds a small scratch git repository holding the real ignore rules and the
committed sources the derived-count writers read (`docs/VERIFICATION_STATUS.md`,
`docs-site/llms.template.txt`). On each branch it adds one `test/*.t.sol`, runs
every derived-count writer with branch-specific metrics injected in place of
`current_metrics()`, and commits whatever git then sees. The merge must be
conflict-free and differ from the base only by the two added test files:
derived counts live in git-ignored build outputs, never in committed files.
"""

from __future__ import annotations

import contextlib
import io
import shutil
import subprocess
import sys
import tempfile
import unittest
from collections.abc import Callable
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import generate_verification_status
import sync_verification_status_doc
import update_doc_numbers
import verification_metrics

ROOT = SCRIPT_DIR.parent
COMMITTED_INPUTS = [
    ".gitignore",
    "docs-site/.gitignore",
    "docs/VERIFICATION_STATUS.md",
    "docs-site/llms.template.txt",
]


def _metrics(foundry_functions: int) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "theorems": {
            "total": 2, "categories": 1, "per_contract": {"Counter": 2}, "covered": 1,
            "coverage_percent": 50, "excluded": 1, "proven": 2, "stdlib": 0,
            "non_stdlib_total": 2,
        },
        "tests": {
            "foundry_functions": foundry_functions, "suites": foundry_functions,
            "property_functions": 1, "differential_total": 1,
        },
        "proofs": {"axioms": 0, "sorry": 0},
        "codebase": {"core_lines": 1, "example_contracts": 1},
        "toolchain": {"lean": "leanprover/lean4:v4.31.0", "solc": "0.8.33"},
    }


def _writers(repo: Path) -> list[Callable[[], None]]:
    """Every derived-count writer, pointed at *repo* (each writes where a contributor or build would)."""
    site = repo / "docs-site"
    return [
        lambda: generate_verification_status.main(
            ["--output", str(repo / "artifacts" / "verification_status.json")]
        ),
        lambda: sync_verification_status_doc.main([]),
        lambda: sync_verification_status_doc.main(
            ["--write", str(site / "public" / "verification-status.txt")]
        ),
        lambda: update_doc_numbers.main(
            ["--template", str(site / "llms.template.txt"), "--output", str(site / "public" / "llms.txt")]
        ),
    ]


def _git(repo: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", "-C", str(repo), "-c", "user.name=test", "-c", "user.email=test@example.invalid", *args],
        capture_output=True,
        text=True,
        check=check,
    )


class DerivedCountsMergeTests(unittest.TestCase):
    def _inject(self, module: Any, name: str, value: Any) -> None:
        self.addCleanup(setattr, module, name, getattr(module, name))
        setattr(module, name, value)

    def _branch_adding_test(self, repo: Path, tag: str, foundry_functions: int) -> None:
        _git(repo, "checkout", "-q", "-b", f"add-{tag}", "base")
        (repo / "test" / f"DerivedCountsMerge{tag}.t.sol").write_text(
            f"contract DerivedCountsMerge{tag}Test {{ function test_{tag}() public pure {{}} }}\n",
            encoding="utf-8",
        )
        metrics = _metrics(foundry_functions)
        self._inject(verification_metrics, "collect_metrics", lambda: metrics)
        self._inject(sync_verification_status_doc, "current_metrics", lambda: metrics)
        self._inject(update_doc_numbers, "current_metrics", lambda: metrics)
        with contextlib.redirect_stdout(io.StringIO()):
            for writer in _writers(repo):
                writer()
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "-m", f"add test {tag}")

    def test_two_branches_adding_tests_merge_cleanly(self) -> None:
        if shutil.which("git") is None:
            self.skipTest("needs git")
        with tempfile.TemporaryDirectory() as tmpdir:
            repo = Path(tmpdir) / "repo"
            for rel in COMMITTED_INPUTS:
                (repo / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(ROOT / rel, repo / rel)
            (repo / "test").mkdir()
            (repo / "test" / "Base.t.sol").write_text("contract BaseTest {}\n", encoding="utf-8")
            _git(repo, "init", "-q", "-b", "base")
            _git(repo, "add", "-A")
            _git(repo, "commit", "-q", "-m", "base")

            self._inject(sync_verification_status_doc, "STATUS_DOC", repo / "docs" / "VERIFICATION_STATUS.md")
            self._inject(sync_verification_status_doc, "collect_covered", lambda: {"Counter": {"a"}})
            self._inject(sync_verification_status_doc, "load_exclusions", lambda: {"Counter": {"b"}})
            self._branch_adding_test(repo, "A", 11)
            self._branch_adding_test(repo, "B", 12)

            self.assertIn("12 Foundry tests", (repo / "docs-site" / "public" / "llms.txt").read_text())
            merge = _git(repo, "merge", "--no-edit", "add-A", check=False)
            self.assertEqual(merge.returncode, 0, merge.stdout + merge.stderr)
            changed = _git(repo, "diff", "--name-only", "base", "HEAD").stdout.split()
            self.assertEqual(
                sorted(changed),
                ["test/DerivedCountsMergeA.t.sol", "test/DerivedCountsMergeB.t.sol"],
                "a derived-count writer changed a committed file",
            )


if __name__ == "__main__":
    unittest.main()
