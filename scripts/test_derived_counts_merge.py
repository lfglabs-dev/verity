#!/usr/bin/env python3
"""Two branches that each add a Foundry test merge without touching a committed count.

Copies the current checkout into a scratch git repository, adds one
`test/*.t.sol` per branch, runs every derived-count writer on each branch,
commits whatever git then sees, and merges the branches. The merge must be
conflict-free and must differ from the base only by the two added test files:
derived counts live in git-ignored build outputs, never in committed files.
"""

from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent

# Commands that write derived counts, run from the repository root. All must
# write only git-ignored paths.
DERIVED_COUNT_WRITERS: list[list[str]] = [
    ["scripts/generate_verification_status.py"],
    ["scripts/sync_verification_status_doc.py", "--write", "docs-site/public/verification-status.txt"],
]

TEST_TEMPLATE = """// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

contract DerivedCountsMerge{tag}Test {{
    function test_derivedCountsMerge{tag}() public pure {{}}
}}
"""


def _git(repo: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", "-C", str(repo), "-c", "user.name=test", "-c", "user.email=test@example.invalid", *args],
        capture_output=True,
        text=True,
        check=check,
    )


def _copy_checkout(dest: Path) -> None:
    listed = _git(ROOT, "ls-files", "-z", "--cached", "--others", "--exclude-standard").stdout
    for rel in filter(None, listed.split("\0")):
        src = ROOT / rel
        if not src.is_file():
            continue
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, target)


class DerivedCountsMergeTests(unittest.TestCase):
    def _branch_adding_test(self, repo: Path, tag: str) -> None:
        _git(repo, "checkout", "-q", "-b", f"add-{tag}", "base")
        (repo / "test" / f"DerivedCountsMerge{tag}.t.sol").write_text(
            TEST_TEMPLATE.format(tag=tag), encoding="utf-8"
        )
        for writer in DERIVED_COUNT_WRITERS:
            result = subprocess.run(
                [sys.executable, *writer], cwd=repo, capture_output=True, text=True, check=False
            )
            self.assertEqual(result.returncode, 0, f"{writer}: {result.stderr}")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "-m", f"add test {tag}")

    def test_two_branches_adding_tests_merge_cleanly(self) -> None:
        if not (ROOT / ".git").exists() or shutil.which("git") is None:
            self.skipTest("needs a git checkout")
        with tempfile.TemporaryDirectory() as tmpdir:
            repo = Path(tmpdir) / "repo"
            repo.mkdir()
            _copy_checkout(repo)
            _git(repo, "init", "-q", "-b", "base")
            _git(repo, "add", "-A")
            _git(repo, "commit", "-q", "-m", "base")

            self._branch_adding_test(repo, "A")
            self._branch_adding_test(repo, "B")

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
