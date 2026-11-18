#!/usr/bin/env python3
"""Tests for rebase_pr_onto_main on throwaway git repositories (no Lean)."""

from __future__ import annotations

import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
import unittest.mock
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import rebase_pr_onto_main as tool

# Fake generator: gen.txt is src.txt upper-cased; `--check` fails on drift.
FAKE_GENERATOR = """\
import sys
from pathlib import Path
want = Path("src.txt").read_text().upper()
if sys.argv[1:] == ["--check"]:
    sys.exit(0 if Path("gen.txt").read_text() == want else 1)
Path("gen.txt").write_text(want)
"""

GIT_ENV = {
    "GIT_AUTHOR_NAME": "Test",
    "GIT_AUTHOR_EMAIL": "test@example.com",
    "GIT_COMMITTER_NAME": "Test",
    "GIT_COMMITTER_EMAIL": "test@example.com",
    "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_CONFIG_NOSYSTEM": "1",
}


class RebaseToolTests(unittest.TestCase):
    def setUp(self) -> None:
        self._env = unittest.mock.patch.dict(os.environ, GIT_ENV)
        self._env.start()
        self.tmp = Path(tempfile.mkdtemp())
        generator = self.tmp / "fake_gen.py"
        generator.write_text(FAKE_GENERATOR)
        self.config = tool.Config(
            generators=(tool.Generator(("gen.txt",), (sys.executable, str(generator))),),
            append_only={"list.txt": r"^item [a-z0-9]+$"},
            deleted_on_base=("artifacts/*",),
        )
        self.origin = self.tmp / "origin.git"
        self.repo = self.tmp / "work"
        self.git_at(self.tmp, "init", "-q", "--bare", "-b", "main", str(self.origin))
        self.git_at(self.tmp, "clone", "-q", str(self.origin), str(self.repo))
        self.git("checkout", "-q", "-b", "main")
        self.write(
            {
                "list.txt": "header\nitem a\nitem b\n",
                "src.txt": "hello\n",
                "gen.txt": "HELLO\n",
                "code.txt": "x = 1\n",
                "artifacts/status.json": "{}\n",
            }
        )
        self.commit("initial")
        self.git("push", "-q", "-u", "origin", "main")
        self.git("checkout", "-q", "-b", "pr")

    def tearDown(self) -> None:
        self._env.stop()
        subprocess.run(["rm", "-rf", str(self.tmp)], check=True)

    # helpers ---------------------------------------------------------------
    def git_at(self, cwd: Path, *args: str) -> str:
        proc = subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True)
        if proc.returncode != 0:
            raise AssertionError(f"git {args} failed: {proc.stderr}")
        return proc.stdout.strip()

    def git(self, *args: str) -> str:
        return self.git_at(self.repo, *args)

    def write(self, files: dict[str, str]) -> None:
        for name, text in files.items():
            path = self.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)

    def commit(self, message: str) -> None:
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)

    def push_pr(self) -> None:
        self.git("push", "-q", "-u", "origin", "pr")

    def advance_main(self, files: dict[str, str], delete: tuple[str, ...] = ()) -> None:
        """Commit on main (via the origin) while keeping `pr` checked out."""
        self.git("checkout", "-q", "main")
        self.write(files)
        for name in delete:
            self.git("rm", "-q", name)
        self.commit("main moves")
        self.git("push", "-q", "origin", "main")
        self.git("checkout", "-q", "pr")

    def run_tool(self, *args: str) -> tuple[int, dict]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = tool.main(["--repo", str(self.repo), "--json", *args], config=self.config)
        return code, json.loads(out.getvalue())

    def in_rebase(self) -> bool:
        return Git(self.repo).rebase_dir() is not None

    # guard -------------------------------------------------------------------
    def test_guard_refuses_when_local_differs_from_upstream(self) -> None:
        self.write({"code.txt": "x = 2\n"})
        self.commit("pr change")
        self.push_pr()
        self.write({"code.txt": "x = 3\n"})
        self.commit("unpushed local work")
        before = self.git("rev-parse", "HEAD")
        code, out = self.run_tool()
        self.assertEqual(code, 5)
        self.assertIn("differs from its upstream", out["error"])
        self.assertEqual(self.git("rev-parse", "HEAD"), before)
        self.assertFalse(self.in_rebase())

    def test_guard_refuses_dirty_tree(self) -> None:
        self.push_pr()
        self.write({"code.txt": "dirty\n"})
        code, out = self.run_tool()
        self.assertEqual(code, 5)
        self.assertIn("tracked changes", out["error"])
        self.assertEqual((self.repo / "code.txt").read_text(), "dirty\n")

    # conflict categories -----------------------------------------------------
    def test_union_resolves_append_only_list(self) -> None:
        self.write({"list.txt": "header\nitem a\nitem b\nitem pr\n"})
        self.commit("pr adds item")
        self.push_pr()
        self.advance_main({"list.txt": "header\nitem a\nitem b\nitem main\n"})
        code, out = self.run_tool()
        self.assertEqual(code, 0, out)
        self.assertEqual(out["union"], ["list.txt"])
        self.assertEqual(
            (self.repo / "list.txt").read_text(), "header\nitem a\nitem b\nitem main\nitem pr\n"
        )
        self.assertEqual(out["ahead"], 1)

    def test_union_refuses_non_list_lines(self) -> None:
        self.write({"list.txt": "header pr\nitem a\nitem b\n"})
        self.commit("pr edits header")
        self.push_pr()
        self.advance_main({"list.txt": "header main\nitem a\nitem b\n"})
        code, out = self.run_tool()
        self.assertEqual(code, 3)
        self.assertIn("not a list entry", out["conflicts"][0])
        self.assertTrue(self.in_rebase())

    def test_modify_delete_takes_deletion(self) -> None:
        self.write({"artifacts/status.json": '{"pr": 1}\n'})
        self.commit("pr touches artifact")
        self.push_pr()
        self.advance_main({}, delete=("artifacts/status.json",))
        code, out = self.run_tool()
        self.assertEqual(code, 0, out)
        self.assertEqual(out["deleted"], ["artifacts/status.json"])
        self.assertFalse((self.repo / "artifacts/status.json").exists())
        self.assertEqual(self.git("ls-files", "artifacts"), "")

    def test_real_conflict_stops_with_exit_3(self) -> None:
        self.write({"code.txt": "x = pr\n"})
        self.commit("pr change")
        self.push_pr()
        self.advance_main({"code.txt": "x = main\n"})
        code, out = self.run_tool()
        self.assertEqual(code, 3)
        self.assertEqual(out["conflicts"], ["code.txt"])
        self.assertTrue(self.in_rebase())

    def test_regenerate_commit_skipped_and_generated_file_regenerated(self) -> None:
        self.write({"src.txt": "hello pr\n"})
        self.commit("pr changes source")
        self.write({"gen.txt": "HELLO PR\n"})
        self.commit("chore: regenerate generated files")
        self.push_pr()
        self.advance_main({"code.txt": "x = main\n", "gen.txt": "HELLO MAIN\n"})
        old = self.git("rev-parse", "HEAD")
        code, out = self.run_tool()
        self.assertEqual(code, 0, out)
        self.assertEqual(len(out["skipped"]), 1)
        self.assertEqual(out["regenerated"], ["gen.txt"])
        self.assertEqual(out["old_sha"], old)
        self.assertEqual((self.repo / "gen.txt").read_text(), "HELLO PR\n")
        subjects = self.git("log", "--format=%s", "origin/main..HEAD").splitlines()
        self.assertEqual(
            subjects,
            ["chore: regenerate generated files after rebasing onto origin/main", "pr changes source"],
        )
        self.assertEqual(self.git("log", "-1", "--format=%an"), "Test")
        self.assertIn("git push --force-with-lease origin pr", out["push_command"])

    def test_generated_conflict_takes_base_then_regenerates(self) -> None:
        self.write({"src.txt": "hello pr\n", "gen.txt": "HELLO PR\n"})
        self.commit("pr changes source and output")
        self.push_pr()
        self.advance_main({"gen.txt": "HELLO MAIN\n"})
        code, out = self.run_tool()
        self.assertEqual(code, 0, out)
        self.assertEqual(out["generated"], ["gen.txt"])
        # The replayed PR commit carries the base's version; the final commit regenerates it.
        self.assertEqual(self.git("show", "HEAD~1:gen.txt"), "HELLO MAIN")
        self.assertEqual(out["regenerated"], ["gen.txt"])
        self.assertEqual((self.repo / "gen.txt").read_text(), "HELLO PR\n")

    def test_resumes_rebase_in_progress(self) -> None:
        self.write({"code.txt": "x = pr\n"})
        self.commit("pr change")
        self.write({"list.txt": "header\nitem a\nitem b\nitem pr\n"})
        self.commit("pr adds item")
        self.push_pr()
        self.advance_main(
            {"code.txt": "x = main\n", "list.txt": "header\nitem a\nitem b\nitem main\n"}
        )
        code, _ = self.run_tool()
        self.assertEqual(code, 3)
        self.write({"code.txt": "x = both\n"})
        self.git("add", "code.txt")
        code, out = self.run_tool()
        self.assertEqual(code, 0, out)
        self.assertFalse(self.in_rebase())
        self.assertEqual(out["union"], ["list.txt"])
        self.assertEqual(out["ahead"], 2)
        self.assertEqual((self.repo / "code.txt").read_text(), "x = both\n")

    def test_text_output_is_one_line(self) -> None:
        self.push_pr()
        self.advance_main({"code.txt": "x = main\n"})
        out = io.StringIO()
        with redirect_stdout(out):
            code = tool.main(["--repo", str(self.repo)], config=self.config)
        self.assertEqual(code, 0)
        self.assertEqual(len(out.getvalue().splitlines()), 1)
        self.assertIn("pr: ", out.getvalue())


class UnionMergeTests(unittest.TestCase):
    def test_duplicate_in_region_is_refused(self) -> None:
        merged, reason = tool.union_merge(
            "item a\n", "item a\nitem b\nitem c\n", "item a\nitem c\nitem b\n", r"^item \w+$"
        )
        self.assertIsNone(merged)
        self.assertIn("duplicate", reason)


Git = tool.Git

if __name__ == "__main__":
    unittest.main()
