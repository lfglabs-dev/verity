#!/usr/bin/env python3
"""Rebase a PR branch onto the base branch, resolving the routine conflicts.

Usage:
  python3 scripts/rebase_pr_onto_main.py [--base origin/main] [--branch NAME] [--json]

PR branches in this repository conflict with main mostly on files nobody
edits by hand: generated files (``PrintAxioms.lean``, ``artifacts/*.json``)
and append-only lists (smoke module lists, smoke imports). This tool rebases
the branch and resolves exactly those conflicts, per the tables below:

  * generated file   -> take the base's side during the rebase, regenerate once
                        at the end (one "chore: regenerate ..." commit);
  * append-only list -> ``git merge-file --union``, only when every line of every
                        conflict hunk is a list entry and the union has no
                        duplicate line;
  * modify/delete    -> a file the base deleted and the PR modified is deleted
                        when it matches ``DELETED_ON_BASE_PATTERNS``;
  * anything else    -> stop with exit 3, leaving the rebase in progress.

Commits whose subject starts with "chore: regenerate" are dropped, since the
regeneration happens once at the end.

Guard: the tool refuses (exit 5) when the working tree has tracked changes, or
when the local branch differs from its upstream (``@{u}``), e.g. after a
finished but unpushed rebase or conflict resolution. It never resets the
branch and never pushes. If a rebase is already in progress (for instance
after you fixed the conflicts of an exit-3 stop), it resumes that rebase.

Exit codes: 0 rebased, 1 git or generator failure, 3 unresolved conflicts
(rebase left in progress), 4 a generator ``--check`` still fails after
regeneration, 5 refused by the guard.
"""

from __future__ import annotations

import argparse
import fnmatch
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Sequence

SKIP_SUBJECT_PREFIX = "chore: regenerate"


@dataclass(frozen=True)
class Generator:
    """A committed generated file set and the commands that produce/check it."""

    outputs: tuple[str, ...]
    command: tuple[str, ...]

    @property
    def check_command(self) -> tuple[str, ...]:
        return (*self.command, "--check")


# Committed generated files, each with the generator that `make check` runs
# with `--check`. Generators needing a Lean build (storage layout report) are
# not listed: a conflict on their outputs stops the tool.
GENERATORS: tuple[Generator, ...] = (
    Generator(
        ("PrintAxioms.lean", "scripts/VerityUnionAxioms.lean"),
        ("python3", "scripts/generate_print_axioms.py"),
    ),
    Generator(
        ("artifacts/trust_surface_report.json",),
        ("python3", "scripts/generate_trust_surface_report.py"),
    ),
    Generator(
        ("artifacts/evmyullean_capability_report.json", "artifacts/evmyullean_unsupported_nodes.json"),
        ("python3", "scripts/generate_evmyullean_capability_report.py"),
    ),
    Generator(
        ("artifacts/evmyullean_native_lowering_report.json",),
        ("python3", "scripts/generate_evmyullean_native_lowering_report.py"),
    ),
    Generator(
        ("artifacts/evmyullean_fork_audit.json",),
        ("python3", "scripts/generate_evmyullean_fork_audit.py"),
    ),
    Generator(
        ("artifacts/layer2_boundary_catalog.json",),
        ("python3", "scripts/generate_layer2_boundary_catalog.py"),
    ),
    Generator(
        ("scripts/verify_sync_spec.json",),
        ("python3", "scripts/generate_verify_sync_spec.py"),
    ),
)

# Append-only lists: path -> regex every line of a conflict hunk must match.
APPEND_ONLY: dict[str, str] = {
    # The two `smoke_modules=( ... )` bash arrays are the only lines that are a bare module name.
    ".github/workflows/verify.yml": r"^\s+Contracts(\.[A-Za-z0-9_]+)+\s*$",
    # The file is a list of imports.
    "Contracts/Smoke.lean": r"^import [A-Za-z0-9_.]+$",
    # Only the import header is a list; conflicts in the test code stop the tool.
    "Compiler/MainTest.lean": r"^import [A-Za-z0-9_.]+$",
}

# Files deleted on the base that the PR may still modify (formerly committed
# artifacts): the deletion wins. Other modify/delete conflicts stop the tool.
DELETED_ON_BASE_PATTERNS: tuple[str, ...] = ("artifacts/*",)


@dataclass(frozen=True)
class Config:
    generators: tuple[Generator, ...] = GENERATORS
    append_only: dict[str, str] = field(default_factory=lambda: dict(APPEND_ONLY))
    deleted_on_base: tuple[str, ...] = DELETED_ON_BASE_PATTERNS


class ToolError(Exception):
    def __init__(self, message: str, code: int = 1, conflicts: list[str] | None = None) -> None:
        super().__init__(message)
        self.code = code
        self.conflicts = conflicts or []


@dataclass
class Result:
    branch: str = ""
    base: str = ""
    old_sha: str = ""
    new_sha: str = ""
    ahead: int = 0
    skipped: list[str] = field(default_factory=list)
    generated: list[str] = field(default_factory=list)
    union: list[str] = field(default_factory=list)
    deleted: list[str] = field(default_factory=list)
    regenerated: list[str] = field(default_factory=list)
    conflicts: list[str] = field(default_factory=list)
    push_command: str = ""


class Git:
    def __init__(self, repo: Path) -> None:
        self.repo = repo

    def run(
        self, *args: str, check: bool = True, env: dict[str, str] | None = None
    ) -> subprocess.CompletedProcess[str]:
        proc = subprocess.run(
            ["git", *args],
            cwd=self.repo,
            capture_output=True,
            text=True,
            env={**os.environ, **(env or {})},
        )
        if check and proc.returncode != 0:
            raise ToolError(f"git {' '.join(args)} failed:\n{proc.stdout}{proc.stderr}".rstrip())
        return proc

    def out(self, *args: str) -> str:
        return self.run(*args).stdout.strip()

    def ok(self, *args: str) -> bool:
        return self.run(*args, check=False).returncode == 0

    def git_path(self, name: str) -> Path:
        return self.repo / self.out("rev-parse", "--git-path", name)

    def rebase_dir(self) -> Path | None:
        for name in ("rebase-merge", "rebase-apply"):
            path = self.git_path(name)
            if path.is_dir():
                return path
        return None


def _short(git: Git, rev: str) -> str:
    return git.out("rev-parse", "--short", rev)


def _unmerged(git: Git) -> dict[str, set[int]]:
    """Map each unmerged path to the set of index stages present (1 base, 2 ours, 3 theirs)."""
    stages: dict[str, set[int]] = {}
    for entry in git.out("ls-files", "-u", "-z").split("\0"):
        if not entry:
            continue
        meta, path = entry.split("\t", 1)
        stages.setdefault(path, set()).add(int(meta.split()[2]))
    return stages


def _stage_text(git: Git, stage: int, path: str) -> str:
    proc = git.run("show", f":{stage}:{path}", check=False)
    return proc.stdout if proc.returncode == 0 else ""


def _conflict_hunks(merged: str, marker: str) -> list[tuple[list[str], list[str]]]:
    """Parse diff3-style merge output into (ours, theirs) line lists per hunk."""
    hunks: list[tuple[list[str], list[str]]] = []
    section: str | None = None
    ours: list[str] = []
    theirs: list[str] = []
    for line in merged.splitlines():
        if line.startswith("<" * len(marker)):
            section, ours, theirs = "ours", [], []
        elif section and line.startswith("|" * len(marker)):
            section = "base"
        elif section and line == "=" * len(marker):
            section = "theirs"
        elif section and line.startswith(">" * len(marker)):
            hunks.append((ours, theirs))
            section = None
        elif section == "ours":
            ours.append(line)
        elif section == "theirs":
            theirs.append(line)
    return hunks


def union_merge(base: str, ours: str, theirs: str, line_pattern: str) -> tuple[str | None, str]:
    """Union-merge an append-only list. Returns (merged text, "") or (None, reason)."""
    size = 17
    regex = re.compile(line_pattern)
    with tempfile.TemporaryDirectory() as tmp:
        paths = []
        for name, text in (("ours", ours), ("base", base), ("theirs", theirs)):
            path = Path(tmp) / name
            path.write_text(text, encoding="utf-8")
            paths.append(str(path))
        marked = subprocess.run(
            ["git", "merge-file", "-p", "--diff3", f"--marker-size={size}", *paths],
            capture_output=True, text=True,
        )
        for ours_lines, theirs_lines in _conflict_hunks(marked.stdout, "x" * size):
            region = ours_lines + theirs_lines
            stray = [line for line in region if not regex.match(line)]
            if stray:
                return None, f"conflict line is not a list entry: {stray[0].strip()!r}"
            dups = sorted({line.strip() for line in region if region.count(line) > 1})
            if dups:
                return None, f"union would duplicate {dups[0]!r}"
        union = subprocess.run(
            ["git", "merge-file", "-p", "--union", *paths], capture_output=True, text=True
        )
        if union.returncode < 0:
            return None, "git merge-file --union failed"
        return union.stdout, ""


def _generated_paths(config: Config) -> set[str]:
    return {out for gen in config.generators for out in gen.outputs}


def _note(seen: list[str], path: str) -> None:
    """Record a path once, across all the rebase stops that touched it."""
    if path not in seen:
        seen.append(path)


def resolve_conflicts(git: Git, config: Config, result: Result) -> list[str]:
    """Resolve the conflicts of the current rebase stop; return the unresolved ones."""
    bad: list[str] = []
    generated = _generated_paths(config)
    for path, stages in sorted(_unmerged(git).items()):
        if path in generated:
            if 2 in stages:
                git.run("checkout", "--ours", "--", path)
                git.run("add", "--", path)
            else:
                git.run("rm", "-q", "--cached", "--", path)
                (git.repo / path).unlink(missing_ok=True)
            _note(result.generated, path)
        elif 2 not in stages and stages == {1, 3} and any(
            fnmatch.fnmatch(path, pat) for pat in config.deleted_on_base
        ):
            git.run("rm", "-q", "--cached", "--", path)
            (git.repo / path).unlink(missing_ok=True)
            _note(result.deleted, path)
        elif path in config.append_only and stages == {1, 2, 3}:
            merged, reason = union_merge(
                _stage_text(git, 1, path),
                _stage_text(git, 2, path),
                _stage_text(git, 3, path),
                config.append_only[path],
            )
            if merged is None:
                bad.append(f"{path} ({reason})")
                continue
            (git.repo / path).write_text(merged, encoding="utf-8")
            git.run("add", "--", path)
            _note(result.union, path)
        else:
            bad.append(path)
    return bad


def _stopped_subject(git: Git) -> str:
    proc = git.run("log", "-1", "--format=%s", "REBASE_HEAD", check=False)
    return proc.stdout.strip() if proc.returncode == 0 else ""


def _sequence_editor(todo: Path) -> int:
    """GIT_SEQUENCE_EDITOR hook: drop the "chore: regenerate" commits from the todo list."""
    lines = todo.read_text(encoding="utf-8").splitlines(keepends=True)
    kept = []
    for line in lines:
        words = line.split(None, 2)
        # Git >= 2.45 writes "pick <sha> # <subject>"; older versions "pick <sha> <subject>".
        subject = words[2].removeprefix("# ") if len(words) == 3 else ""
        if words and words[0] in ("pick", "p") and subject.startswith(SKIP_SUBJECT_PREFIX):
            kept.append("drop " + line.split(None, 1)[1])
        else:
            kept.append(line)
    todo.write_text("".join(kept), encoding="utf-8")
    return 0


def start_rebase(git: Git, base: str, result: Result) -> None:
    merge_base = git.out("merge-base", base, "HEAD")
    for entry in git.out("log", "--reverse", "--format=%h %s", f"{merge_base}..HEAD").splitlines():
        sha, _, subject = entry.partition(" ")
        if subject.startswith(SKIP_SUBJECT_PREFIX):
            result.skipped.append(sha)
    editor = shlex.join([sys.executable, str(Path(__file__).resolve()), "--sequence-editor"])
    proc = git.run(
        "rebase", "-i", base,
        check=False,
        env={"GIT_SEQUENCE_EDITOR": editor, "GIT_EDITOR": "true"},
    )
    if proc.returncode != 0 and git.rebase_dir() is None:
        raise ToolError(f"git rebase failed to start:\n{proc.stdout}{proc.stderr}".rstrip())


def drive_rebase(git: Git, config: Config, result: Result) -> None:
    for _ in range(10000):
        if git.rebase_dir() is None:
            return
        subject = _stopped_subject(git)
        if subject.startswith(SKIP_SUBJECT_PREFIX):
            stopped = git.out("rev-parse", "REBASE_HEAD")
            # Already counted when it was planned for dropping: count each commit once.
            if not any(stopped.startswith(sha) for sha in result.skipped):
                result.skipped.append(_short(git, "REBASE_HEAD"))
            git.run("rebase", "--skip", env={"GIT_EDITOR": "true"})
            continue
        bad = resolve_conflicts(git, config, result)
        if bad:
            result.conflicts = bad
            raise ToolError(
                f"stopped on conflicts while applying {subject!r}: {', '.join(bad)}\n"
                "Resolve them, `git add` them, then rerun this tool to resume the rebase "
                "(or `git rebase --abort`).",
                code=3,
                conflicts=bad,
            )
        proc = git.run("rebase", "--continue", check=False, env={"GIT_EDITOR": "true"})
        if proc.returncode != 0 and git.rebase_dir() is not None:
            if _unmerged(git):
                continue
            if git.ok("diff", "--cached", "--quiet") and git.ok("diff", "--quiet"):
                # The commit became empty once the base's side was taken.
                git.run("rebase", "--skip", env={"GIT_EDITOR": "true"})
                continue
            raise ToolError(f"git rebase --continue failed:\n{proc.stdout}{proc.stderr}".rstrip())
    raise ToolError("rebase did not finish")


def _run(cmd: Sequence[str], repo: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(list(cmd), cwd=repo, capture_output=True, text=True)


def regenerate(git: Git, config: Config, base: str, result: Result) -> None:
    rerun: list[Generator] = []
    for gen in config.generators:
        if _run(gen.check_command, git.repo).returncode == 0:
            continue
        proc = _run(gen.command, git.repo)
        if proc.returncode != 0:
            raise ToolError(f"{shlex.join(gen.command)} failed:\n{proc.stdout}{proc.stderr}".rstrip())
        rerun.append(gen)
        changed = git.out("status", "--porcelain", "--", *gen.outputs)
        if changed:
            git.run("add", "--", *gen.outputs)
            result.regenerated.extend(gen.outputs)
    if result.regenerated:
        git.run("commit", "-q", "-m", f"chore: regenerate generated files after rebasing onto {base}")
    for gen in rerun:
        proc = _run(gen.check_command, git.repo)
        if proc.returncode != 0:
            raise ToolError(
                f"{shlex.join(gen.check_command)} still fails after regeneration:\n"
                f"{proc.stdout}{proc.stderr}".rstrip(),
                code=4,
            )


def _branch_remote(git: Git, branch: str) -> str:
    return git.run("config", f"branch.{branch}.remote", check=False).stdout.strip()


def guard(git: Git, branch: str) -> str:
    """Refuse when local work could be lost; return the upstream ref."""
    if git.out("status", "--porcelain", "--untracked-files=no"):
        raise ToolError("working tree has tracked changes; commit or stash them first", code=5)
    proc = git.run("rev-parse", "--abbrev-ref", f"{branch}@{{u}}", check=False)
    if proc.returncode != 0:
        raise ToolError(
            f"{branch} has no upstream; set one with `git branch -u <remote>/{branch}`", code=5
        )
    upstream = proc.stdout.strip()
    local, remote = git.out("rev-parse", branch), git.out("rev-parse", upstream)
    if local != remote:
        raise ToolError(
            f"{branch} ({local[:9]}) differs from its upstream {upstream} ({remote[:9]}); "
            "push it or reconcile it yourself, this tool never discards local commits",
            code=5,
        )
    return upstream


def rebase(repo: Path, base: str, branch: str | None, fetch: bool, config: Config) -> Result:
    git = Git(repo)
    result = Result(base=base)
    state = git.rebase_dir()
    if state is not None:
        result.branch = (state / "head-name").read_text().strip().removeprefix("refs/heads/")
        result.old_sha = (state / "orig-head").read_text().strip()
        if branch and branch != result.branch:
            raise ToolError(f"a rebase of {result.branch} is in progress, not of {branch}", code=5)
        drive_rebase(git, config, result)
    else:
        current = git.out("rev-parse", "--abbrev-ref", "HEAD")
        result.branch = branch or current
        if result.branch == "HEAD":
            raise ToolError("HEAD is detached; pass --branch", code=5)
        if fetch:
            remotes = set(git.out("remote").split())
            wanted = {base.split("/", 1)[0], _branch_remote(git, result.branch)}
            for remote in sorted(wanted & remotes):
                git.run("fetch", "-q", remote)
        guard(git, result.branch)
        if result.branch != current:
            git.run("switch", "-q", result.branch)
        result.old_sha = git.out("rev-parse", "HEAD")
        start_rebase(git, base, result)
        drive_rebase(git, config, result)
    regenerate(git, config, base, result)
    result.new_sha = git.out("rev-parse", "HEAD")
    result.ahead = int(git.out("rev-list", "--count", f"{base}..HEAD"))
    remote = _branch_remote(git, result.branch) or "origin"
    result.push_command = f"git push --force-with-lease {remote} {result.branch}"
    return result


def _fmt(items: list[str]) -> str:
    return ",".join(items) if items else "-"


def format_line(r: Result) -> str:
    return (
        f"{r.branch}: {r.old_sha[:9]} -> {r.new_sha[:9]}, {r.ahead} ahead of {r.base}; "
        f"skipped={_fmt(r.skipped)} generated={_fmt(r.generated)} union={_fmt(r.union)} "
        f"deleted={_fmt(r.deleted)} regenerated={_fmt(r.regenerated)}; "
        f"push with: {r.push_command}"
    )


def main(argv: Sequence[str] | None = None, config: Config | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Rebase a PR branch onto the base, auto-resolving generated files and "
        "append-only lists; never pushes, never discards local commits.",
    )
    parser.add_argument("--base", default="origin/main", help="branch to rebase onto (default: origin/main)")
    parser.add_argument("--branch", help="branch to rebase (default: the current branch)")
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="repository path (default: cwd)")
    parser.add_argument("--no-fetch", action="store_true", help="do not fetch the base and upstream remotes")
    parser.add_argument("--json", action="store_true", help="print the result as a JSON object")
    parser.add_argument("--sequence-editor", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("todo", nargs="?", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    if args.sequence_editor:
        return _sequence_editor(args.todo)
    if args.todo is not None:
        parser.error(f"unexpected argument: {args.todo}")

    repo = Path(Git(args.repo).out("rev-parse", "--show-toplevel"))
    try:
        result = rebase(repo, args.base, args.branch, not args.no_fetch, config or Config())
    except ToolError as exc:
        if args.json:
            payload = {"ok": False, "exit_code": exc.code, "error": str(exc), "conflicts": exc.conflicts}
            print(json.dumps(payload))
        else:
            print(f"error: {exc}", file=sys.stderr)
        return exc.code
    if args.json:
        print(json.dumps({"ok": True, **result.__dict__}))
    else:
        print(format_line(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
