#!/usr/bin/env python3
"""Every Lean module under the source roots is built by a bare `lake build`.

A module is built by `lake build` when it is a root of a `@[default_target]`
library (its `roots`/`globs` in `lakefile.lean`) or is imported, transitively,
by one. A module outside that closure is never elaborated by `lake build`: its
proofs, `#guard_msgs` tests and `decide` examples go unchecked, and tools that
load its stale `.olean` see old code.

Likewise, every `lean_exe` that the Makefile, scripts or CI workflows run directly
from `.lake/build/bin/` must be a `@[default_target]`: otherwise a bare `lake build`
rebuilds the `.olean`s but not the binary, and the stale binary, loading the new
environment, misbehaves (a segfault after a `ContractState` field was added).

Usage: python3 scripts/check_lake_default_coverage.py [--root DIR]
Silent and exit 0 when every module and directly-run executable is covered;
otherwise lists what is not and exits 1.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

SOURCE_ROOTS = ("Verity", "Contracts", "Compiler")

_LIB_RE = re.compile(
    r"(?P<attr>@\[default_target\]\s*)?lean_lib\s+«(?P<name>[^»]+)»\s+where(?P<body>.*?)(?=\n(?:@\[|lean_lib|lean_exe|input_dir|require|package)|\Z)",
    re.S,
)
_GLOB_RE = re.compile(r"\.(?P<kind>one|submodules|andSubmodules)\s+`(?P<mod>[\w.]+)")
_ROOTS_RE = re.compile(r"roots\s*:=\s*#\[(?P<items>.*?)\]", re.S)
_SRCDIR_RE = re.compile(r'srcDir\s*:=\s*"(?P<dir>[^"]+)"')
_EXE_RE = re.compile(r"(?P<attr>@\[default_target\]\s*)?lean_exe\s+«(?P<name>[^»]+)»")
_BIN_RE = re.compile(r"\.lake/build/bin/(?P<name>[A-Za-z0-9_-]+)")
# Where binaries are run from: the Makefile, scripts and CI workflows.
INVOKER_GLOBS = ("Makefile", "scripts/**/*", ".github/**/*.yml", "test/**/*.sh")
_IMPORT_RE = re.compile(r"^import\s+(?P<mods>[^\n]+)", re.M)


def _strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def module_files(root: Path, src_dir: str = ".") -> dict[str, Path]:
    """All modules found under `src_dir`, by dotted name."""
    base = root / src_dir
    out: dict[str, Path] = {}
    for path in base.rglob("*.lean"):
        rel = path.relative_to(base)
        if rel.parts[0].startswith(".") or rel.parts[0] == ".lake" or rel.name == "lakefile.lean":
            continue
        out[".".join(rel.with_suffix("").parts)] = path
    return out


def default_roots(lakefile_text: str, root: Path) -> tuple[set[str], set[str]]:
    """Root modules of the default-target libraries, and the source dirs they live in."""
    text = _strip_comments(lakefile_text)
    roots: set[str] = set()
    src_dirs: set[str] = {"."}
    for lib in _LIB_RE.finditer(text):
        if not lib.group("attr"):
            continue
        body = lib.group("body")
        src_dir = (m.group("dir") if (m := _SRCDIR_RE.search(body)) else ".")
        src_dirs.add(src_dir)
        available = module_files(root, src_dir)
        globs = list(_GLOB_RE.finditer(body))
        if (rm := _ROOTS_RE.search(body)):
            roots.update(re.findall(r"`([\w.]+)", rm.group("items")))
        elif not globs:
            roots.add(lib.group("name"))
        for g in globs:
            mod, kind = g.group("mod"), g.group("kind")
            if kind in ("one", "andSubmodules"):
                roots.add(mod)
            if kind in ("submodules", "andSubmodules"):
                roots.update(m for m in available if m.startswith(mod + "."))
    return roots, src_dirs


def imports_of(path: Path) -> list[str]:
    text = _strip_comments(path.read_text(encoding="utf-8"))
    mods: list[str] = []
    for line in _IMPORT_RE.finditer(text):
        mods.extend(tok for tok in line.group("mods").split() if re.fullmatch(r"[\w.]+", tok))
    return mods


def uncovered_modules(root: Path) -> list[str]:
    roots, src_dirs = default_roots((root / "lakefile.lean").read_text(encoding="utf-8"), root)
    files: dict[str, Path] = {}
    for src_dir in src_dirs:
        files.update(module_files(root, src_dir))
    seen: set[str] = set()
    stack = [m for m in roots if m in files]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        stack.extend(m for m in imports_of(files[mod]) if m in files and m not in seen)
    wanted = {m for m in files if m.split(".")[0] in SOURCE_ROOTS}
    return sorted(wanted - seen)


def non_default_run_executables(root: Path) -> list[str]:
    """`lean_exe`s run directly from `.lake/build/bin/` that a bare `lake build` does not build."""
    text = _strip_comments((root / "lakefile.lean").read_text(encoding="utf-8"))
    exes = {m.group("name"): bool(m.group("attr")) for m in _EXE_RE.finditer(text)}
    run: set[str] = set()
    for pattern in INVOKER_GLOBS:
        for path in root.glob(pattern):
            if path.is_file() and path.suffix not in (".pyc",):
                try:
                    body = path.read_text(encoding="utf-8")
                except UnicodeDecodeError:
                    continue
                run.update(m.group("name") for m in _BIN_RE.finditer(body))
    return sorted(name for name in run if name in exes and not exes[name])


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args(argv)
    status = 0
    missing = uncovered_modules(args.root)
    if missing:
        print(f"{len(missing)} Lean module(s) are not built by `lake build` "
              "(add them to a @[default_target] library in lakefile.lean):", file=sys.stderr)
        for mod in missing:
            print(f"  {mod}", file=sys.stderr)
        status = 1
    stale = non_default_run_executables(args.root)
    if stale:
        print(f"{len(stale)} executable(s) run from .lake/build/bin/ are not rebuilt by "
              "`lake build` (mark them @[default_target] in lakefile.lean):", file=sys.stderr)
        for name in stale:
            print(f"  {name}", file=sys.stderr)
        status = 1
    return status


if __name__ == "__main__":
    sys.exit(main())
