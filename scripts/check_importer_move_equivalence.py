#!/usr/bin/env python3
"""Equivalence harness for move-only refactors of the Solidity importer (#2837).

A move-only PR (for example, moving declarations out of
`Compiler/SolidityImport/Import.lean` into construct modules) must not change
what the importer produces. This script makes that claim checkable:

* ``targets`` lists every ``solidity_import`` command in the smoke modules,
  with its fully qualified name.
* ``dump --out DIR`` writes, for each smoke module, a probe that appends
  ``#eval`` dumps of ``repr <name>.model`` and ``repr <name>.report`` (the
  technique ``solidity_import_mutations.py`` uses for ``model.golden``), runs it
  with ``lake env lean`` and keeps its full output (unsupported-construct
  warnings, rejection errors and every other message) and exit code. This is a
  Lean job: run it through ``lean-job`` or in CI, once on the base and once on
  the candidate checkout. ``--probe-only`` writes the probes without running
  Lean.
* ``compare BASE CANDIDATE`` diffs two dumps byte for byte.
* ``anchors`` checks that every mutation anchor occurs exactly once in the file
  its script routes it to, so a moved declaration cannot silently turn a
  mutant into a no-op.

Allowed differences (the only ones): the 64-hex value of the report field
``sourceDigest``. A move changes the hashed importer source files, so every
digest changes once by design (#2849). Nothing else may differ: models,
every other report field, diagnostics, exit codes and the target list must be
byte-identical. Absolute checkout and output paths are replaced by ``<root>``
and ``<out>`` when a dump is written, so two checkouts can be compared.

A comparison that saw no model or no report fails: an empty dump is not
evidence of equivalence. So does a dump that was not built first, a probe that
could not load a module, an error at a line of the smoke module itself, an
import not pinned by ``#guard_msgs`` that produced no value, a ``--module``
subset (unless ``--allow-subset``), a probe that did not reach its final
``complete`` marker or exited other than 0 or 1 (1 is normal: a rejected
import's absent value is an error in the probe), and a base and candidate at the same clean
revision. Dumps go inside their checkout (e.g. ``.lake/importer-equivalence``),
because the importer resolves source paths from the probe's package root.

Not dumped: the accessors and the `covered` theorem an import also defines.
Smoke modules that use them still fail to elaborate if they break, and that
shows up as a diagnostics or exit-code difference.
"""
from __future__ import annotations

import argparse
import ast
import importlib
import json
import re
import shlex
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
SMOKE = Path("Contracts/SolidityImportSmoke")
IMPORT = "Compiler/SolidityImport/Import.lean"

DIGEST_RE = re.compile(r'sourceDigest := "([0-9a-f]{64})"')
DIGEST_PLACEHOLDER = 'sourceDigest := "<digest>"'
NAME = r"[A-Za-z_À-￿][A-Za-z0-9_'!?À-￿]*"
IMPORT_RE = re.compile(rf"^(?:#guard_msgs\b.*?\bin\s+)?solidity_import\s+({NAME}(?:\.{NAME})*)\b")
NAMESPACE_RE = re.compile(rf"^namespace\s+({NAME}(?:\.{NAME})*)\s*$")
SECTION_RE = re.compile(rf"^(?:noncomputable\s+)?section(?:\s+({NAME}(?:\.{NAME})*))?\s*$")
END_RE = re.compile(rf"^end(?:\s+({NAME}(?:\.{NAME})*))?\s*$")


class HarnessError(Exception):
    pass


# --------------------------------------------------------------------------
# Targets and probes


def strip_comments(text: str) -> list[str]:
    """Source lines with `--` and (nested) `/- -/` comments blanked out."""
    out: list[str] = []
    depth = 0
    for line in text.splitlines():
        kept = []
        i = 0
        in_string = False
        while i < len(line):
            two = line[i:i + 2]
            if depth:
                if two == "/-":
                    depth += 1
                    i += 2
                elif two == "-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
                continue
            ch = line[i]
            if in_string:
                kept.append(ch)
                if ch == "\\":
                    kept.append(line[i + 1:i + 2])
                    i += 2
                    continue
                in_string = ch != '"'
                i += 1
            elif ch == '"':
                in_string = True
                kept.append(ch)
                i += 1
            elif two == "--":
                break
            elif two == "/-":
                depth += 1
                i += 2
            else:
                kept.append(ch)
                i += 1
        out.append("".join(kept))
    return out


GUARD_RE = re.compile(r"^#guard_msgs\b.*\bin\s*$")


def import_targets(text: str) -> list[tuple[str, bool]]:
    """Fully qualified names of the top-level `solidity_import` commands, each
    with whether `#guard_msgs` pins its messages (such an import may
    legitimately define no value: its evidence is the pinned messages)."""
    scopes: list[tuple[str, str | None]] = []  # (kind, name)
    found: list[tuple[str, bool]] = []
    guard = False
    for raw in strip_comments(text):
        line = raw.strip()
        if not line:
            continue
        guarded, guard = guard, bool(GUARD_RE.match(line))
        if guard:
            continue
        if m := NAMESPACE_RE.match(line):
            scopes.append(("namespace", m.group(1)))
        elif m := SECTION_RE.match(line):
            scopes.append(("section", m.group(1)))
        elif m := END_RE.match(line):
            if not scopes:
                raise HarnessError(f"unbalanced `{line}`")
            kind, name = scopes.pop()
            if (m.group(1) or None) != name:
                raise HarnessError(f"`{line}` closes {kind} {name}")
        elif raw[:1] not in (" ", "\t") and (m := IMPORT_RE.match(line)):
            prefix = [n for kind, n in scopes if kind == "namespace"]
            found.append((".".join(prefix + [m.group(1)]), guarded or line.startswith("#guard_msgs")))
    names = [name for name, _ in found]
    if len(set(names)) != len(names):
        raise HarnessError(f"duplicate solidity_import names: {names}")
    return found


def import_names(text: str) -> list[str]:
    return [name for name, _ in import_targets(text)]


def targets(root: Path, modules: list[str] | None = None) -> dict[str, list[str]]:
    found: dict[str, list[str]] = {}
    for path in sorted((root / SMOKE).glob("*.lean")):
        if modules and path.stem not in modules:
            continue
        try:
            names = import_names(path.read_text(encoding="utf-8"))
        except HarnessError as error:
            raise HarnessError(f"{path.relative_to(root)}: {error}") from None
        if names:
            found[path.stem] = names
    if modules and set(modules) - set(found):
        raise HarnessError(f"no solidity_import in: {sorted(set(modules) - set(found))}")
    return found


def lean_string(path: Path) -> str:
    return json.dumps(str(path))  # JSON string escapes are valid Lean string escapes


def probe_text(source: str, names: list[str], dumps: Path) -> str:
    """The module followed by one dump per value. An absent value (a rejected or
    `collectUnsupported` import) is an `unknown identifier` error that both sides
    must report identically."""
    lines = [source.rstrip("\n"), "", "-- check_importer_move_equivalence.py probe"]
    for name in names:
        for kind in ("model", "report"):
            target = lean_string(dumps / f"{name}.{kind}")
            lines.append(f'#eval IO.FS.writeFile {target} (toString (repr {name}.{kind}) ++ "\\n")')
    # Last: proves Lean reached the end of the probe (not killed, timed out or aborted).
    lines.append(f'#eval IO.FS.writeFile {lean_string(dumps / "complete")} ""')
    return "\n".join(lines) + "\n"


def normalize_paths(text: str, root: Path, out: Path) -> str:
    # The output directory may live under the checkout: replace the longer path first.
    for path, label in sorted(((out, "<out>"), (root, "<root>")), key=lambda p: -len(str(p[0]))):
        text = text.replace(str(path.resolve()), label)
    return text


def module_imports(source: str) -> list[str]:
    """The modules a Lean file imports (its leading `import` lines)."""
    found: list[str] = []
    for line in strip_comments(source):
        words = line.split()
        if not words:
            continue
        if words[0] != "import":
            break
        found += words[1:]
    return found


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", *args], cwd=root, text=True, capture_output=True).stdout.strip()


def dump(root: Path, out: Path, modules: list[str] | None, runner: list[str], probe_only: bool,
         build: bool = True) -> dict:
    root, out = root.resolve(), out.resolve()
    # The importer resolves `from "..."` against the package root it finds above
    # the probe file, so probes must live inside the checkout (e.g. under .lake/).
    if not out.is_relative_to(root):
        raise HarnessError(f"--out must be inside the checkout {root} (e.g. {root / '.lake/importer-equivalence'})")
    if out.exists() and any(out.iterdir()):
        raise HarnessError(f"{out} is not empty")
    found = targets(root, modules)
    if not found:
        raise HarnessError("no solidity_import targets found")
    sources = {module: (root / SMOKE / f"{module}.lean").read_text(encoding="utf-8") for module in found}
    imports = sorted({name for source in sources.values() for name in module_imports(source)})
    # `lake env lean` never rebuilds: without this build a probe can load oleans
    # from another revision, or fail on a missing one identically on both sides.
    built = build and not probe_only
    out.mkdir(parents=True, exist_ok=True)
    if built:
        result = subprocess.run([*runner, "lake", "build", *imports], cwd=root, text=True, capture_output=True)
        (out / "build.log").write_text(normalize_paths(result.stdout + result.stderr, root, out), encoding="utf-8")
        if result.returncode:
            raise HarnessError(f"lake build of the smoke imports failed (exit {result.returncode}); see {out / 'build.log'}")
    manifest = {"revision": git(root, "rev-parse", "HEAD"),
                "dirty": bool(git(root, "status", "--porcelain", "--untracked-files=no")),
                "built": built, "subset": bool(modules), "imports": imports, "targets": found,
                "guarded": {module: [name for name, guarded in import_targets(sources[module]) if guarded]
                            for module in found},
                "source_lines": {module: len(sources[module].rstrip("\n").splitlines()) for module in found}}
    for module, names in found.items():
        directory = out / module
        directory.mkdir(parents=True)
        probe = out / "probes" / f"{module}.lean"
        probe.parent.mkdir(exist_ok=True)
        probe.write_text(probe_text(sources[module], names, directory), encoding="utf-8")
        if probe_only:
            continue
        result = subprocess.run([*runner, "lake", "env", "lean", str(probe)], cwd=root,
                                text=True, capture_output=True)
        (directory / "diagnostics.txt").write_text(
            normalize_paths(result.stdout + result.stderr, root, out), encoding="utf-8")
        (directory / "exit").write_text(f"{result.returncode}\n", encoding="utf-8")
        print(f"{module}: exit {result.returncode}", flush=True)
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return manifest


# --------------------------------------------------------------------------
# Comparison


def normalize_report(text: str, where: str) -> str:
    normalized, count = DIGEST_RE.subn(DIGEST_PLACEHOLDER, text)
    if count != 1:
        raise HarnessError(f"{where}: expected exactly one sourceDigest, found {count}")
    return normalized


def dump_files(directory: Path) -> set[str]:
    return {p.relative_to(directory).as_posix() for p in directory.rglob("*")
            if p.is_file() and p.parts[len(directory.parts)] not in ("probes", "manifest.json", "build.log")}


# A probe that could not load a module proves nothing, even when both sides agree.
MISSING_BUILD_RE = re.compile(r"object file \S+ of module \S+ does not exist|unknown module prefix|unknown package"
                              r"|package root not found")
# An error at a line of the module itself. Smoke modules elaborate cleanly (expected
# failures are pinned by `#guard_msgs`), so such an error means the environment (a
# missing solc, a bad checksum, ...) or the importer broke, even if both sides agree.
SOURCE_ERROR_RE = re.compile(r"^<out>/probes/([^/:]+)\.lean:(\d+):\d+: error", re.MULTILINE)


def compare(base: Path, candidate: Path, allow_subset: bool = False) -> dict:
    """Byte comparison of two dumps. Returns a summary; `mismatches` must be empty."""
    mismatches: list[str] = []
    manifests = []
    for side in (base, candidate):
        manifest = side / "manifest.json"
        if not manifest.is_file():
            raise HarnessError(f"{side}: missing manifest.json (not a dump)")
        manifests.append(json.loads(manifest.read_text(encoding="utf-8")))
    for label, manifest in zip(("base", "candidate"), manifests):
        if not manifest.get("built"):
            mismatches.append(f"{label} dump was not built before probing")
        if manifest.get("subset") and not allow_subset:
            mismatches.append(f"{label} dump covers only some modules (pass --allow-subset)")
    if (manifests[0].get("revision") == manifests[1].get("revision")
            and not manifests[0].get("dirty") and not manifests[1].get("dirty")):
        mismatches.append("base and candidate are the same clean revision")
    if manifests[0]["targets"] != manifests[1]["targets"]:
        mismatches.append("targets differ")
    base_files, candidate_files = dump_files(base), dump_files(candidate)
    for name in sorted(base_files - candidate_files):
        mismatches.append(f"only in base: {name}")
    for name in sorted(candidate_files - base_files):
        mismatches.append(f"only in candidate: {name}")
    for label, manifest, files in (("base", manifests[0], base_files), ("candidate", manifests[1], candidate_files)):
        for module in manifest["targets"]:
            if f"{module}/complete" not in files:
                mismatches.append(f"{label} probe of {module} did not run to completion")
    counts = {"model": 0, "report": 0, "diagnostics": 0, "exit": 0, "complete": 0}
    digest_changed = 0
    for name in sorted(base_files & candidate_files):
        before = (base / name).read_text(encoding="utf-8")
        after = (candidate / name).read_text(encoding="utf-8")
        kind = name.rsplit("/", 1)[-1]
        kind = "diagnostics" if kind == "diagnostics.txt" else kind if kind in ("exit", "complete") else kind.rsplit(".", 1)[-1]
        if kind not in counts:
            raise HarnessError(f"unexpected dump file {name}")
        counts[kind] += 1
        if kind == "report":
            if before != after:
                digest_changed += 1
            before = normalize_report(before, f"base {name}")
            after = normalize_report(after, f"candidate {name}")
        if kind == "exit":
            for label, text in (("base", before), ("candidate", after)):
                # 1 is normal: a rejected import's absent value is an error in the probe.
                if text.strip() not in ("0", "1"):
                    mismatches.append(f"abnormal exit {text.strip()} in {label} {name}")
        if kind == "diagnostics":
            for label, text, manifest in (("base", before, manifests[0]), ("candidate", after, manifests[1])):
                if MISSING_BUILD_RE.search(text):
                    mismatches.append(f"missing build output in {label} {name}")
                lines = manifest.get("source_lines", {})
                for module, line in SOURCE_ERROR_RE.findall(text):
                    if int(line) <= lines.get(module, 0):
                        mismatches.append(f"error in module source in {label} {name}: line {line}")
        if before != after:
            mismatches.append(f"differs: {name}")
    for kind in ("model", "report", "diagnostics"):
        if counts[kind] == 0:
            mismatches.append(f"no {kind} compared: the dumps are not evidence")
    # Rejected and `#guard_msgs`-checked imports legitimately define no value; their
    # evidence is the diagnostics. List them so a reviewer sees what was not dumped.
    without_output = sorted(f"{module}: {name}" for module, names in manifests[0]["targets"].items()
                            for name in names
                            if not {f"{module}/{name}.model", f"{module}/{name}.report"} & base_files)
    guarded = {f"{module}: {name}" for module, names in manifests[0].get("guarded", {}).items() for name in names}
    for target in without_output:
        if target not in guarded:
            mismatches.append(f"no value for an import not pinned by #guard_msgs: {target}")
    return {"compared": counts, "reports_with_changed_digest": digest_changed,
            "targets_without_value": without_output,
            "base_revision": manifests[0].get("revision"),
            "candidate_revision": manifests[1].get("revision"), "mismatches": mismatches}


# --------------------------------------------------------------------------
# Mutation anchors

# How each table-driven mutation script routes an anchor to a file:
#   "path"   MUTANTS[name] = (relative path, anchor, ...)
#   "import" MUTANTS[name] = (anchor, ...), applied to Import.lean
#   "router" MUTANTS[name] = (anchor, ...), file from mutation_source(root, name)
#   a path   MUTANTS[name] = (anchor, ...), applied to that file
MUTANT_TABLES = {
    "check_abi_length_for_mutations": "path",
    "check_abi_mutations": "import",
    "check_account_storage_mutations": "Verity/Core.lean",
    "check_byte_call_mutations": "Verity/Core/Model/Denote.lean",
    "check_create2_struct_emit_mutations": "path",
    "check_deployment_world_mutations": "Verity/Core/Model/DenoteCreate2.lean",
    "check_environment_mutations": "import",
    "check_extcodecopy_struct_decode_mutations": "path",
    "check_extcodehash_mutations": "path",
    "check_external_code_and_low_level_call_mutations": "path",
    "check_hashing_mutations": "path",
    "check_interface_static_call_mutations": "path",
    "check_interface_word_static_call_mutations": "path",
    "check_memory_call_mutations": "path",
    "check_multiple_dynamic_abi_mutations": "path",
    "check_nested_dynamic_struct_abi_mutations": "path",
    "check_scalar_array_abi_mutations": "path",
    "check_storage_mutations": "router",
    "check_struct_abi_mutations": "path",
    "mutations": "path",
}
# Scripts whose MUTANTS table is not an anchor table, with the reason.
NOT_ANCHOR_TABLES = {
    "check_create2_opcode_mutations": "anchors keyed by Lean module with an expected count, not uniqueness",
    "pinned_sequence": "a tuple of mutant names, no anchors",
}
# Scripts with inline anchors applied to Import.lean: string constants bound to
# `anchor`, or the anchor element of each `rules` tuple.
INLINE_ANCHOR_SCRIPTS = (
    "check_block_mutations",
    "check_reference_argument_mutations",
    "check_reference_boundary_mutations",
    "check_reference_location_mutation",
)
MUTANTS_ASSIGN = re.compile(r"^MUTANTS\s*=", re.MULTILINE)


@dataclass(frozen=True)
class Anchor:
    script: str
    mutant: str
    file: str
    text: str


def inline_anchors(script: str, source: str) -> list[Anchor]:
    found: list[Anchor] = []
    for node in ast.walk(ast.parse(source)):
        if not isinstance(node, ast.Assign) or len(node.targets) != 1:
            continue
        target = node.targets[0]
        if not isinstance(target, ast.Name):
            continue
        if target.id == "anchor" and isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
            found.append(Anchor(script, script, IMPORT, node.value.value))
        elif target.id == "rules" and isinstance(node.value, ast.List):
            for rule in node.value.elts:
                name, anchor = ast.literal_eval(rule.elts[0]), ast.literal_eval(rule.elts[1])
                found.append(Anchor(script, name, IMPORT, anchor))
    return found


def table_anchors(script: str, module, routing: str, root: Path) -> list[Anchor]:
    found: list[Anchor] = []
    for name, spec in module.MUTANTS.items():
        if not isinstance(spec, tuple) or len(spec) < 2:
            raise HarnessError(f"{script}: {name}: unexpected mutant shape {type(spec).__name__}")
        if routing == "path":
            relative, text = spec[0], spec[1]
        elif routing == "router":
            relative, text = module.mutation_source(root, name).relative_to(root).as_posix(), spec[0]
        else:
            relative, text = (IMPORT if routing == "import" else routing), spec[0]
        if not (isinstance(relative, str) and relative.endswith(".lean") and isinstance(text, str)):
            raise HarnessError(f"{script}: {name}: cannot route ({relative!r})")
        found.append(Anchor(script, name, relative, text))
    return found


def declared_tables(package: Path) -> tuple[list[str], list[str]]:
    """Scripts that define a MUTANTS table, and routing problems: a table this
    file does not classify, or a classified script without a table."""
    problems: list[str] = []
    declared = sorted(p.stem for p in package.glob("*.py") if MUTANTS_ASSIGN.search(p.read_text(encoding="utf-8")))
    for script in declared:
        if script not in MUTANT_TABLES and script not in NOT_ANCHOR_TABLES:
            problems.append(f"{script}: MUTANTS table with no routing in check_importer_move_equivalence.py")
    for script in sorted(set(MUTANT_TABLES) - set(declared)):
        problems.append(f"{script}: routed but defines no MUTANTS table")
    return declared, problems


def collect_anchors(root: Path = ROOT, scripts: Path = SCRIPTS) -> tuple[list[Anchor], list[str]]:
    """Every routed anchor, plus the problems that prevent collecting them."""
    package = scripts / "solidity_differential"
    declared, problems = declared_tables(package)
    if str(scripts) not in sys.path:
        sys.path.insert(0, str(scripts))
    anchors: list[Anchor] = []
    for script, routing in MUTANT_TABLES.items():
        if script not in declared:
            continue
        module = importlib.import_module(f"solidity_differential.{script}")
        try:
            anchors += table_anchors(script, module, routing, root)
        except HarnessError as error:
            problems.append(str(error))
    for script in INLINE_ANCHOR_SCRIPTS:
        path = package / f"{script}.py"
        found = inline_anchors(script, path.read_text(encoding="utf-8")) if path.is_file() else []
        if not found:
            problems.append(f"{script}: no inline anchor found")
        anchors += found
    return anchors, problems


# Anchors allowed not to occur exactly once, with their count. Empty since #2831
# re-anchored the 17 stale mutants recorded here on 2026-11-21: every anchor must
# now occur exactly once. The check also fails if an entry's count changes and for
# a listed mutant that no longer exists.
KNOWN_ANCHOR_PROBLEMS: dict[tuple[str, str], int] = {}


def anchor_problems(anchors: list[Anchor], root: Path = ROOT,
                    known: dict[tuple[str, str], int] | None = None) -> list[str]:
    """Anchors that do not occur exactly once in their routed file, except the
    `known` ones at their recorded count; plus `known` entries that changed."""
    known = KNOWN_ANCHOR_PROBLEMS if known is None else known
    problems: list[str] = []
    texts: dict[str, str] = {}
    seen: set[tuple[str, str]] = set()
    for anchor in anchors:
        path = root / anchor.file
        if anchor.file not in texts:
            texts[anchor.file] = path.read_text(encoding="utf-8") if path.is_file() else ""
        count = texts[anchor.file].count(anchor.text) if anchor.text else 0
        key = (anchor.script, anchor.mutant)
        seen.add(key)
        if key in known:
            if count != known[key]:
                problems.append(f"{anchor.script}: {anchor.mutant}: known anchor problem changed "
                                f"({known[key]} -> {count} in {anchor.file}); update KNOWN_ANCHOR_PROBLEMS")
        elif count != 1:
            problems.append(f"{anchor.script}: {anchor.mutant}: anchor occurs {count} times in {anchor.file}")
    for script, mutant in sorted(set(known) - seen):
        problems.append(f"{script}: {mutant}: listed in KNOWN_ANCHOR_PROBLEMS but no longer a mutant")
    return problems


# --------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("targets", help="list solidity_import targets")
    p.add_argument("--root", type=Path, default=ROOT)
    p.add_argument("--module", action="append")
    p = sub.add_parser("dump", help="dump models, reports and diagnostics (a Lean job)")
    p.add_argument("--root", type=Path, default=ROOT)
    p.add_argument("--out", type=Path, required=True, help="inside the checkout, e.g. .lake/importer-equivalence/base")
    p.add_argument("--module", action="append", help="smoke module stem (default: all)")
    p.add_argument("--runner", default="", help='command prefix, e.g. "lean-job lane-equiv --"')
    p.add_argument("--probe-only", action="store_true", help="write probes, do not run Lean")
    p.add_argument("--no-build", action="store_true",
                   help="skip `lake build` of the smoke imports (compare rejects such dumps)")
    p = sub.add_parser("compare", help="compare two dumps")
    p.add_argument("base", type=Path)
    p.add_argument("candidate", type=Path)
    p.add_argument("--allow-subset", action="store_true", help="accept dumps made with --module")
    p = sub.add_parser("anchors", help="check that every mutation anchor occurs exactly once")
    args = parser.parse_args(argv)
    try:
        if args.command == "targets":
            print(json.dumps(targets(args.root.resolve(), args.module), indent=2))
        elif args.command == "dump":
            manifest = dump(args.root, args.out, args.module, shlex.split(args.runner), args.probe_only,
                            build=not args.no_build)
            print(f"{sum(map(len, manifest['targets'].values()))} imports in {len(manifest['targets'])} modules")
        elif args.command == "compare":
            summary = compare(args.base, args.candidate, args.allow_subset)
            print(json.dumps(summary, indent=2))
            return 1 if summary["mismatches"] else 0
        else:
            anchors, problems = collect_anchors()
            problems += anchor_problems(anchors)
            for problem in problems:
                print(problem)
            print(f"{len(anchors)} anchors, {len(problems)} problems")
            return 1 if problems else 0
    except HarnessError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
