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
evidence of equivalence.
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


def import_names(text: str) -> list[str]:
    """Fully qualified names of the top-level `solidity_import` commands."""
    scopes: list[tuple[str, str | None]] = []  # (kind, name)
    names: list[str] = []
    for raw in strip_comments(text):
        line = raw.strip()
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
            names.append(".".join(prefix + [m.group(1)]))
    if len(set(names)) != len(names):
        raise HarnessError(f"duplicate solidity_import names: {names}")
    return names


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
    return "\n".join(lines) + "\n"


def normalize_paths(text: str, root: Path, out: Path) -> str:
    # The output directory may live under the checkout: replace the longer path first.
    for path, label in sorted(((out, "<out>"), (root, "<root>")), key=lambda p: -len(str(p[0]))):
        text = text.replace(str(path.resolve()), label)
    return text


def dump(root: Path, out: Path, modules: list[str] | None, runner: list[str], probe_only: bool) -> dict:
    root, out = root.resolve(), out.resolve()
    if out.exists() and any(out.iterdir()):
        raise HarnessError(f"{out} is not empty")
    found = targets(root, modules)
    if not found:
        raise HarnessError("no solidity_import targets found")
    revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, text=True,
                              capture_output=True).stdout.strip()
    manifest = {"revision": revision, "targets": found}
    for module, names in found.items():
        directory = out / module
        directory.mkdir(parents=True)
        probe = out / "probes" / f"{module}.lean"
        probe.parent.mkdir(exist_ok=True)
        source = (root / SMOKE / f"{module}.lean").read_text(encoding="utf-8")
        probe.write_text(probe_text(source, names, directory), encoding="utf-8")
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
            if p.is_file() and p.parts[len(directory.parts)] not in ("probes", "manifest.json")}


def compare(base: Path, candidate: Path) -> dict:
    """Byte comparison of two dumps. Returns a summary; `mismatches` must be empty."""
    mismatches: list[str] = []
    manifests = []
    for side in (base, candidate):
        manifest = side / "manifest.json"
        if not manifest.is_file():
            raise HarnessError(f"{side}: missing manifest.json (not a dump)")
        manifests.append(json.loads(manifest.read_text(encoding="utf-8")))
    if manifests[0]["targets"] != manifests[1]["targets"]:
        mismatches.append("targets differ")
    base_files, candidate_files = dump_files(base), dump_files(candidate)
    for name in sorted(base_files - candidate_files):
        mismatches.append(f"only in base: {name}")
    for name in sorted(candidate_files - base_files):
        mismatches.append(f"only in candidate: {name}")
    counts = {"model": 0, "report": 0, "diagnostics": 0, "exit": 0}
    digest_changed = 0
    for name in sorted(base_files & candidate_files):
        before = (base / name).read_text(encoding="utf-8")
        after = (candidate / name).read_text(encoding="utf-8")
        kind = name.rsplit("/", 1)[-1]
        kind = "diagnostics" if kind == "diagnostics.txt" else kind if kind == "exit" else kind.rsplit(".", 1)[-1]
        if kind not in counts:
            raise HarnessError(f"unexpected dump file {name}")
        counts[kind] += 1
        if kind == "report":
            if before != after:
                digest_changed += 1
            before = normalize_report(before, f"base {name}")
            after = normalize_report(after, f"candidate {name}")
        if before != after:
            mismatches.append(f"differs: {name}")
    for kind in ("model", "report", "diagnostics"):
        if counts[kind] == 0:
            mismatches.append(f"no {kind} compared: the dumps are not evidence")
    return {"compared": counts, "reports_with_changed_digest": digest_changed,
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


# Anchors that already do not occur exactly once on main when this check was added
# (2026-11-21, origin/main 6413bcba2), with the count observed then. These mutants
# fail as harness errors today; they are pre-existing debt, not move regressions.
# The check fails if an entry's count changes (fix it, then delete the entry) and
# for any anchor not listed here, so a move cannot add to the list silently.
KNOWN_ANCHOR_PROBLEMS = {
    ("check_byte_call_mutations", "selector-shift"): 3,
    ("check_create2_struct_emit_mutations", "import-struct-emit-payload"): 2,
    ("check_environment_mutations", "import-msg-sender"): 0,
    ("check_external_code_and_low_level_call_mutations", "denote-low-level-call-forward"): 6,
    ("check_external_code_and_low_level_call_mutations", "denote-low-level-call-short"): 3,
    ("check_scalar_array_abi_mutations", "import-scalar-array-validation"): 0,
    ("check_storage_mutations", "import-string-event-data-before-indexed-guard"): 2,
    ("check_storage_mutations", "import-if-root-swap"): 0,
    ("check_storage_mutations", "import-local-write-delete"): 0,
    ("check_storage_mutations", "import-invariant-for-bound"): 0,
    ("check_storage_mutations", "import-packed-member-delete"): 0,
    ("check_storage_mutations", "import-named-helper-frame"): 0,
    ("check_storage_mutations", "import-msg-data-and-enum-calldata-guard"): 0,
    ("check_storage_mutations", "import-multiproof-verifiers-bool-member-read-invert"): 0,
    ("check_storage_mutations", "import-votes-checkpoints-arrays-bitmaps-root-struct-return-zero"): 0,
    ("check_storage_mutations", "import-public-getters-and-builtins-revert-reason-empty"): 0,
    ("check_storage_mutations", "import-unchecked-block-root"): 0,
    ("check_struct_abi_mutations", "import-struct-memory-offset"): 2,
}


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
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--module", action="append", help="smoke module stem (default: all)")
    p.add_argument("--runner", default="", help='command prefix, e.g. "lean-job lane-equiv --"')
    p.add_argument("--probe-only", action="store_true", help="write probes, do not run Lean")
    p = sub.add_parser("compare", help="compare two dumps")
    p.add_argument("base", type=Path)
    p.add_argument("candidate", type=Path)
    p = sub.add_parser("anchors", help="check that every mutation anchor occurs exactly once")
    args = parser.parse_args(argv)
    try:
        if args.command == "targets":
            print(json.dumps(targets(args.root.resolve(), args.module), indent=2))
        elif args.command == "dump":
            manifest = dump(args.root, args.out, args.module, shlex.split(args.runner), args.probe_only)
            print(f"{sum(map(len, manifest['targets'].values()))} imports in {len(manifest['targets'])} modules")
        elif args.command == "compare":
            summary = compare(args.base, args.candidate)
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
