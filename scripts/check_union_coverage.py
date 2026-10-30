#!/usr/bin/env python3
"""Verify that Verity's whole-library axiom union covers the exact verified population.

Checks two fail-closed invariants on source alone (no Lean invocation needed):
1. No verified module under ``Verity``, ``Compiler``, or ``Contracts`` imports a
   non-verified local module.
2. ``scripts/VerityUnionAxioms.lean`` (and ``PrintAxioms.lean``) transitively
   imports every verified module and zero non-verified local modules.

Usage:
    python3 scripts/check_union_coverage.py
"""

from __future__ import annotations

import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from property_utils import ROOT, extract_lean_import_modules, strip_lean_comments

TOP_NAMESPACES: tuple[str, ...] = ("Verity", "Compiler", "Contracts")

# Non-verified CLI drivers, executable frontends, umbrellas that pull in tests/smoke,
# and Foundry/differential test runners.
EXACT_EXCLUDED_MODULES: frozenset[str] = frozenset(
    {
        "Compiler",
        "Contracts",
        "Compiler.Codegen.Profile",
        "Compiler.Codegen.AccelPlugin",
        "Compiler.Main",
        "Compiler.MainDriver",
        "Compiler.CompileDriver",
        "Compiler.CompileDriverCommon",
        "Compiler.ModuleInput",
        "Compiler.CheckContract",
        "Compiler.Gas.Report",
        "Compiler.Gas.StaticAnalysis",
        "Compiler.RandomGen",
        "Compiler.DiffTestTypes",
        "Contracts.Interpreter",
        "Compiler.SolidityImport",
        "Compiler.SolidityImport.Differential",
        "Compiler.SolidityImport.SequenceRunner",
        "Compiler.SolidityImport.ByteCallTransactions",
        "Compiler.SolidityImport.CallResponderMocks",
        "Compiler.SolidityImport.StaticOracleMocks",
    }
)

EXCLUDED_PATH_PARTS: frozenset[str] = frozenset({"Autoresearch", "Examples"})
EXCLUDED_STEM_SUFFIXES: tuple[str, ...] = ("Test", "FeatureTest", "TestRunner")


def is_local_namespace_module(module: str) -> bool:
    return any(
        module == ns or module.startswith(f"{ns}.") for ns in TOP_NAMESPACES
    )


def is_verified_module(module: str, rel_path: Path) -> bool:
    if module in EXACT_EXCLUDED_MODULES:
        return False
    parts = rel_path.with_suffix("").parts
    if any("Smoke" in part for part in parts):
        return False
    if any(part in EXCLUDED_PATH_PARTS for part in parts):
        return False
    stem = parts[-1]
    if stem.endswith(EXCLUDED_STEM_SUFFIXES):
        return False
    return True


def discover_population(
    root: Path = ROOT,
) -> tuple[dict[str, Path], set[str], dict[str, list[str]], list[str]]:
    """Return ``(disk_map, verified_modules, imports_map, root_modules)``."""
    all_paths: list[Path] = []
    for ns in TOP_NAMESPACES:
        umbrella = root / f"{ns}.lean"
        if umbrella.is_file():
            all_paths.append(umbrella)
        tree = root / ns
        if tree.is_dir():
            all_paths.extend(sorted(tree.rglob("*.lean")))

    if not all_paths:
        raise ValueError("missing Verity/Compiler/Contracts source trees")

    disk_map: dict[str, Path] = {}
    verified: set[str] = set()
    for path in all_paths:
        rel = path.relative_to(root)
        module = ".".join(rel.with_suffix("").parts)
        disk_map[module] = path
        if is_verified_module(module, rel):
            verified.add(module)

    if not verified:
        raise ValueError("verified population is empty")

    imports_map: dict[str, list[str]] = {}
    leaks: list[str] = []
    for module in sorted(verified):
        text = strip_lean_comments(disk_map[module].read_text(encoding="utf-8"))
        local_imports: list[str] = []
        for line in text.splitlines():
            for imp in extract_lean_import_modules(line):
                if not is_local_namespace_module(imp):
                    continue
                if imp not in disk_map:
                    raise ValueError(
                        f"missing local dependency imported by {module}: {imp}"
                    )
                if imp not in verified:
                    leaks.append(f"{module} -> {imp}")
                local_imports.append(imp)
        imports_map[module] = local_imports

    if leaks:
        raise ValueError(
            "verified modules import non-verified local modules: "
            + ", ".join(leaks)
        )

    imported_by_other: set[str] = set()
    for module, imps in imports_map.items():
        for imp in imps:
            if imp in verified and imp != module:
                imported_by_other.add(imp)

    roots = sorted(verified - imported_by_other)
    return disk_map, verified, imports_map, roots


def check_target_coverage(
    target_file: Path,
    disk_map: dict[str, Path],
    verified: set[str],
    imports_map: dict[str, list[str]],
) -> int:
    if not target_file.is_file():
        raise ValueError(f"missing union-audit file: {target_file}")

    text = strip_lean_comments(target_file.read_text(encoding="utf-8"))
    direct_imports: list[str] = []
    for line in text.splitlines():
        direct_imports.extend(extract_lean_import_modules(line))

    pending: list[str] = []
    for imp in direct_imports:
        if not is_local_namespace_module(imp):
            continue
        if imp not in disk_map:
            raise ValueError(f"missing local union-audit dependency: {imp}")
        if imp not in verified:
            raise ValueError(
                f"{target_file.name} imports non-verified local module: {imp}"
            )
        pending.append(imp)

    reached: set[str] = set()
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        pending.extend(imports_map[module])

    missing = sorted(verified - reached)
    if missing:
        raise ValueError(
            f"modules outside {target_file.name} whole-library axiom audit: "
            + ", ".join(missing)
        )
    return len(reached)


def check_union_coverage(root: Path = ROOT) -> int:
    disk_map, verified, imports_map, _ = discover_population(root)
    union_count = check_target_coverage(
        root / "scripts" / "VerityUnionAxioms.lean",
        disk_map,
        verified,
        imports_map,
    )
    print_axioms_path = root / "PrintAxioms.lean"
    if print_axioms_path.is_file():
        check_target_coverage(print_axioms_path, disk_map, verified, imports_map)
    return union_count


def main() -> int:
    try:
        covered = check_union_coverage(ROOT)
    except (OSError, ValueError) as exc:
        print(f"REGRESSION — union coverage: {exc}", file=sys.stderr)
        return 1
    print(
        f"OK — whole-library axiom union covers all {covered} verified Verity modules "
        "(0 non-verified local imports)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
