#!/usr/bin/env python3
"""Guard high-level Lean import boundaries between macro, model, and proof layers."""

from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path

from property_utils import ROOT, extract_lean_import_modules, strip_lean_comments


@dataclass(frozen=True)
class ImportRule:
    name: str
    root: Path
    forbidden: tuple[str, ...]
    message: str
    allowed_imports: tuple[str, ...] = ()
    allowed_path_imports: tuple[tuple[str, str], ...] = ()


PRODUCTION_ROOTS = (
    ROOT / "Verity" / "Macro",
    ROOT / "Compiler" / "CompilationModel",
    ROOT / "Compiler" / "Proofs" / "IRGeneration",
    ROOT / "Compiler" / "Proofs" / "YulGeneration",
)

QUARANTINED_PATH_PARTS = {
    "fixtures",
    "generated",
    "Interop",
}

QUARANTINED_SUFFIXES = (
    "Test.lean",
    "FeatureTest.lean",
    "Smoke.lean",
)

BRIDGE_PROOF_IMPORTS = (
    "Compiler.Proofs.YulGeneration.IRFuel",
    "Compiler.Proofs.YulGeneration.LogNames",
    "Compiler.Proofs.YulGeneration.RuntimeTypes",
    "Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas",
    "Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgePredicates",
    "Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBuiltinSemantics",
    "Compiler.Proofs.YulGeneration.Backends.EvmYulLeanPureBuiltinLemmas",
)

RULES = (
    ImportRule(
        name="macro-to-compiler",
        root=ROOT / "Verity" / "Macro",
        forbidden=("Compiler.",),
        allowed_imports=(
            "Compiler.CompilationModel",
            "Compiler.Selector",
            "Compiler.Selectors",
            "Compiler.ECM",
            "Compiler.ProofStatus",
        ),
        allowed_path_imports=(
            ("Verity/Macro/Translate.lean", "Compiler.Modules."),
            ("Verity/Macro/Translate.lean", "Compiler.Keccak.Sponge"),
            ("Verity/Macro/Translate/Expr.lean", "Compiler.Modules."),
            ("Verity/Macro/Translate/Expr.lean", "Compiler.Keccak.Sponge"),
            ("Verity/Macro/KeccakLit.lean", "Compiler.Keccak.Sponge"),
        ),
        message=(
            "Verity/Macro production code may only import the compilation model, "
            "selectors, ECM metadata, and syntax/core support"
        ),
    ),
    ImportRule(
        name="compilationmodel-no-macro",
        root=ROOT / "Compiler" / "CompilationModel",
        forbidden=("Verity.Macro",),
        message="Compiler/CompilationModel must not import macro code",
    ),
    ImportRule(
        name="ir-proofs-no-native-backend",
        root=ROOT / "Compiler" / "Proofs" / "IRGeneration",
        forbidden=(
            "Compiler.Proofs.YulGeneration.",
        ),
        allowed_imports=BRIDGE_PROOF_IMPORTS,
        message=(
            "Compiler/Proofs/IRGeneration may use model/compiler semantics and "
            "Yul bridge interfaces, but not Yul-native backend proof modules directly"
        ),
    ),
    ImportRule(
        name="yul-proofs-no-macro",
        root=ROOT / "Compiler" / "Proofs" / "YulGeneration",
        forbidden=("Verity.Macro",),
        message="Compiler/Proofs/YulGeneration must not reach back into macro syntax",
    ),
)


def _render_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def _matches_module(module_name: str, prefix: str) -> bool:
    if prefix.endswith("."):
        return module_name.startswith(prefix)
    return module_name == prefix or module_name.startswith(f"{prefix}.")


def _is_quarantined(path: Path) -> bool:
    if path.name.endswith(QUARANTINED_SUFFIXES):
        return True
    parts = set(path.parts)
    return bool(parts.intersection(QUARANTINED_PATH_PARTS))


def _is_allowed(rule: ImportRule, path: Path, module_name: str) -> bool:
    for allowed in rule.allowed_imports:
        if _matches_module(module_name, allowed):
            return True

    rendered = _render_path(path)
    rendered_posix = path.as_posix()
    for path_suffix, allowed in rule.allowed_path_imports:
        if (
            (rendered == path_suffix or rendered_posix.endswith(path_suffix))
            and _matches_module(module_name, allowed)
        ):
            return True

    return False


def _lean_files(root: Path) -> list[Path]:
    if not root.exists():
        return []
    return sorted(path for path in root.rglob("*.lean") if not _is_quarantined(path))


def collect_layer_import_failures(rules: tuple[ImportRule, ...] = RULES) -> list[str]:
    failures: list[str] = []
    for rule in rules:
        for path in _lean_files(rule.root):
            contents = strip_lean_comments(path.read_text(encoding="utf-8"))
            for line_no, line in enumerate(contents.splitlines(), 1):
                for module_name in extract_lean_import_modules(line):
                    if not any(_matches_module(module_name, forbidden) for forbidden in rule.forbidden):
                        continue
                    if _is_allowed(rule, path, module_name):
                        continue
                    failures.append(
                        f"{_render_path(path)}:{line_no}: {rule.name}: "
                        f"forbidden import `{module_name}` ({rule.message})"
                    )
    return failures


def main_for_rules(rules: tuple[ImportRule, ...] = RULES) -> int:
    failures = collect_layer_import_failures(rules)
    if failures:
        print("Layer import boundary check failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print("Layer import boundary check passed.")
    return 0


def main() -> int:
    return main_for_rules()


if __name__ == "__main__":
    raise SystemExit(main())
