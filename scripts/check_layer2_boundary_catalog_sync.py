#!/usr/bin/env python3
"""Keep Layer 2 docs aligned with the machine-readable boundary catalog."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CATALOG = ROOT / "artifacts" / "layer2_boundary_catalog.json"
TARGET_FILES = {
    "ROADMAP": ROOT / "docs" / "ROADMAP.md",
    "VERIFICATION_STATUS": ROOT / "docs" / "VERIFICATION_STATUS.md",
    "COMPILER_PROOFS_README": ROOT / "Compiler" / "Proofs" / "README.md",
}


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def load_catalog(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def validate_catalog(catalog: dict) -> None:
    target = catalog.get("theorem_target", {})
    if target.get("intended_claim") != "proof_complete_macro_lowered_verity_contract_image":
        raise ValueError("unexpected theorem target claim in Layer 2 boundary catalog")
    if target.get("excludes_arbitrary_lean_compilation_models") is not True:
        raise ValueError("Layer 2 boundary catalog must exclude arbitrary Lean-produced models")

    helper = catalog.get("supported_spec_split", {}).get("helper_boundary", {})
    if helper.get("current_fail_closed_gate") != "SupportedBodyInterface.stmtList":
        raise ValueError("Layer 2 boundary catalog is missing the helper fail-closed gate")
    if not helper.get("blocking_seams"):
        raise ValueError("Layer 2 boundary catalog is missing helper blocking seams")


def lean_name(ref: str) -> str:
    return ref.rsplit(".", 1)[-1]


def catalog_surface_snippets(catalog: dict) -> list[str]:
    helper = catalog["supported_spec_split"]["helper_boundary"]
    compat = helper["compiled_target_compatibility_subset"]
    source_helper = helper["source_helper_goal_surface"]
    compiled_target = helper["compiled_target_proof_surface"]

    refs = [
        compat["goal_surface"],
        compat["dispatch_goal_surface"],
        compat["goal_composition_surface"],
        compat["goal_decomposition_surface"],
        compat["interface_builder_surface"],
        compat["stmt_subgoal_surface"],
        compat["stmt_subgoal_closed_surface"],
        compat["expr_stmt_dedicated_builtin_classifier"],
        source_helper["direct_body_goal"],
        source_helper["direct_body_goal_helper_ir"],
        catalog["current_theorem"]["helper_ir_goal_ready_variant"],
        catalog["current_theorem"]["helper_ir_closed_variant"],
        compiled_target["source"],
    ]
    return [f"`{lean_name(ref)}`" for ref in refs]


def common_boundary_snippets(catalog: dict) -> list[str]:
    helper = catalog["supported_spec_split"]["helper_boundary"]
    return [
        "`artifacts/layer2_boundary_catalog.json`",
        f"`{helper['current_fail_closed_gate']}`",
        "total fuel-indexed helper-aware IR semantics",
        "direct helper-free lemmas for `stop`, `mstore`, `revert`, `return`, and mapping-slot `sstore`",
        "helper-free conservative-extension goal is now closed",
        "[#1638]",
        *catalog_surface_snippets(catalog),
    ]


def expected_snippets(catalog: dict) -> dict[str, list[str]]:
    helper = catalog["supported_spec_split"]["helper_boundary"]
    theorem_target = catalog["theorem_target"]
    assert theorem_target["intended_claim"] == "proof_complete_macro_lowered_verity_contract_image"
    assert helper["current_fail_closed_gate"] == "SupportedBodyInterface.stmtList"
    common = common_boundary_snippets(catalog)
    return {
        "ROADMAP": [
            *common,
            "macro-lowered `verity_contract` image",
            "`SupportedStmtList.helperSurfaceClosed`",
            "`execIRFunctionWithInternals` / `interpretIRWithInternals`",
            "conservative extension of `interpretIR`",
        ],
        "VERIFICATION_STATUS": [
            *common,
            "macro-lowered image of `verity_contract`",
            "`SupportedBodyInterface.stmtList` gate",
            "helper-aware body theorem does not yet consume helper-summary soundness/rank evidence",
            "legacy-compatible external-body Yul subset",
        ],
        "COMPILER_PROOFS_README": [
            *common,
            "`SupportedSpec` split",
            "`calls.helpers`",
            "summary-soundness evidence",
            "legacy-compatible external-body Yul subset",
        ],
    }


def main() -> int:
    if not CATALOG.exists():
        print(f"Missing: {CATALOG.relative_to(ROOT)}", file=sys.stderr)
        return 1

    try:
        catalog = load_catalog(CATALOG)
        validate_catalog(catalog)
    except (json.JSONDecodeError, ValueError) as exc:
        print(f"{CATALOG.relative_to(ROOT)}: {exc}", file=sys.stderr)
        return 1

    errors: list[str] = []
    expected = expected_snippets(catalog)
    for label, path in TARGET_FILES.items():
        if not path.exists():
            errors.append(f"Missing: {path.relative_to(ROOT)}")
            continue
        normalized = normalize_ws(path.read_text(encoding="utf-8"))
        for snippet in expected[label]:
            if normalize_ws(snippet) not in normalized:
                errors.append(
                    f"{path.relative_to(ROOT)} is out of sync with the Layer 2 boundary catalog: missing `{snippet}`"
                )

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print("layer2 boundary catalog sync passed: docs reference the machine-readable Layer 2 boundary")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
