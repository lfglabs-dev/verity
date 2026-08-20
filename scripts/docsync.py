#!/usr/bin/env python3
"""Schema-driven doc-sync engine (P7 consolidation).

One declarative registry replaces the per-checker scripts of the
"Lean decl -> JSON artifact -> Markdown doc" pipeline described in
scripts/consolidation-inventory.md (Clusters A/B). Each entry binds an
extraction condition (interpreter feature matrix, Lean source surface, or
static expectations) to required/forbidden snippets in Markdown docs.

Usage:
    python3 scripts/docsync.py --check                       # run every entry
    python3 scripts/docsync.py --check --only <entry> [...]  # run a subset
    python3 scripts/docsync.py --list                        # list entries

Exit codes match the legacy scripts: 0 on success, 1 on any sync failure,
and per-entry stdout/stderr output is preserved byte-for-byte.

Legacy `scripts/check_*_sync.py` entry points remain as thin shims that
delegate here, so external callers keep working.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from interpreter_feature_matrix import interpreter_status, load_feature_matrix

ROOT = SCRIPT_DIR.parent
FEATURE_MATRIX_REL = "artifacts/interpreter_feature_matrix.json"


class DocSyncError(Exception):
    """Raised by extraction conditions; the message is printed verbatim to stderr."""


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def _rel(root: Path, rel_path: str) -> Path:
    return root / Path(rel_path)


# ---------------------------------------------------------------------------
# Extraction conditions (decide whether a boundary note is required)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class MatrixBoundaryCondition:
    """Boundary note required unless every feature is proved and fully supported."""

    expr_features: tuple[str, ...] = ()
    stmt_features: tuple[str, ...] = ()
    expr_missing_message: str = ""
    stmt_missing_message: str = ""

    def evaluate(self, root: Path) -> bool:
        matrix_path = _rel(root, FEATURE_MATRIX_REL)
        if not matrix_path.exists():
            raise DocSyncError(f"Missing: {FEATURE_MATRIX_REL}")
        try:
            matrix = load_feature_matrix(matrix_path)
            return self._needs_note(matrix)
        except (json.JSONDecodeError, ValueError) as exc:
            raise DocSyncError(f"{FEATURE_MATRIX_REL}: {exc}") from exc

    def _needs_note(self, matrix: dict) -> bool:
        sections = (
            ("expr_features", self.expr_features, self.expr_missing_message),
            ("stmt_features", self.stmt_features, self.stmt_missing_message),
        )
        selected: list[dict] = []
        for section, wanted, missing_message in sections:
            if not wanted:
                continue
            entries = {
                entry["feature"]: entry
                for entry in matrix.get(section, [])
                if entry.get("feature") in set(wanted)
            }
            if entries.keys() != set(wanted):
                raise ValueError(missing_message)
            selected.extend(entries.values())
        for entry in selected:
            if entry.get("proof_status") != "proved":
                return True
            if interpreter_status(entry, "SourceInterpreter_basic") != "supported":
                return True
            if interpreter_status(entry, "SourceInterpreter_fuel") != "supported":
                return True
        return False


@dataclass(frozen=True)
class LeanSurfaceCondition:
    """Docs note required when every surface token is present in a Lean source file.

    A partial surface (some tokens present, some missing) is itself an error.
    """

    source_rel: str
    tokens: tuple[str, ...]
    partial_message_prefix: str

    def evaluate(self, root: Path) -> bool:
        source_path = _rel(root, self.source_rel)
        if not source_path.exists():
            raise DocSyncError(f"Missing: {self.source_rel}")
        text = source_path.read_text(encoding="utf-8")
        present = tuple(token for token in self.tokens if token in text)
        if present and len(present) != len(self.tokens):
            missing = [t.strip() for t in self.tokens if t not in present]
            present_rendered = ", ".join(t.strip() for t in present)
            missing_rendered = ", ".join(missing)
            raise DocSyncError(
                f"{self.partial_message_prefix} "
                f"present: {present_rendered}; missing: {missing_rendered}"
            )
        return len(present) == len(self.tokens)


# ---------------------------------------------------------------------------
# Entry kinds
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ConditionalNoteEntry:
    """When the extraction condition holds, require note snippets in target docs."""

    name: str
    condition: object
    targets: dict[str, str]  # label -> repo-relative doc path
    snippets: dict[str, list[str]]  # label -> required snippets when note needed
    out_of_sync_message: str  # str.format(path=..., snippet=...)
    pass_message: str  # str.format(status="required" | "not required")

    def check(self, root: Path) -> int:
        try:
            needs_note = self.condition.evaluate(root)
        except DocSyncError as exc:
            print(str(exc), file=sys.stderr)
            return 1

        errors: list[str] = []
        for label, rel_path in self.targets.items():
            path = _rel(root, rel_path)
            if not path.exists():
                errors.append(f"Missing: {rel_path}")
                continue
            normalized = normalize_ws(path.read_text(encoding="utf-8"))
            for snippet in (self.snippets.get(label, []) if needs_note else []):
                if normalize_ws(snippet) not in normalized:
                    errors.append(
                        self.out_of_sync_message.format(path=rel_path, snippet=snippet)
                    )

        if errors:
            for error in errors:
                print(error, file=sys.stderr)
            return 1

        status = "required" if needs_note else "not required"
        print(self.pass_message.format(status=status))
        return 0


@dataclass(frozen=True)
class SnippetSyncEntry:
    """Unconditionally require (and forbid) snippets across target docs."""

    name: str
    targets: dict[str, str]
    required: dict[str, list[str]]
    forbidden: dict[str, list[str]]
    missing_message: str  # str.format(path=..., snippet=...)
    forbidden_message: str  # str.format(path=..., snippet=...)
    pass_message: str

    def check(self, root: Path) -> int:
        errors: list[str] = []
        for label, rel_path in self.targets.items():
            path = _rel(root, rel_path)
            if not path.exists():
                errors.append(f"Missing: {rel_path}")
                continue
            normalized = normalize_ws(path.read_text(encoding="utf-8"))
            for snippet in self.required.get(label, []):
                if normalize_ws(snippet) not in normalized:
                    errors.append(
                        self.missing_message.format(path=rel_path, snippet=snippet)
                    )
            for snippet in self.forbidden.get(label, []):
                if normalize_ws(snippet) in normalized:
                    errors.append(
                        self.forbidden_message.format(path=rel_path, snippet=snippet)
                    )

        if errors:
            for error in errors:
                print(error, file=sys.stderr)
            return 1

        print(self.pass_message)
        return 0


@dataclass(frozen=True)
class CategoryNoteEntry:
    """Pin feature-matrix proof-status categories and require category snippets in one doc."""

    name: str
    target_rel: str
    categories: tuple[tuple[tuple[str, ...], str, str], ...]  # (features, status, label)
    snippets: tuple[str, ...]
    out_of_sync_message: str  # str.format(path=..., snippet=...)
    pass_message: str

    def _validate_matrix(self, matrix: dict) -> None:
        status_map: dict[str, str] = {}
        for section in ("expr_features", "stmt_features"):
            entries = matrix.get(section)
            if not isinstance(entries, list):
                raise ValueError(f"interpreter feature matrix is missing {section}")
            for entry in entries:
                feature = entry.get("feature")
                status = entry.get("proof_status")
                if not isinstance(feature, str):
                    raise ValueError(f"{section} entry is missing string feature name")
                if not isinstance(status, str):
                    raise ValueError(f"{section} entry `{feature}` is missing proof_status")
                status_map[feature] = status

        for features, expected, label in self.categories:
            missing = [feature for feature in features if feature not in status_map]
            if missing:
                raise ValueError(
                    f"interpreter feature matrix is missing {label} entries: {', '.join(missing)}"
                )
            mismatched = [feature for feature in features if status_map[feature] != expected]
            if mismatched:
                rendered = ", ".join(f"{feature}={status_map[feature]}" for feature in mismatched)
                raise ValueError(f"{label} drifted from expected `{expected}` status: {rendered}")

    def check(self, root: Path) -> int:
        matrix_path = _rel(root, FEATURE_MATRIX_REL)
        target_path = _rel(root, self.target_rel)
        if not matrix_path.exists():
            print(f"Missing: {FEATURE_MATRIX_REL}", file=sys.stderr)
            return 1
        if not target_path.exists():
            print(f"Missing: {self.target_rel}", file=sys.stderr)
            return 1

        try:
            matrix = load_feature_matrix(matrix_path)
            self._validate_matrix(matrix)
        except (json.JSONDecodeError, ValueError) as exc:
            print(f"{FEATURE_MATRIX_REL}: {exc}", file=sys.stderr)
            return 1

        normalized_doc = normalize_ws(target_path.read_text(encoding="utf-8"))
        errors: list[str] = []
        for snippet in self.snippets:
            if normalize_ws(snippet) not in normalized_doc:
                errors.append(
                    self.out_of_sync_message.format(path=self.target_rel, snippet=snippet)
                )

        if errors:
            for error in errors:
                print(error, file=sys.stderr)
            return 1

        print(self.pass_message)
        return 0


@dataclass(frozen=True)
class Layer2BoundaryCatalogEntry:
    """Validate docs against the machine-readable Layer 2 boundary catalog."""

    name: str
    catalog_rel: str
    targets: dict[str, str]
    pass_message: str

    def _load_catalog(self, root: Path) -> dict:
        catalog_path = _rel(root, self.catalog_rel)
        if not catalog_path.exists():
            raise DocSyncError(f"Missing: {self.catalog_rel}")
        try:
            catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
            self._validate_catalog(catalog)
            return catalog
        except (json.JSONDecodeError, ValueError) as exc:
            raise DocSyncError(f"{self.catalog_rel}: {exc}") from exc

    def _validate_catalog(self, catalog: dict) -> None:
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

    @staticmethod
    def _lean_name(ref: str) -> str:
        return ref.rsplit(".", 1)[-1]

    def _catalog_surface_snippets(self, catalog: dict) -> list[str]:
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
        return [f"`{self._lean_name(ref)}`" for ref in refs]

    def _common_boundary_snippets(self, catalog: dict) -> list[str]:
        helper = catalog["supported_spec_split"]["helper_boundary"]
        return [
            "`artifacts/layer2_boundary_catalog.json`",
            f"`{helper['current_fail_closed_gate']}`",
            "total fuel-indexed helper-aware IR semantics",
            "direct helper-free lemmas for `stop`, `mstore`, `revert`, `return`, and mapping-slot `sstore`",
            "helper-free conservative-extension goal is now closed",
            "[#1638]",
            *self._catalog_surface_snippets(catalog),
        ]

    def expected_snippets(self, catalog: dict) -> dict[str, list[str]]:
        helper = catalog["supported_spec_split"]["helper_boundary"]
        theorem_target = catalog["theorem_target"]
        assert theorem_target["intended_claim"] == "proof_complete_macro_lowered_verity_contract_image"
        assert helper["current_fail_closed_gate"] == "SupportedBodyInterface.stmtList"
        common = self._common_boundary_snippets(catalog)
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

    def check(self, root: Path) -> int:
        try:
            catalog = self._load_catalog(root)
        except DocSyncError as exc:
            print(str(exc), file=sys.stderr)
            return 1

        errors: list[str] = []
        expected = self.expected_snippets(catalog)
        for label, rel_path in self.targets.items():
            path = _rel(root, rel_path)
            if not path.exists():
                errors.append(f"Missing: {rel_path}")
                continue
            normalized = normalize_ws(path.read_text(encoding="utf-8"))
            for snippet in expected[label]:
                if normalize_ws(snippet) not in normalized:
                    errors.append(
                        f"{rel_path} is out of sync with the Layer 2 boundary catalog: missing `{snippet}`"
                    )

        if errors:
            for error in errors:
                print(error, file=sys.stderr)
            return 1

        print(self.pass_message)
        return 0


# ---------------------------------------------------------------------------
# Registry
# ---------------------------------------------------------------------------

PROOF_BOUNDARY_TARGETS = {
    "EDSL_API": "docs-site/content/edsl/external-calls.mdx",
    "COMPILER_DOC": "docs-site/content/compiler.mdx",
    "SOLIDITY_GUIDE": "docs-site/content/guides/solidity-to-verity.mdx",
}


LOW_LEVEL_CALL_BOUNDARY = ConditionalNoteEntry(
    name="low_level_call_boundary",
    condition=MatrixBoundaryCondition(
        expr_features=("call", "staticcall", "delegatecall"),
        expr_missing_message=(
            "interpreter feature matrix is missing one or more low-level call entries"
        ),
    ),
    targets=PROOF_BOUNDARY_TARGETS,
    snippets={
        "EDSL_API": [
            "They are not yet modeled by the current proof interpreters.",
            "low-level call plumbing and returndata behavior remain a compiler-and-testing trust boundary rather than a proved semantic feature today.",
            "When the low-level form is `delegatecall`, the trust report now also isolates it as a dedicated proxy / upgradeability boundary; archive `--trust-report` and use `--deny-proxy-upgradeability` for proof-strict runs (see issue `#1420`).",
        ],
        "COMPILER_DOC": [
            "their runtime semantics are still outside the current native verified runtime model.",
            "call success / returndata mechanics remain validated by differential testing and tracked under issue `#1332`.",
            "`delegatecall` also remains a separate proxy / upgradeability trust boundary; archive `--trust-report` and add `--deny-proxy-upgradeability` if those semantics must stay outside the selected verification envelope (see issue `#1420`).",
        ],
        "SOLIDITY_GUIDE": [
            "Those low-level call mechanics compile, but they are still outside the current native verified runtime semantics;",
            "see issue `#1332`",
            "Treat `delegatecall` even more strictly: it is also tracked as a dedicated proxy / upgradeability boundary, so archive `--trust-report` and use `--deny-proxy-upgradeability` when proxy semantics must remain outside the verified subset (see issue `#1420`).",
        ],
    },
    out_of_sync_message=(
        "{path} is out of sync with low-level call proof boundary: missing `{snippet}`"
    ),
    pass_message="low-level call boundary sync passed: boundary note {status}",
)


LINEAR_MEMORY_BOUNDARY = ConditionalNoteEntry(
    name="linear_memory_boundary",
    condition=MatrixBoundaryCondition(
        expr_features=("mload", "returndataOptionalBoolAt"),
        stmt_features=("mstore", "calldatacopy", "returndataCopy"),
        expr_missing_message=(
            "interpreter feature matrix is missing one or more linear-memory expression entries"
        ),
        stmt_missing_message=(
            "interpreter feature matrix is missing one or more linear-memory statement entries"
        ),
    ),
    targets=PROOF_BOUNDARY_TARGETS,
    snippets={
        "EDSL_API": [
            "First-class linear-memory forms (`Expr.mload`, `Stmt.mstore`, `Stmt.returndataCopy`, `Expr.returndataOptionalBoolAt`) also compile today, but they are still only partially modeled by the current proof interpreters.",
            "treat them as an explicit memory/ABI trust boundary, archive `--trust-report`, and use `--deny-linear-memory-mechanics` for proof-strict runs (see issue `#1411`).",
        ],
        "COMPILER_DOC": [
            "Memory-oriented intrinsics (`mload`, `mstore`, `returndataCopy`, `returndataOptionalBoolAt`) compile, but the current proof interpreters still model them only partially.",
            "surface that boundary with `--trust-report` / `--deny-linear-memory-mechanics`; the remaining gap is tracked under issue `#1411`.",
        ],
        "SOLIDITY_GUIDE": [
            "Manual ABI or memory plumbing (`mload` / `mstore` / copy-based payload handling) compiles, but it is still outside the fully proved interpreter semantics today.",
            "use `--deny-linear-memory-mechanics` if the translated contract must stay inside the proved subset (see issue `#1411`).",
        ],
    },
    out_of_sync_message=(
        "{path} is out of sync with linear-memory proof boundary: missing `{snippet}`"
    ),
    pass_message="linear-memory boundary sync passed: boundary note {status}",
)


AXIOMATIZED_PRIMITIVE_BOUNDARY = ConditionalNoteEntry(
    name="axiomatized_primitive_boundary",
    condition=MatrixBoundaryCondition(
        expr_features=("keccak256",),
        expr_missing_message=(
            "interpreter feature matrix is missing one or more axiomatized primitive entries"
        ),
    ),
    targets=PROOF_BOUNDARY_TARGETS,
    snippets={
        "EDSL_API": [
            "`Expr.keccak256` also remains an explicit proof boundary today: the compiler supports it directly, but the current proof stack still treats dynamic memory hashing as an explicit primitive assumption instead of a fully modeled operation.",
            "archive `--trust-report` and use `--deny-axiomatized-primitives` for proof-strict runs (see issue `#1411`).",
        ],
        "COMPILER_DOC": [
            "The `keccak256` intrinsic also compiles, but dynamic memory hashing remains an explicit primitive assumption in the current proof stack rather than a fully modeled operation.",
            "archive `--trust-report` and add `--deny-axiomatized-primitives` if the selected contracts must stay inside the proved subset (see issue `#1411`).",
        ],
        "SOLIDITY_GUIDE": [
            "Raw `keccak256` hashing also compiles through the typed intrinsic surface, but dynamic memory hashing still relies on an explicit primitive assumption in the current proof stack.",
            "archive `--trust-report`, and use `--deny-axiomatized-primitives` when the translated contract must stay inside the proved subset (see issue `#1411`).",
        ],
    },
    out_of_sync_message=(
        "{path} is out of sync with axiomatized-primitive proof boundary: missing `{snippet}`"
    ),
    pass_message="axiomatized-primitive boundary sync passed: boundary note {status}",
)


STRUCT_MAPPING_SURFACE = ConditionalNoteEntry(
    name="struct_mapping_surface",
    condition=LeanSurfaceCondition(
        source_rel="Compiler/CompilationModel/Types.lean",
        tokens=(
            "| mappingStruct ",
            "| mappingStruct2 ",
            "| structMember ",
            "| structMember2 ",
            "| setStructMember ",
            "| setStructMember2 ",
        ),
        partial_message_prefix=(
            "Compiler/CompilationModel/Types.lean has partial struct-mapping surface support;"
        ),
    ),
    targets={
        "ROADMAP": "docs/ROADMAP.md",
        "COMPILER_DOC": "docs-site/content/compiler.mdx",
        "ADD_CONTRACT": "docs-site/content/guides/add-contract.mdx",
    },
    snippets={
        "ROADMAP": [
            "FieldType.mappingStruct` / `FieldType.mappingStruct2` plus `Expr.structMember` / `Stmt.setStructMember` now make struct-valued mappings and packed submembers first-class",
        ],
        "COMPILER_DOC": [
            '`structMember "f" key "member"`',
            '`structMember2 "f" k1 k2 "member"`',
            '`setStructMember "f" key "member" val`',
            '`setStructMember2 "f" k1 k2 "member" val`',
            "For Morpho-style `mapping(K => Struct)` / `mapping(K1 => mapping(K2 => Struct))` layouts, declare `FieldType.mappingStruct` / `FieldType.mappingStruct2`",
        ],
        "ADD_CONTRACT": [
            "`generate_contract.py` currently scaffolds scalar fields plus simple `mapping(address => uint256)` / `mapping(uint256 => uint256)` storage only.",
            "For `mappingStruct` / `mappingStruct2` layouts with packed members, use the native `verity_contract` storage forms `MappingStruct(...)` / `MappingStruct2(...)` and the corresponding `structMember` / `setStructMember` operations directly.",
        ],
    },
    out_of_sync_message=(
        "{path} is out of sync with struct-mapping compiler support: missing `{snippet}`"
    ),
    pass_message="struct-mapping surface sync passed: docs note {status}",
)


LAYER2_BOUNDARY = SnippetSyncEntry(
    name="layer2_boundary",
    targets={
        "AXIOMS": "AXIOMS.md",
        "COMPILER_PROOFS_README": "Compiler/Proofs/README.md",
        "VERIFICATION_STATUS": "docs/VERIFICATION_STATUS.md",
        "ROADMAP": "docs/ROADMAP.md",
        "ROOT_README": "README.md",
        "TRUST_ASSUMPTIONS": "TRUST_ASSUMPTIONS.md",
        "DOCS_SITE_COMPILER": "docs-site/content/compiler.mdx",
        "DOCS_SITE_INDEX": "docs-site/content/index.mdx",
        "DOCS_SITE_EXAMPLES": "docs-site/content/examples.mdx",
        "DOCS_SITE_FIRST_CONTRACT": "docs-site/content/first-contract.mdx",
        "DOCS_SITE_VERIFICATION": "docs-site/content/verification.mdx",
        "LLMS": "docs-site/public/llms.txt",
    },
    required={
        "AXIOMS": [
            "### 1. `solidityMappingSlot_lt_evmModulus` (eliminated)",
            "- Active axioms: 1",
            "`solidityMappingSlot_injective`",
        ],
        "COMPILER_PROOFS_README": [
            "Generic whole-contract theorem",
            "0 sorry, 0 axioms",
        ],
        "VERIFICATION_STATUS": [
            "## Layer 2: CompilationModel → IR — GENERIC WHOLE-CONTRACT THEOREM",
            "a whole-contract theorem surface, [`compile_preserves_semantics`](../Compiler/Proofs/IRGeneration/Contract.lean), quantified over arbitrary supported `CompilationModel`s",
            "What is not fully migrated yet",
            "No Lean axioms remain in Layer 2",
        ],
        "ROADMAP": [
            "🟢 **Layer 2 Generic Theorem**",
            "generic whole-contract `CompilationModel.compile` theorem is proved for the current supported fragment",
        ],
        "ROOT_README": [
            "a generic whole-contract theorem covers the supported fragment with zero axioms",
            "The dispatch bridge is an explicit theorem hypothesis, not an axiom.",
            "0 axioms",
        ],
        "TRUST_ASSUMPTIONS": [
            "Layer 2: SUPPORTED-FRAGMENT GENERIC THEOREM -- CompilationModel → IR",
            "A generic whole-contract theorem is proved for the current supported `CompilationModel` fragment.",
            "former generic body-simulation axiom has been eliminated",
            "it now has 1 documented Lean axiom",
            "explicit theorem hypothesis rather than a Lean axiom",
        ],
        "DOCS_SITE_COMPILER": [
            "**Layer 2 boundary today**",
            "the generic whole-contract `CompilationModel -> IR` theorem is proved for the current explicit supported fragment.",
            "former exact-state body-simulation axiom has been eliminated",
            "explicit theorem hypothesis rather than a Lean axiom",
        ],
        "DOCS_SITE_INDEX": [
            "`Compiler/Proofs/IRGeneration/Contract.lean` (generic whole-contract `CompilationModel -> IR` theorem for the current supported fragment)",
        ],
        "DOCS_SITE_EXAMPLES": [
            "`Compiler/Proofs/IRGeneration/Contract.lean` for the current supported fragment",
        ],
        "DOCS_SITE_FIRST_CONTRACT": [
            "the compiler-level `CompilationModel -> IR` result now lives in `Compiler/Proofs/IRGeneration/Contract.lean`",
        ],
        "DOCS_SITE_VERIFICATION": [
            "**Generic whole-contract Layer 2 theorem**: `Compiler/Proofs/IRGeneration/Contract.lean`",
        ],
        "LLMS": [
            "Generic whole-contract theorem for the supported fragment. 0 axioms.",
            "1 documented Lean axiom",
        ],
    },
    forbidden={
        "COMPILER_PROOFS_README": [
            "it still depends on 2 documented axioms in `Compiler.Proofs.IRGeneration.Function`",
            "generic body simulation and `execIRFunctionFuel`/`execIRFunction` bridging",
        ],
        "AXIOMS": [
            "### 2. `supported_function_body_correct_from_exact_state`",
            "supported_function_body_correct_from_exact_state",
            "- Active axioms: 3",
            "- Active axioms: 0",
        ],
        "VERIFICATION_STATUS": [
            "## Layer 2: CompilationModel → IR — COMPLETE",
            "it still depends on 2 documented Layer-2 axioms",
            "Still axiomatized: generic supported body simulation and the `execIRFunctionFuel` to `execIRFunction` bridge",
            "PARTIAL GENERIC, 2 AXIOMS, CONTRACT BRIDGES ACTIVE",
            "there is not yet a single compiler-level theorem quantified over arbitrary supported `CompilationModel` programs and successful `CompilationModel.compile` output.",
        ],
        "ROADMAP": [
            "✅ **Layer 2 Complete**",
            "Layer 2 Partial Generic",
        ],
        "ROOT_README": [
            "Layer 2: CompilationModel → IR        [PROVEN]",
            "| 2 | CompilationModel → IR preserves behavior |",
            "depends on 2 documented axioms",
            "documented bridge axiom",
            "1 generic non-core Layer 2 axiom",
            "There are currently 4 documented Lean axioms in total",
            "There is currently 1 documented Lean axiom in total",
        ],
        "TRUST_ASSUMPTIONS": [
            "FULLY VERIFIED — CompilationModel → IR",
            "All three layers are proven in Lean",
            "2 documented sub-axioms for generic body simulation and the `execIRFunctionFuel`/`execIRFunction` bridge",
            "4 documented Lean axioms",
            "1 documented bridge axiom",
            "2 documented axioms in [AXIOMS.md](AXIOMS.md): 1 selector axiom and 1 generic non-core Layer 2 axiom",
            "Layer 3: GENERIC SURFACE, 1 axiom — IR → Yul",
            "1 Layer 3 dispatch bridge axiom",
        ],
        "DOCS_SITE_COMPILER": [
            "**Layer 2 framework proof**: `CompilationModel -> IR` preserves semantics.",
            "depends on 2 documented axioms.",
            "1 documented bridge axiom",
            "depends on 1 documented axiom",
            "full-contract Layer 2 preservation still relies on contract-specific bridge theorems.",
        ],
        "DOCS_SITE_FIRST_CONTRACT": [
            "18 proof terms currently use `sorry`",
        ],
        "LLMS": [
            "CompilationModel -> IR preservation",
            "3 documented axioms",
            "4 documented axioms",
            "partial generic CompilationModel -> IR boundary",
        ],
    },
    missing_message=(
        "{path} is out of sync with the Layer 2 boundary: missing `{snippet}`"
    ),
    forbidden_message=(
        "{path} still over-claims the Layer 2 boundary: found forbidden snippet `{snippet}`"
    ),
    pass_message="layer2 boundary sync passed: generic Layer 2 theorem boundary documented",
)


INTERPRETER_FEATURE_BOUNDARY_CATALOG = CategoryNoteEntry(
    name="interpreter_feature_boundary_catalog",
    target_rel="docs/INTERPRETER_FEATURE_MATRIX.md",
    categories=(
        (("blockNumber", "contractAddress", "chainid"), "partial", "runtime introspection"),
        (("mload", "mstore", "returndataOptionalBoolAt"), "partial", "single-word linear memory"),
        (("returndataCopy", "revertReturndata"), "partial", "no-call returndata"),
        (
            (
                "keccak256",
                "call",
                "staticcall",
                "delegatecall",
                "rawLog",
                "externalCallBind",
                "ecm",
            ),
            "not_modeled",
            "not-modeled proof-boundary",
        ),
    ),
    snippets=(
        "Partially modeled features currently include runtime introspection "
        "(`blockNumber`, `contractAddress`, `chainid`) and single-word linear-memory forms "
        "(`mload`, `mstore`, `returndataOptionalBoolAt`).",
        "The same no-call invariant admits `revertReturndata`: its generated `returndatasize()` "
        "is zero, so it proves the exact empty revert `revert(0, 0)`.",
        "Fully not-modeled features currently include `keccak256`, low-level call plumbing "
        "(`call`, `staticcall`, `delegatecall`), event emission (`rawLog`), and external call modules "
        "(`externalCallBind`, `ecm`).",
    ),
    out_of_sync_message=(
        "{path} is out of sync with interpreter proof-boundary categories: missing `{snippet}`"
    ),
    pass_message="interpreter feature boundary catalog sync passed",
)


LAYER2_BOUNDARY_CATALOG = Layer2BoundaryCatalogEntry(
    name="layer2_boundary_catalog",
    catalog_rel="artifacts/layer2_boundary_catalog.json",
    targets={
        "ROADMAP": "docs/ROADMAP.md",
        "VERIFICATION_STATUS": "docs/VERIFICATION_STATUS.md",
        "COMPILER_PROOFS_README": "Compiler/Proofs/README.md",
    },
    pass_message=(
        "layer2 boundary catalog sync passed: docs reference the machine-readable Layer 2 boundary"
    ),
)


ENTRIES = {
    entry.name: entry
    for entry in (
        LOW_LEVEL_CALL_BOUNDARY,
        LINEAR_MEMORY_BOUNDARY,
        AXIOMATIZED_PRIMITIVE_BOUNDARY,
        STRUCT_MAPPING_SURFACE,
        LAYER2_BOUNDARY,
        LAYER2_BOUNDARY_CATALOG,
        INTERPRETER_FEATURE_BOUNDARY_CATALOG,
    )
}


# ---------------------------------------------------------------------------
# Engine
# ---------------------------------------------------------------------------


def get_entry(name: str):
    return ENTRIES[name]


def run_entry(name: str, root: Path | None = None) -> int:
    return ENTRIES[name].check(root if root is not None else ROOT)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Schema-driven doc-sync engine")
    parser.add_argument(
        "--check",
        action="store_true",
        help="Run sync checks (default; all current entries are check-only).",
    )
    parser.add_argument(
        "--only",
        action="append",
        help="Run only the selected entry. Can be repeated or comma-separated.",
    )
    parser.add_argument("--list", action="store_true", help="List registered entries")
    parser.add_argument(
        "--root",
        type=Path,
        default=None,
        help="Repository root override (used by tests).",
    )
    args = parser.parse_args(argv)

    if args.list:
        for name in sorted(ENTRIES):
            print(name)
        return 0

    selected: list[str] = []
    for raw in args.only or []:
        selected.extend(part for part in raw.split(",") if part)
    unknown = [name for name in selected if name not in ENTRIES]
    if unknown:
        print(f"Unknown docsync entries: {', '.join(unknown)}", file=sys.stderr)
        return 2
    if not selected:
        selected = sorted(ENTRIES)

    rc = 0
    for name in selected:
        rc = max(rc, run_entry(name, root=args.root))
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
