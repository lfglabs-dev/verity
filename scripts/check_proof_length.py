#!/usr/bin/env python3
"""Check proof lengths and enforce size limits.

Enforces the proof hygiene guideline from CONTRIBUTING.md:
- Proofs should be under 30 lines.
- Proofs over 50 lines require an entry in the allowlist below.
- New proofs exceeding the hard limit without an allowlist entry fail CI.

Usage:
    python3 scripts/check_proof_length.py
    python3 scripts/check_proof_length.py --format=markdown   # summary table
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from property_utils import ROOT, THEOREM_RE, strip_lean_comments

# Any new declaration keyword that ends the current proof span.
_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:(?:partial)\s+)?"
    r"(?:theorem|lemma|def|example|instance|inductive|structure|class|abbrev|opaque)"
    r"(?:\s+|$)"
)
# A theorem header whose name is on the following line (used for names that
# would not fit in 100 columns), e.g. `theorem` alone, then `    longName`.
_SPLIT_THEOREM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected)\s+)*(?:theorem|lemma)\s*$"
)
_SPLIT_NAME_RE = re.compile(r"^\s*(?P<name>[A-Za-z_][A-Za-z0-9_.']*)\b")
_END_RE = re.compile(r"^\s*end\b")
_SECTION_RE = re.compile(r"^\s*(?:section|namespace)\b")

SOFT_LIMIT = 30
HARD_LIMIT = 50

# Existing proofs that exceed HARD_LIMIT. Each entry was reviewed and accepted
# before the check was introduced. New proofs must not be added here without a
# justification comment in the PR explaining why decomposition is not feasible.
ALLOWLIST: set[str] = {
    # Native selected-body handoff: splits generated switch-case freshness into
    # the actual lowered user-body freshness used by the remaining native
    # selected-body execution bridge.
    "nativeGeneratedSelectedUserBodyMatchedFresh_of_switchFresh",
    # Native selected-body handoff: packages compile-derived closure facts with
    # switch-freshness-derived matched-flag freshness for the actual lowered
    # user body. This deliberately stays private until the execution bridge is
    # closed.
    "selectedUserBodyClosureAndMatchedFresh_of_compile_ok_supported_switchFresh",
    # --- SimpleStorage native EVMYulLean dispatcher closed forms ---
    # These are concrete generated-code reductions for the store(uint256)
    # selected path. The long proofs are linear fuel/body-shape plumbing over
    # generated Yul and are kept local to the Phase 3 bridge discharge.
    "exec_block_simpleStorageLoweredStoreCaseBodyTail3_halt",
    "simpleStorageNativeContract_dispatcherExec_storeHit_halt_atFuel",
    # Phase 3 short-calldata store-hit endpoint: same generated dispatcher
    # plumbing as the halt endpoint, but the selected body takes the ABI
    # argument-length revert branch before reaching the store payload.
    "simpleStorageNativeContract_dispatcherExec_storeHit_short_revert_atFuel",
    # Phase 3 store-hit storage projection: zero sstore erases the EVM RBMap
    # key, while the IR stores a bounded zero word. The proof must split zero
    # and nonzero writes plus same-key/other-key projected lookups.
    "projectStorageFromState_storeHit_initialState_materialized",
    # Phase 2 retrieve-hit prerequisites: closed-form interpretIR reduction
    # over the retrieve body's two-statement form (`mstore(0, sload(0));
    # return(0, 32)`); the proof must walk the EDSL execIRStmts/execIRStmt
    # state machine through the call/expr/builtin layers and discharge a
    # fuel-bound side condition. Cannot be split without exposing internal
    # IR-evaluation helpers.
    "interpretIR_simpleStorage_retrieveHit",
    # Phase 2 retrieve-hit prerequisites: dispatcher-exec halt-form chain.
    # Composes the body-level closed form with the existing tail3 reduction
    # endpoint after opening the source-lowered existential and pinning the
    # switch case shape. The 155-line span is the union of fuel-reshape,
    # existential-opening, body-state plumbing, and `_via_reduction`'s
    # decomposition obligation; each piece is mechanical but inseparable.
    "simpleStorageNativeContract_dispatcherExec_retrieveHit_halt_atFuel",
    # Phase 2 retrieve-hit prerequisites: closed-form `projectResult`
    # evaluation on the YulHalt halt produced by the lowered retrieve body.
    # The proof must thread `mstore0_then_return32_*` harness lemmas across
    # the chained `setMachineState` overrides to extract the 32-byte
    # `H_return` window before computing `projectHaltReturn`.
    "projectResult_retrieveHit_eq",
    # Direct native-vs-IR retrieve-hit closure: intentionally mirrors the
    # concrete native dispatcher halt and projected-storage plumbing above, but
    # targets `nativeDispatcherExecMatchesIRPositive` directly.
    "simpleStorageNativeRetrieveHitMatchBridge_proved",
    # Direct native-vs-IR store-hit closure: it intentionally keeps the
    # short-calldata revert and argument-present storage-update branches in one
    # proof so the direct native case split stays explicit.
    "simpleStorageNativeStoreHitMatchBridge_proved",
    # Projected native dispatcher result wrapper has a short proof body, but
    # the scanner includes the following public runtime-harness doc block.
    "nativeDispatcherExecMatchesIRPositive_of_project_eq_match",
    # --- Misc ---
    # PR #1915 init-prefixed dispatcher bridge. These proofs are generated-code
    # shape peel/reduction endpoints for `initFreeMemoryPointer; buildSwitch`.
    # They keep the concrete init `mstore(0x40, 128)` state transition, selector
    # switch lowering, and SimpleStorage closed-form reductions explicit; splitting
    # further would mainly create one-use wrappers around the same generated
    # dispatcher case analysis.
    "sizeOf_emitYul_runtimeCode_mapping_ge_lowered_cases_length_plus25",
    "lowerStmtsNative_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block",
    "nativeDispatcherExecMatchesIRPositive_of_initFreeMemoryPointer_buildSwitch_selector_miss_noFallback_noReceive_atFuel",
    "nativeDispatcherExecMatchesIRPositive_of_initFreeMemoryPointer_buildSwitch_selector_miss_noFallback_noReceive",
    "nativeDispatcherExecMatchesIRPositive_of_initFreeMemoryPointer_buildSwitch_selector_miss_noFallback_noReceive_withSwitchIds_atFuel",
    "nativeDispatcherExecMatchesIRPositive_of_initFreeMemoryPointer_buildSwitch_selector_miss_noFallback_noReceive_withSwitchIds",
    "simpleStorageNativeRuntimeDispatcherStmts_exists_init_block",
    "simpleStorageNativeContract_dispatcherExec_storeHit_error_via_reduction",
    "simpleStorageNativeContract_dispatcherExec_retrieveHit_error_via_reduction",
    "exec_block_lowerNativeSwitchBlock_revert_default_postInitFreeMemory_hasSelectorState_projectResult_eq",
    "exec_block_lowerNativeSwitchBlock_selector_find_hit_postInitFreeMemory_hasSelectorState_error_projectResult_eq",
    "exec_block_lowerNativeSwitchBlock_selector_find_hit_postInitFreeMemory_hasSelectorState_ok_projectResult_eq_finalMatched",
    "contractDispatcherExecResult_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_peel",
}

# PR #1822 native EVMYulLean generic-dispatcher closure. These regexes cover
# generated-runtime/native-dispatcher simulation families whose proof spans are
# long because they compose selector dispatch, switch lowering, fuel
# normalization, environment validation, and projected storage/result equality.
# Factoring each endpoint further would mostly create single-use wrappers over
# the same generated dispatcher case split.
ALLOWLIST_REGEXES: tuple[re.Pattern[str], ...] = tuple(
    re.compile(pattern)
    for pattern in (
        r"^compile_preserves_native_evmYulLean_",
        r"^nativeDispatcherExecMatchesIRPositive_of_buildSwitch_",
        r"^nativeGenerated(?:SelectorHit|CallDispatcherResult|CallDispatcherMatchesIR)_",
        r"^nativeGeneratedSelectorHit(?:SuccessUserBody)?LoweredArtifacts.*$",
        r"^NativeGenerated(?:SelectorHit|SelectedUserBody).*",
        r"^contractDispatcherExecResult_buildSwitch_noFallback_noReceive_",
        r"^contractDispatcherExecResult_block_lowerNativeSwitchBlock_",
        r"^exec_(?:block_)?lowerNativeSwitchBlock_.*"
        r"(?:generated_prefix|finalMatched_store_fuel)$",
        r"^NativeBlockPreservesWord(?:_revived)?_switchCaseBody_"
        r"(?:payable|nonpayable)_of_user_body$",
        r"^nativeGeneratedSelectorHitBodyPreservesMatched_.*$",
        r"^nativeGeneratedSelectorHit_success_of_user_body_exec_bridge_atFuel_revived.*$",
        r"^nativeResultsMatchOn_execIRFunction_.*_markedPrefix$",
        r"^execIRFunction_(?:zeroParam|oneParam)_.*$",
        r"^projectResult_literalReturnHit_eq$",
        r"^exec_block_(?:store0_calldataload4_stop|simpleStorageLoweredStoreCaseBodyTail2)"
        r"_markedPrefix_halt$",
        r"^lowerRuntimeContractNative_of_compile_ok_supported_exists$",
        r"^lowerStmtsNative(?:WithSwitchIds)?_buildSwitch_noFallback_noReceive_ok_block$",
        r"^sizeOf_(?:buildSwitch_noFallback_noReceive_ge_source_cases_length"
        r"(?:_plus24)?|emitYul_runtimeCode_mapping_ge_lowered_cases_length"
        r"(?:_plus24)?)$",
        r"^supportedStmtList_safe_of_state_"
        r"(?:effect_closed|except_mapping_writes_stmt_safety)$",
        # Thin denote-headed wrapper; the count is inflated by the trailing
        # module comment block (proof body is a single composition term).
        r"^simpleStorage_denote_endToEnd_native_evmYulLean_of_sourceIR$",
    )
)

# Directories containing proof files to scan.
PROOF_DIRS = [
    ROOT / "Compiler" / "Proofs",
    ROOT / "Verity" / "Proofs",
    ROOT / "Verity" / "Core",
    ROOT / "Contracts",
]


def _is_proof_terminator(line: str) -> bool:
    """Return True if *line* starts a new declaration or ends a scope."""
    return bool(_DECL_RE.match(line) or _END_RE.match(line) or _SECTION_RE.match(line))


def _theorem_name_at(lines: list[str], i: int) -> str | None:
    """Return the theorem name declared at line *i*, if any.

    Handles both `theorem name ...` and split headers where the name sits on
    the next line.
    """
    m = THEOREM_RE.match(lines[i])
    if m:
        return m.group("name")
    if _SPLIT_THEOREM_RE.match(lines[i]) and i + 1 < len(lines):
        m = _SPLIT_NAME_RE.match(lines[i + 1])
        if m:
            return m.group("name")
    return None


def measure_proofs(lean_file: Path) -> list[tuple[str, int, int]]:
    """Return (name, start_line_1indexed, length) for every theorem/lemma."""
    text = lean_file.read_text(encoding="utf-8")
    stripped = strip_lean_comments(text)
    lines = stripped.splitlines()

    results: list[tuple[str, int, int]] = []
    current_name: str | None = None
    current_start: int | None = None

    for i, line in enumerate(lines):
        name = _theorem_name_at(lines, i)
        if name is not None:
            # Close previous proof span.
            if current_name is not None and current_start is not None:
                results.append((current_name, current_start + 1, i - current_start))
            current_name = name
            current_start = i
        elif current_name is not None and _is_proof_terminator(line):
            results.append((current_name, current_start + 1, i - current_start))  # type: ignore[arg-type]
            # The terminator might itself be a new theorem via the THEOREM_RE branch
            # above, but since THEOREM_RE didn't match, this is a def/end/etc.
            current_name = None
            current_start = None

    # Handle proof at end of file.
    if current_name is not None and current_start is not None:
        results.append((current_name, current_start + 1, len(lines) - current_start))

    return results


def is_allowlisted(name: str) -> bool:
    return name in ALLOWLIST or any(pattern.match(name) for pattern in ALLOWLIST_REGEXES)


def main() -> None:
    parser = argparse.ArgumentParser(description="Check proof lengths.")
    parser.add_argument(
        "--format",
        choices=["text", "markdown"],
        default="text",
        help="Output format (default: text)",
    )
    args = parser.parse_args()

    all_proofs: list[tuple[Path, str, int, int]] = []  # (file, name, line, length)
    for proof_dir in PROOF_DIRS:
        if not proof_dir.exists():
            continue
        for lean_file in sorted(proof_dir.rglob("*.lean")):
            for name, line, length in measure_proofs(lean_file):
                all_proofs.append((lean_file, name, line, length))

    # Partition into buckets.
    violations: list[tuple[Path, str, int, int]] = []
    warnings: list[tuple[Path, str, int, int]] = []
    allowlisted: list[tuple[Path, str, int, int]] = []

    for file, name, line, length in all_proofs:
        if length > HARD_LIMIT:
            if is_allowlisted(name):
                allowlisted.append((file, name, line, length))
            else:
                violations.append((file, name, line, length))
        elif length > SOFT_LIMIT:
            warnings.append((file, name, line, length))

    total = len(all_proofs)
    under_soft = total - len(warnings) - len(allowlisted) - len(violations)

    if args.format == "markdown":
        _print_markdown(total, under_soft, warnings, allowlisted, violations)
    else:
        _print_text(total, under_soft, warnings, allowlisted, violations)

    if violations:
        sys.exit(1)


def _print_text(
    total: int,
    under_soft: int,
    warnings: list[tuple[Path, str, int, int]],
    allowlisted: list[tuple[Path, str, int, int]],
    violations: list[tuple[Path, str, int, int]],
) -> None:
    print(f"Proof length check: {total} proofs scanned.")
    print(f"  {under_soft} under {SOFT_LIMIT} lines (good)")
    print(f"  {len(warnings)} between {SOFT_LIMIT}-{HARD_LIMIT} lines (acceptable)")
    print(f"  {len(allowlisted)} over {HARD_LIMIT} lines (allowlisted)")

    if violations:
        print(
            f"\nERROR: {len(violations)} proof(s) exceed {HARD_LIMIT} lines "
            f"without an allowlist entry:",
            file=sys.stderr,
        )
        for file, name, line, length in sorted(violations, key=lambda x: -x[3]):
            rel = file.relative_to(ROOT)
            print(
                f"  {rel}:{line}: {name} ({length} lines, limit {HARD_LIMIT})",
                file=sys.stderr,
            )
        print(
            f"\nTo fix: decompose the proof into smaller lemmas, or add the "
            f"theorem name to ALLOWLIST in scripts/check_proof_length.py with "
            f"a justification comment in the PR.",
            file=sys.stderr,
        )
    else:
        print(
            f"\nProof length check passed. "
            f"No new proofs exceed the {HARD_LIMIT}-line hard limit."
        )


def _print_markdown(
    total: int,
    under_soft: int,
    warnings: list[tuple[Path, str, int, int]],
    allowlisted: list[tuple[Path, str, int, int]],
    violations: list[tuple[Path, str, int, int]],
) -> None:
    print("### Proof Length Distribution\n")
    print(f"| Range | Count | Percentage |")
    print(f"| :-- | --: | --: |")
    pct = lambda n: f"{100 * n / total:.0f}%" if total else "0%"
    print(f"| Under {SOFT_LIMIT} lines | {under_soft} | {pct(under_soft)} |")
    print(f"| {SOFT_LIMIT}-{HARD_LIMIT} lines | {len(warnings)} | {pct(len(warnings))} |")
    print(f"| Over {HARD_LIMIT} lines (allowlisted) | {len(allowlisted)} | {pct(len(allowlisted))} |")
    if violations:
        print(f"| **Over {HARD_LIMIT} lines (NEW, failing)** | **{len(violations)}** | **{pct(len(violations))}** |")
    print(f"| **Total** | **{total}** | 100% |")


if __name__ == "__main__":
    main()
