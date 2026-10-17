#!/usr/bin/env python3
"""Generate/check deterministic EVMYulLean fork-audit artifact.

Records the exact divergence between ``lfglabs-dev/EVMYulLean`` (the fork
Verity depends on) and its upstream ``NethermindEth/EVMYulLean``. The
artifact answers the audit question: "What code in Verity's pinned
EVMYulLean dependency is NOT identical to the upstream reference?"

The fork audit is a required trust-surface document under Issue #1722:
every fork-side divergence must be minimal and documented here. Semantic
changes require an explicit, immutable, evidence-bound scope expansion so that downstream auditors can review exactly what
Verity is trusting beyond upstream EVMYulLean's Ethereum conformance
test suite.

This script does NOT fetch from GitHub at build time (CI may run
offline). Instead, the audit contents are hand-maintained as a
constant below, and this script simply serializes them into a
deterministic JSON artifact and checks that the on-disk artifact
matches. The on-disk SHA in ``lake-manifest.json`` is cross-checked
against the ``pinned_commit`` field to catch silent drift: if Verity
bumps the pinned EVMYulLean commit, this script fails, forcing the
developer to regenerate the audit manifest.

Usage:
    python3 scripts/generate_evmyullean_fork_audit.py
    python3 scripts/generate_evmyullean_fork_audit.py --check
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

from property_utils import ROOT

LAKE_MANIFEST = ROOT / "lake-manifest.json"
PACKAGE_MANIFESTS = sorted((ROOT / "packages").glob("*/lake-manifest.json"))
LAKE_MANIFESTS = [LAKE_MANIFEST, *PACKAGE_MANIFESTS]
DEFAULT_OUTPUT = ROOT / "artifacts" / "evmyullean_fork_audit.json"

# Hand-maintained record of the fork's divergence from upstream.
# When the pinned commit changes, update this dict and re-run the
# generator. The script's check mode will refuse to pass if the pinned
# commit in lake-manifest.json disagrees with ``pinned_commit`` here.
FORK_AUDIT = {
    "schema_version": 2,
    "fork_url": "https://github.com/lfglabs-dev/EVMYulLean",
    "upstream_url": "https://github.com/NethermindEth/EVMYulLean",
    "pinned_commit": "4cf4c5d0f286e8efc3d9e972ce3616bfe83a0624",
    "upstream_base": "047f63070309f436b66c61e276ab3b6d1169265a",
    "fork_ahead_by": 25,
    "fork_behind_by": 0,
    "divergence_summary": (
        "The 25 fork commits include 18 previously audited visibility/toolchain/merge "
        "commits, native proof APIs and memory lemmas, a total jump-destination scanner, "
        "and an Osaka creation correction. The scanner implementation and shared "
        "CREATE/CREATE2 collision/storage transitions are explicitly audited semantic "
        "changes; upstream conformance does not transfer to those changes by ancestry. "
        "The creation correction has exact-head native, mutation/replay and independent "
        "Foundry v1.5.0 Osaka evidence. This is component evidence, not full conformance."
    ),
    "commits": [
        {
            "sha": "ed9215e9ba8e3fa73128f3b67131793a01db332f",
            "title": "feat: expose powAux for downstream formal verification",
            "file": "EvmYul/UInt256.lean",
            "category": "visibility",
            "semantic_change": False,
            "rationale": (
                "Remove `private` modifier from `EvmYul.UInt256.powAux` "
                "(binary-exponentiation accumulator for `UInt256.exp`). "
                "In Lean 4.22.0 private declarations cannot be unfolded "
                "across module boundaries (`simp only`, `unfold`, and "
                "`delta` all fail) because their equational theorems are "
                "also private (Lean 4 PR #8519). Exposing the function "
                "unblocks Verity's inductive bridge proof for the `exp` "
                "builtin in `EvmYulLeanBridgeLemmas.lean`."
            ),
            "diff_summary": (
                "1 file changed, 2 insertions(+), 1 deletion(-): strip "
                "`private` from one `def`, add a doc comment. No behavior "
                "change."
            ),
            "trust_impact": (
                "Zero. Visibility is a module-system concept with no "
                "runtime or logical effect on term evaluation."
            ),
        },
        {
            "sha": "7b54b8f38bb68ee930d00d39c1b11dd60fb123c8",
            "title": "fix: replace deprecated nativeLibDir with staticLibDir",
            "file": "lakefile.lean",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": (
                "`Lake.Package.nativeLibDir` was deprecated in Lean "
                "4.22.0 in favor of `staticLibDir`. The fork pins to "
                "Lean 4.22.0 to match Verity's toolchain, so the fix "
                "silences a build-time warning that Verity's build "
                "would otherwise promote to an error under its "
                "`-Dwarnings.toErrors=true` CI policy."
            ),
            "diff_summary": (
                "1 file changed, 1 insertion(+), 1 deletion(-): rename "
                "one field reference in the FFI extern-lib build step. "
                "No behavior change."
            ),
            "trust_impact": (
                "Zero. Lake build metadata only; compiled output is "
                "byte-identical up to path naming."
            ),
        },
        {
            "sha": "b353c7583ea36e49dbbffd57f5b25f4d01226e15",
            "title": "ffi: expose zero byte array body",
            "file": "EvmYul/FFI/ffi.lean",
            "category": "visibility",
            "semantic_change": False,
            "rationale": (
                "Replace the opaque `ByteArray.zeroes` extern declaration "
                "with a kernel-visible Lean body using `Array.replicate`. "
                "The attached extern name remains the same, preserving the "
                "runtime FFI target while allowing downstream proofs to unfold "
                "the size and byte contents of zero-filled padding."
            ),
            "diff_summary": (
                "1 file changed, 1 insertion(+), 1 deletion(-): replace one "
                "opaque declaration with an equivalent Lean definition. No "
                "behavior change."
            ),
            "trust_impact": (
                "Low. This makes the existing zero-fill behavior visible to "
                "Lean's kernel for proofs; it does not alter Yul/EVM execution "
                "semantics or the extern symbol used by compiled code."
            ),
        },
        {
            "sha": "7785a9bba344db917e42b7f1033ee8346197bb40",
            "title": "Expose checkpoint state projections",
            "file": "EvmYul/Yul/StateOps.lean",
            "category": "visibility",
            "semantic_change": False,
            "rationale": (
                "Expose the saved shared-state and varstore inside Yul "
                "checkpoint states through existing projection helpers. "
                "Downstream proofs need these projections after revived "
                "control-flow paths; the change reads data already stored in "
                "the checkpoint and does not alter execution, checkpoint "
                "construction, or revival behavior."
            ),
            "diff_summary": (
                "1 file changed, 20 insertions(+), 5 deletions(-): refine "
                "`toSharedState`, `executionEnv`, `toMachineState`, `toState`, "
                "and `store` to project from checkpoint states instead of "
                "falling back to `default`. No execution rule changes."
            ),
            "trust_impact": (
                "Low. This changes proof-facing state query behavior on "
                "checkpoint values only; it does not change Yul/EVM execution "
                "semantics or runtime state transitions."
            ),
        },
        {
            "sha": "38d53df8b4488d5322894619ea8385fcbb2e6f5d",
            "title": "chore: upgrade Lean toolchain to v4.24.0",
            "file": "lean-toolchain, lakefile.lean, lake-manifest.json, Conform/Wheels.lean, EvmYul/Yul/YulNotation.lean, EvmYul/EVM/Semantics.lean",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": (
                "Move the fork and its Mathlib dependency from Lean 4.22.0 "
                "to Lean 4.24.0 so downstream Verity projects can use the "
                "same toolchain as lean-lsp-mcp 0.28.0. Adapt JSON object "
                "iteration to Std.TreeMap.Raw, update the custom Yul parser "
                "to current parser-context APIs and non-conflicting syntax "
                "category names, and make a UInt256 zero literal explicit."
            ),
            "diff_summary": (
                "6 files changed, 82 insertions(+), 60 deletions(-): update "
                "toolchain metadata and mechanical compatibility points for "
                "Lean 4.24.0. The EvmYul default target still builds all 1059 "
                "jobs successfully."
            ),
            "trust_impact": (
                "Low. The migration preserves the existing JSON conversion, "
                "Yul syntax and execution behavior while adopting renamed or "
                "stricter Lean 4.24 APIs. No EVM/Yul transition rule changes."
            ),
        },
        {
            "sha": "fc8e4788cef3af6d41a2ab5022c2c68fc107e25d",
            "title": "Merge pull request #2 from lfglabs-dev/codex/lean424-checkpoint",
            "file": "merge commit",
            "category": "merge",
            "semantic_change": False,
            "rationale": "Merge commit combining the audited Lean 4.24 and checkpoint-projection changes.",
            "diff_summary": "Merge-only history node; content is enumerated by its parent commits.",
            "trust_impact": "Zero beyond the individually audited parent commits.",
        },
        {
            "sha": "2400ef4ec3db40da832a1d0394f1726e299ed632",
            "title": "Merge pull request #1 from lfglabs-dev/fix/checkpoint-state-queries",
            "file": "merge commit",
            "category": "merge",
            "semantic_change": False,
            "rationale": "Merge commit landing the audited checkpoint projection and Lean 4.24 changes.",
            "diff_summary": "Merge-only history node; content is enumerated by its parent commits.",
            "trust_impact": "Zero beyond the individually audited parent commits.",
        },
        {
            "sha": "2850ea1b2785bffb9ae44b36c1e7516d02fe6826",
            "title": "chore: upgrade to Lean 4.31.0",
            "file": "lean-toolchain, lakefile.lean, lake-manifest.json",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": "Update Lean, Mathlib, and Lake metadata from 4.24 to 4.31.",
            "diff_summary": "3 files changed, 17 insertions(+), 16 deletions(-).",
            "trust_impact": "Low; build metadata only.",
        },
        {
            "sha": "8401b6e668fc48c145c14acb4e8c52fca8c80d74",
            "title": "fix: adapt bitwise xor to Lean 4.31",
            "file": "EvmYul/UInt256.lean, lakefile.lean",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": "Adapt xor notation and the Lake version declaration to Lean 4.31 APIs.",
            "diff_summary": "2 files changed, 2 insertions(+), 2 deletions(-).",
            "trust_impact": "Low; type-directed compatibility changes preserve xor behavior.",
        },
        {
            "sha": "4060647fc55121d2575e64fa5dc37af62117e08f",
            "title": "fix: convert string slice before lowercasing",
            "file": "EvmYul/Wheels.lean",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": "Materialize the Lean 4.31 string slice before applying lowercase conversion.",
            "diff_summary": "1 file changed, 1 insertion(+), 1 deletion(-).",
            "trust_impact": "Low; preserves the parsed lowercase string.",
        },
        {
            "sha": "959420a4b00e07939aa2a2a6d5f430aa94e35438",
            "title": "fix: preserve homogeneous xor instance",
            "file": "EvmYul/UInt256.lean",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": "Make the UInt256 xor instance result type explicit under Lean 4.31.",
            "diff_summary": "1 file changed, 1 insertion(+), 1 deletion(-).",
            "trust_impact": "Low; instance elaboration only.",
        },
        {
            "sha": "d4afe3be9b9160a6162f084f3b187dc3c7282b66",
            "title": "fix: migrate RBMap usage to Std TreeMap",
            "file": "Conform/*.lean, EvmYul/**/*.lean",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": "Replace removed RBMap construction and traversal APIs with Std.TreeMap equivalents.",
            "diff_summary": "13 files changed, 25 insertions(+), 39 deletions(-).",
            "trust_impact": "Low; collection representation migration preserves keys and values.",
        },
        {
            "sha": "26ed6f948fd2d555325b4c4bfb7001237b752063",
            "title": "fix: adapt maps and slices for Lean 4.31",
            "file": "Conform/Wheels.lean, EvmYul/Maps/StorageMap.lean, EvmYul/Yul/YulNotation.lean",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": "Adapt remaining map and slice call sites to their Lean 4.31 types.",
            "diff_summary": "3 files changed, 2 insertions(+), 6 deletions(-).",
            "trust_impact": "Low; mechanical API compatibility.",
        },
        {
            "sha": "ab541b3febf7f3c75dbee43ff98f594aa7fe5cfc",
            "title": "fix: update TreeMap APIs for Lean 4.31",
            "file": "Conform/*.lean, EvmYul/**/*.lean",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": "Update TreeMap lookup, fold, and conversion calls to Lean 4.31 signatures.",
            "diff_summary": "13 files changed, 69 insertions(+), 65 deletions(-).",
            "trust_impact": "Low; preserves collection operations while changing API spelling.",
        },
        {
            "sha": "76653da7c02d2359e6058872702b99e37fd377db",
            "title": "fix: complete Lean 4.31 collection migration",
            "file": "EvmYul/EVM/Semantics.lean",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": "Complete the remaining collection conversions in EVM semantics.",
            "diff_summary": "1 file changed, 3 insertions(+), 3 deletions(-).",
            "trust_impact": "Low; representation-compatible collection access.",
        },
        {
            "sha": "7a33dd5f20d1fcff7fe960f8ed14627d81277c97",
            "title": "fix: return arrays from conformance partition",
            "file": "Conform/Main.lean",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": "Convert the partition result to the array type required by Lean 4.31.",
            "diff_summary": "1 file changed, 1 insertion(+), 1 deletion(-).",
            "trust_impact": "Low; preserves partition membership and ordering.",
        },
        {
            "sha": "01f260fe7cbffce47b7babe7d55e4e4f41bdec7a",
            "title": "fix: use product keys with Lean 4.31 JSON objects",
            "file": "Conform/Main.lean, Conform/TestParser.lean",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": "Project JSON object key/value products using the Lean 4.31 object API.",
            "diff_summary": "2 files changed, 2 insertions(+), 2 deletions(-).",
            "trust_impact": "Low; preserves the same JSON keys and values.",
        },
        {
            "sha": "f7e4ee0dc8f8d5265ce822a937ab5be771f182e9",
            "title": "Merge pull request #3 from lfglabs-dev/codex/lean-4.31.0",
            "file": "merge commit",
            "category": "merge",
            "semantic_change": False,
            "rationale": "Merge commit landing the ten individually audited Lean 4.31 compatibility commits.",
            "diff_summary": "Merge-only history node; content is enumerated by its parent commits.",
            "trust_impact": "Zero beyond the individually audited parent commits.",
        },
        {
            "sha": "0ff72b2db35302305fccb1d4f42b480434b77bfe",
            "title": "feat: make D_J total via structural recursion (#4)",
            "file": "EvmYul/EVM/Semantics.lean",
            "category": "semantic-change",
            "semantic_change": True,
            "rationale": "Replace the kernel-opaque partial UInt256 scanner with size-bounded structural Nat recursion. Every step advances at least one byte and PUSH immediate bytes are skipped. The implementation changes; no universal equivalence to the old partial scanner is claimed.",
            "diff_summary": "1 file changed, 14 insertions, 5 deletions.",
            "trust_impact": "Explicit scanner scope: kernel evaluation is now possible. The included PUSH1/JUMPDEST example is a regression, not proof of full upstream conformance."
        },
        {
            "sha": "9d8eda705793eba448fd67850168af515e7fdc7a",
            "title": "feat(evm): add proof-facing step runs (#5)",
            "file": "EvmYul.lean, EvmYul/EVM/Proof/Execution.lean",
            "category": "lemma-addition",
            "semantic_change": False,
            "rationale": "Expose actual step/run relations and X decomposition. Mirrored exceptional/gas/halting definitions are checked by proofs unfolding actual X.",
            "diff_summary": "2 files changed, 493 insertions.",
            "trust_impact": "Kernel-checked API over existing execution; no assumed transition correspondence."
        },
        {
            "sha": "d164b61b995f4f553e975db9cfe3640d0aeefafa",
            "title": "feat(evm): F4d runUntil, basic-block composition, and block tactics (#8)",
            "file": "EvmYul.lean, EvmYul/EVM/Proof/Block.lean",
            "category": "lemma-addition",
            "semantic_change": False,
            "rationale": "Add validated bounded block execution, native precheck state projection and compositional symbolic tactics.",
            "diff_summary": "2 files changed, 735 insertions.",
            "trust_impact": "Adds derived proof/driver APIs; actual EVM.X remains the runtime authority."
        },
        {
            "sha": "b62586650b4f96cc6da25f36574aaa8f329a6420",
            "title": "feat(evm): memory read-over-write lemmas for MSTORE/MSTORE8/RETURN (#9)",
            "file": "EvmYul.lean, EvmYul/EVM/Proof/Memory.lean, EvmYul/EVM/Proof/MemoryStep.lean, EvmYul/UInt256.lean",
            "category": "lemma-addition",
            "semantic_change": False,
            "rationale": "Prove actual memory opcode frames and returned-byte equations; expose fixed-width word encodings with proofs connecting existing byte encoding.",
            "diff_summary": "4 files changed, 1074 insertions.",
            "trust_impact": "Kernel proofs and helper encodings; existing memory execution definitions are unchanged."
        },
        {
            "sha": "a4473c2c1831d99ac3e1c5be7c9ce8e07da04266",
            "title": "fix: align CREATE2 target storage with Osaka execution",
            "file": "EvmYul/EVM/Semantics.lean, Conform/Create2OsakaChecks.lean, scripts/check_create2_osaka_mutations.py, scripts/check_create2_osaka_reference.py, docs/CREATE2_OSAKA.md, lakefile.lean, .github/workflows/lean_action_ci.yml",
            "category": "semantic-change",
            "semantic_change": True,
            "rationale": "Remove unconditional proposed EIP-7610 storage-only collision and initialize fresh persistent storage in shared Lambda. Keep nonce/code collision, target balance and collision snapshot. Real Osaka accepts storage-only targets and clears old storage.",
            "diff_summary": "7 files changed, 318 insertions, 7 deletions.",
            "trust_impact": "Changes shared CREATE/CREATE2 behavior. Four independent real-EVM cases, strict native runtime and four compiled semantic mutants/replays at the audited tip are component evidence. No universal fork selector or whole-transaction equivalence claim."
        },
        {
            "sha": "b3d76d0a1a0c0242138fc81af8e65156fdae25a3",
            "title": "test: reject native initialization panics in CREATE2 checks",
            "file": "scripts/check_create2_osaka_runtime.py, requirements-native-tests.txt, docs/CREATE2_OSAKA.md, .github/workflows/lean_action_ci.yml",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": "Pin Python startup dependencies and require exact native success output with no stderr. Exit0 with initialization PANIC is rejected.",
            "diff_summary": "4 files changed, 54 insertions, 2 deletions.",
            "trust_impact": "Strengthens runtime evidence; no execution-rule changes."
        },
        {
            "sha": "4cf4c5d0f286e8efc3d9e972ce3616bfe83a0624",
            "title": "Merge upstream native proof APIs into Osaka creation fix",
            "file": "merge commit",
            "category": "merge",
            "semantic_change": False,
            "rationale": "Merge current fork native proof APIs into the creation fix without dropping either parent.",
            "diff_summary": "Merge-only history node; changes enumerated in parent records.",
            "trust_impact": "No additional content beyond reviewed parents; both semantic scope expansions still apply."
        },
    ],
    "audit_methodology": [
        "1. Clone lfglabs-dev/EVMYulLean at pinned commit into a local worktree.",
        "2. Add NethermindEth/EVMYulLean as `upstream` remote and fetch.",
        "3. Compute `git merge-base upstream/main origin/main` to find the divergence point.",
        "4. For each commit in `upstream/main..origin/main`, record SHA, title, touched files, and categorize as {visibility, toolchain, lemma-addition, builtin-addition, semantic-change, merge}.",
        "5. Reject semantic changes except the immutable scanner and Osaka creation scope expansions documented in docs/EVMYULLEAN_FORK_SCOPE.md; require evidence identity and explicit limits.",
        "6. Commit this artifact alongside Verity's lake-manifest.json pin bump.",
    ],
    "reproduction": {
        "script": "scripts/generate_evmyullean_fork_audit.py",
        "steps": [
            "git clone https://github.com/lfglabs-dev/EVMYulLean",
            "cd EVMYulLean",
            "git remote add upstream https://github.com/NethermindEth/EVMYulLean.git",
            "git fetch upstream",
            "git log --oneline upstream/main..origin/main",
            "git diff --stat upstream/main..origin/main",
        ],
    },
    "semantic_scope": {
        "document": "docs/EVMYULLEAN_FORK_SCOPE.md",
        "approved_commits": [
            "0ff72b2db35302305fccb1d4f42b480434b77bfe",
            "a4473c2c1831d99ac3e1c5be7c9ce8e07da04266",
        ],
        "evidence": "artifacts/evmyullean_osaka_creation_reference.json",
        "evidence_sha256": "92e6dd70ef72da3c67c5e8656c23fab506466f716a92b6f197cb7ca9d768a25a",
        "upstream_conformance_transfers": False,
    },
    "trust_boundary": (
        "Upstream base 047f63070309f436b66c61e276ab3b6d1169265a plus all 25 "
        "enumerated fork commits. Two implementation/transition changes are separately "
        "scoped. Historical upstream conformance is not certification of the changed "
        "scanner or creation semantics. Exact-head component runtime/mutation/reference "
        "evidence covers four Osaka creation cases; whole-program gas, rollback, "
        "constructor fuel/output and canonical/native account correspondence still "
        "require their own proofs and differential campaigns."
    ),
}

ALLOWED_CATEGORIES = frozenset({
    "visibility",
    "toolchain",
    "lemma-addition",
    "builtin-addition",
    "semantic-change",
    "merge",
})


APPROVED_SEMANTIC_CHANGES = frozenset({
    "0ff72b2db35302305fccb1d4f42b480434b77bfe",
    "a4473c2c1831d99ac3e1c5be7c9ce8e07da04266",
})


def _validate_semantic_scope() -> None:
    scope = FORK_AUDIT.get("semantic_scope", {})
    if (set(scope.get("approved_commits", [])) != APPROVED_SEMANTIC_CHANGES
            or len(scope.get("approved_commits", [])) != len(APPROVED_SEMANTIC_CHANGES)
            or scope.get("upstream_conformance_transfers") is not False):
        raise RuntimeError("semantic scope must name exactly the approved changes and deny conformance transfer")
    listed = {c["sha"] for c in FORK_AUDIT["commits"]}
    if not APPROVED_SEMANTIC_CHANGES <= listed:
        raise RuntimeError("semantic scope contains a commit missing from the audit")
    if scope.get("document") != "docs/EVMYULLEAN_FORK_SCOPE.md" or not (ROOT / scope["document"]).is_file():
        raise RuntimeError("semantic scope document is missing")
    if scope.get("evidence") != "artifacts/evmyullean_osaka_creation_reference.json":
        raise RuntimeError("semantic evidence path is not the audited artifact")
    path = ROOT / scope["evidence"]
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != scope.get("evidence_sha256"):
        raise RuntimeError("semantic evidence identity mismatch")
    evidence = json.loads(path.read_text(encoding="utf-8"))
    tip = FORK_AUDIT["pinned_commit"]
    validation = evidence.get("validation", {})
    expected_checks = {"build", "runtime", "mutations", "real-reference", "diff"}
    checks = validation.get("checks", [])
    if (evidence.get("native_commit") != tip or validation.get("head") != tip
            or validation.get("exit") != 0 or validation.get("sourceIdentityUnchanged") is not True
            or len(checks) != len(expected_checks) or {c.get("name") for c in checks} != expected_checks
            or any(c.get("exit") != 0 for c in checks)):
        raise RuntimeError("semantic evidence lacks complete exact-tip validation")
    reference = evidence.get("reference", {})
    mutations = evidence.get("mutations", {})
    runtime = evidence.get("runtime", {})
    cases = reference.get("rows", [])
    if (reference.get("exit") != 0 or len(cases) != 4
            or {c.get("name") for c in cases} != {"storage-only", "balance-only", "nonce-collision", "code-collision"}):
        raise RuntimeError("semantic reference must contain all four independent EVM cases")
    mutants = mutations.get("rows", [])
    if (mutations.get("exit") != 0 or len(mutants) != 4
            or {m.get("name") for m in mutants} != {
                "reinstate-storage-collision", "omit-storage-reset", "omit-nonce-collision", "omit-code-collision"}
            or any(m.get("exit") != 1 or len(m.get("detected", [])) != 1
                   or m.get("detected") != m.get("replay") for m in mutants)):
        raise RuntimeError("semantic mutations require four runtime failures and identical replay")
    if (runtime.get("exit") != 0 or runtime.get("output") != [
            "Osaka CREATE2 storage reset and nonce/code collision checks passed:4"]):
        raise RuntimeError("semantic runtime must have the strict native success marker")
    identities = [reference.get("identity", {}), mutations.get("identity", {}), runtime.get("identity", {})]
    for source in ("EvmYul/EVM/Semantics.lean", "Conform/Create2OsakaChecks.lean"):
        hashes = [i.get(source) for i in identities]
        if any(not isinstance(h, str) or not re.fullmatch(r"[0-9a-f]{64}", h) for h in hashes) or len(set(hashes)) != 1:
            raise RuntimeError("semantic evidence uses inconsistent native source identities")


def _read_evmyul_package(manifest_path: Path) -> dict[str, object]:
    """Extract the ``evmyul`` package entry from a Lake manifest."""
    with manifest_path.open("r", encoding="utf-8") as f:
        manifest = json.load(f)
    for pkg in manifest.get("packages", []):
        if pkg.get("name") == "evmyul":
            return pkg
    raise RuntimeError(f"evmyul package not found in {manifest_path.relative_to(ROOT)}")


def _validate_audit() -> None:
    """Validate internal invariants of the audit record."""
    if FORK_AUDIT["fork_ahead_by"] != len(FORK_AUDIT["commits"]):
        raise RuntimeError(
            f"fork_ahead_by ({FORK_AUDIT['fork_ahead_by']}) does not match "
            f"number of enumerated commits ({len(FORK_AUDIT['commits'])})"
        )
    if FORK_AUDIT["fork_behind_by"] != 0:
        raise RuntimeError(
            "fork_behind_by must be 0 to retain the recorded upstream ancestry"
        )
    for commit in FORK_AUDIT["commits"]:
        if commit.get("category") not in ALLOWED_CATEGORIES:
            raise RuntimeError(
                f"commit {commit['sha'][:10]} has unsupported category "
                f"{commit.get('category')!r}"
            )
        approved = commit["sha"] in APPROVED_SEMANTIC_CHANGES
        if commit.get("semantic_change") is not approved:
            raise RuntimeError(
                f"commit {commit['sha'][:10]} semantic_change must be {approved}; "
                "unscoped semantic changes require a new explicit audit scope"
            )
        if (commit["category"] == "semantic-change") is not approved:
            raise RuntimeError(f"commit {commit['sha'][:10]} semantic category disagrees with scope")
        if not re.match(r"^[0-9a-f]{40}$", commit["sha"]):
            raise RuntimeError(
                f"invalid SHA format: {commit['sha']}"
            )
    pinned = FORK_AUDIT["pinned_commit"]
    expected_tip = (
        FORK_AUDIT["commits"][-1]["sha"]
        if FORK_AUDIT["commits"]
        else FORK_AUDIT["upstream_base"]
    )
    if pinned != expected_tip:
        raise RuntimeError(
            f"pinned_commit {pinned} must match the audited fork tip "
            f"{expected_tip}"
        )
    _validate_semantic_scope()


def _cross_check_manifest_pin() -> None:
    """Verify every tracked Lake manifest pins the audited fork commit."""
    expected_url = FORK_AUDIT["fork_url"] + ".git"
    for manifest_path in LAKE_MANIFESTS:
        pkg = _read_evmyul_package(manifest_path)
        pinned = pkg.get("rev", "")
        input_rev = pkg.get("inputRev", "")
        label = str(manifest_path.relative_to(ROOT))
        if pinned != FORK_AUDIT["pinned_commit"]:
            raise RuntimeError(
                f"{label} pins evmyul at {pinned} but the fork "
                f"audit records pinned_commit={FORK_AUDIT['pinned_commit']}. "
                f"The audit must be regenerated whenever the pin moves."
            )
        if input_rev != FORK_AUDIT["pinned_commit"]:
            raise RuntimeError(
                f"{label} records evmyul inputRev={input_rev} but the fork "
                f"audit records pinned_commit={FORK_AUDIT['pinned_commit']}."
            )
        if pkg.get("url") != expected_url:
            raise RuntimeError(
                f"{label} points evmyul at {pkg.get('url')} "
                f"but audit records fork_url={expected_url}"
            )


def _serialize() -> str:
    """Render the audit as stable, sorted JSON."""
    return json.dumps(FORK_AUDIT, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="Verify the on-disk artifact matches what would be generated.",
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Output path for the artifact.",
    )
    args = parser.parse_args()

    _validate_audit()
    _cross_check_manifest_pin()
    payload = _serialize()

    if args.check:
        if not args.output.exists():
            print(
                f"fork audit artifact missing: {args.output}",
                file=sys.stderr,
            )
            return 1
        on_disk = args.output.read_text(encoding="utf-8")
        if on_disk != payload:
            print(
                f"fork audit artifact drift: regenerate with\n"
                f"  python3 {Path(__file__).relative_to(ROOT)}",
                file=sys.stderr,
            )
            return 1
        return 0

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(payload, encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
