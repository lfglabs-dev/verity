# Scripts Consolidation Inventory

Inventory of all `check_*.py` (53) and `generate_*.py` (10) scripts — 63 total.
Clustered into 9 families for the schema-driven consolidation effort.

## Cluster Summary

| Cluster | Count | Description |
|---------|------:|-------------|
| [doc-sync](#doc-sync-11) | 11 | Validate documentation text against artifacts or source |
| [compiler-boundary](#compiler-boundary-7) | 7 | Enforce compiler/import dependency walls |
| [package-imports](#package-imports-4) | 4 | Lake package structural integrity |
| [storage-layout](#storage-layout-2) | 2 | Slot layout consistency across EDSL/Spec/Compiler |
| [axiom-audit](#axiom-audit-6) | 6 | Axiom registry, proof hygiene, trust surfaces |
| [coverage](#coverage-5) | 5 | Property-test manifest coverage |
| [selector-gas](#selector-gas-7) | 7 | Selector hashing and gas model integrity |
| [workflow-ci](#workflow-ci-11) | 11 | CI/workflow configuration and metadata validation |
| [artifact-generator](#artifact-generator-10) | 10 | `generate_*.py` — produce deterministic JSON artifacts |
| **Total** | **63** | |

---

## doc-sync (11)

Scripts that verify that human-readable documentation text is consistent with
machine-readable artifacts or Lean source files.

| Filename | Purpose | Source-of-Truth Read | Emits / Asserts |
|----------|---------|----------------------|-----------------|
| `check_axiomatized_primitive_boundary_sync.py` | Keep keccak256 axiom boundary docs aligned with the interpreter feature matrix | `artifacts/interpreter_feature_matrix.json` | Snippet presence in `docs-site/content/{edsl-api-reference,compiler,guides/solidity-to-verity}.mdx` |
| `check_bridge_coverage_sync.py` | Ensure bridge-coverage docs stay in sync with the proven builtin bridge set | `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean` | Snippet presence in `TRUST_ASSUMPTIONS.md`, `AXIOMS.md`, `docs/ARITHMETIC_PROFILE.md`, `docs/INTERPRETER_FEATURE_MATRIX.md`, `Compiler/Proofs/EndToEnd.lean` |
| `check_builtin_bridge_matrix_sync.py` | Validate builtin-bridge documentation against the interpreter feature matrix artifact | `artifacts/interpreter_feature_matrix.json`, `artifacts/evmyullean_native_lowering_report.json` | Snippet/count checks in `docs/INTERPRETER_FEATURE_MATRIX.md` |
| `check_interpreter_feature_boundary_catalog_sync.py` | Keep interpreter proof-boundary category notes aligned with feature matrix | `artifacts/interpreter_feature_matrix.json` | Snippet presence in `docs/INTERPRETER_FEATURE_MATRIX.md` |
| `check_interpreter_feature_summary_sync.py` | Keep interpreter feature summary table aligned with machine-readable matrix | `artifacts/interpreter_feature_matrix.json` | Count/snippet checks in `docs/INTERPRETER_FEATURE_MATRIX.md` |
| `check_layer2_boundary_catalog_sync.py` | Validate Layer 2 docs against the boundary catalog artifact | `artifacts/layer2_boundary_catalog.json` | Snippet presence in `docs/ROADMAP.md`, `docs/VERIFICATION_STATUS.md`, `docs/COMPILER_PROOFS_README.md` |
| `check_layer2_boundary_sync.py` | Keep Layer 2 proof-boundary claims aligned across all doc surfaces | Multiple docs (`AXIOMS.md`, `README.md`, `docs/ROADMAP.md`, etc.) | Cross-doc consistency assertions |
| `check_linear_memory_boundary_sync.py` | Keep linear-memory boundary docs aligned with interpreter feature matrix | `artifacts/interpreter_feature_matrix.json` | Snippet presence in `docs-site/content/{edsl-api-reference,compiler,guides/solidity-to-verity}.mdx` |
| `check_low_level_call_boundary_sync.py` | Keep low-level call docs aligned with interpreter feature matrix | `artifacts/interpreter_feature_matrix.json` | Snippet presence in `docs-site/content/{edsl-api-reference,compiler,guides/solidity-to-verity}.mdx` |
| `check_struct_mapping_surface_sync.py` | Keep struct-mapping storage docs aligned with the compiler surface | `Compiler/CompilationModel/Types.lean` | Snippet presence in `docs/ROADMAP.md`, `docs-site/content/{compiler.mdx,guides/add-contract.mdx}` |
| `check_verification_status_doc.py` | Validate `docs/VERIFICATION_STATUS.md` against the verification status artifact | `artifacts/verification_status.json` | Regex-extracted counts and percentages in `docs/VERIFICATION_STATUS.md` |

---

## compiler-boundary (7)

Scripts that enforce architectural separation between Compiler, Verity, and Contracts
modules, and the EVMYulLean capability boundary.

| Filename | Purpose | Source-of-Truth Read | Emits / Asserts |
|----------|---------|----------------------|-----------------|
| `check_builtin_list_sync.py` | Ensure `Linker.yulBuiltins` and `CompilationModel.interopBuiltinCallNames` stay in sync | `Compiler/Linker.lean`, `Compiler/CompilationModel.lean` | Opcode-universe agreement with documented exceptions |
| `check_compilationmodel_split.py` | Guard the `CompilationModel` facade split against size regressions | `Compiler/CompilationModel.lean`, `Compiler/CompilationModel/` | Facade line count ≤ 200 and correct imports |
| `check_compiler_boundaries.py` | Dispatcher — runs all compiler boundary sub-checks | Orchestrates 6 sub-scripts | Aggregated exit code |
| `check_compiler_contract_imports.py` | Ensure Compiler modules do not depend on concrete Contracts modules | `Compiler/**/*.lean` (recursive scan) | No forbidden `Contracts.*` imports |
| `check_evmyullean_capability_boundary.py` | Enforce EVMYulLean capability boundary for native Yul builtins | `evmyullean_capability.py`, `BUILTINS_FILE` | Native dispatch stays within supported builtin surface |
| `check_layer_import_boundaries.py` | Guard high-level Lean import boundaries between macro/model/proof layers | `Verity/Macro/`, `Compiler/CompilationModel/`, `Compiler/Proofs/{IRGeneration,YulGeneration}/` | No forbidden cross-layer imports |
| `check_mapping_slot_boundary.py` | Ensure proof interpreters depend on the `MappingSlot` abstraction, not raw keccak | `Compiler/Proofs/MappingSlot.lean`, `Compiler/Proofs/IRGeneration/IRInterpreter.lean` | Proof backend stays on keccak-faithful model |

---

## package-imports (4)

Scripts that validate the multi-package Lake structure introduced by the
verity-edsl / verity-compiler / verity-examples split.

| Filename | Purpose | Source-of-Truth Read | Emits / Asserts |
|----------|---------|----------------------|-----------------|
| `check_package_glob_surfaces.py` | Ensure split-package lakefiles only export their intended module surfaces | `packages/verity-{edsl,compiler,examples}/lakefile.lean` | Glob patterns match expected module surfaces |
| `check_package_import_boundaries.py` | Ensure split Lake packages keep their intended import boundaries | `packages/verity-{edsl,compiler}/lakefile.lean` | No cross-package forbidden imports |
| `check_split_compiler_test_artifacts.py` | Ensure the compiler package exports every standalone compiler test module | `packages/verity-compiler/lakefile.lean`, `Compiler/` | All test modules present in package exports |
| `check_split_package_builds.py` | Build each split Lake package independently to guard decoupling | `packages/verity-{edsl,compiler,examples}/` | Each package builds in isolation (invokes `lake build`) |

---

## storage-layout (2)

Scripts verifying EVM storage slot assignments are consistent across the EDSL
definition, spec, and Compiler layers.

| Filename | Purpose | Source-of-Truth Read | Emits / Asserts |
|----------|---------|----------------------|-----------------|
| `check_contract_structure.py` | Validate that all contracts have the expected file structure | `Contracts/*/` directories | Spec, Invariants, and proof modules exist for each contract |
| `check_storage_layout.py` | Validate storage layout consistency across EDSL, Spec, and Compiler | `Contracts/*/{*.lean,Spec.lean}`, `Compiler/Specs.lean` | No intra-contract slot collisions; cross-layer consistency |

---

## axiom-audit (6)

Scripts that audit the trust surface: declared Lean axioms, proof hygiene,
and non-axiom trust mechanisms (`native_decide`, `@[implemented_by]`, etc.).

| Filename | Purpose | Source-of-Truth Read | Emits / Asserts |
|----------|---------|----------------------|-----------------|
| `check_axioms.py` | Validate AXIOMS.md sync and parse PrintAxioms output | All `.lean` files + `AXIOMS.md` | Declared axioms match documented registry |
| `check_lean_hygiene.py` | Enforce zero `sorry`/debug commands in all proofs | All `.lean` files in Compiler/Verity/Contracts/Benchmark | No unsafe constructs outside explicit allowlist |
| `check_lean_warning_regression.py` | Enforce Lean warning count does not regress | Build log, `artifacts/lean_warning_baseline.json` | Warning count ≤ baseline |
| `check_proof_length.py` | Enforce proof size limits (soft: 30 lines, hard: 50 lines) | All `.lean` files | Proofs under limit or in allowlist |
| `check_rewrite_proof_metadata.py` | Fail closed when rewrite proof metadata is missing or stale | `Compiler/Yul/PatchRulesCatalog/*.lean`, `Compiler/ParityPacks.lean` | Rewrite rules declare non-empty `proofId` and proof refs resolve |
| `check_trust_surface_registry.py` | Validate all non-axiom trusted surfaces are documented | Lean files (scan for `native_decide`, `@[implemented_by]`, `partial def`, ECM assumptions) | All trust mechanisms documented in `AXIOMS.md` or `TRUST_ASSUMPTIONS.md` |

---

## coverage (5)

Scripts verifying that property-test manifests and generated test stubs are
complete and consistent with the Lean proof declarations.

| Filename | Purpose | Source-of-Truth Read | Emits / Asserts |
|----------|---------|----------------------|-----------------|
| `check_macro_health.py` | Dispatcher — runs all macro-health sub-checks | Orchestrates `check_macro_property_test_generation` | Aggregated exit code |
| `check_macro_property_test_generation.py` | Check/sync generated macro-property test stubs | `Contracts/Counter/Counter.lean`, `Contracts/`, `artifacts/macro_property_tests/` | Stubs match expected from `verity_contract` declarations |
| `check_property_coverage.py` | Check all theorems in the manifest have property tests or documented exclusions | `artifacts/property_manifest.json`, `test/Property*.t.sol` | Full manifest coverage |
| `check_property_manifest.py` | Check property test files reference valid manifest theorems | `artifacts/property_manifest.json`, `test/Property*.t.sol` | No dangling theorem references |
| `check_property_manifest_sync.py` | Check `property_manifest.json` is in sync with actual Lean proof declarations | Lean files in `Contracts/*/` | Manifest matches actual declarations |

---

## selector-gas (7)

Scripts that verify function selector hashing and static gas model integrity.

| Filename | Purpose | Source-of-Truth Read | Emits / Asserts |
|----------|---------|----------------------|-----------------|
| `check_gas.py` | Dispatcher — runs all gas-related CI checks | Orchestrates `check_gas_calibration`, `check_gas_model_coverage`, `check_gas_report` | Aggregated exit code |
| `check_gas_calibration.py` | Cross-check static gas bounds against Foundry gas measurements | Static gas report, Foundry gas measurements | Static bounds monotonicity and calibration |
| `check_gas_model_coverage.py` | Ensure static gas builtin coverage matches generated Yul call sites | `Compiler/Gas/StaticAnalysis.lean`, `artifacts/yul/` | All Yul calls have static gas models |
| `check_gas_report.py` | Validate `lake exe gas-report` output and monotonicity invariants | `lake exe gas-report` subprocess output | Report format and `deploy ≤ total`, `runtime ≤ total` |
| `check_patch_gas_delta.py` | Check static gas deltas between baseline and patch-enabled reports | Baseline and patch static gas reports | Delta statistics within acceptable range |
| `check_selector_fixtures.py` | Validate selector hashing against solc fixtures | `scripts/fixtures/SelectorFixtures.sol` | Keccak implementation matches solc-derived selectors |
| `check_selectors.py` | Verify selector hashing across CompilationModel, IR proofs, and Yul artifacts | `Compiler/CompilationModel.lean`, `Compiler/Proofs/*/`, `artifacts/yul/` | 11 selector-related invariants across compiler layers |

---

## workflow-ci (11)

Scripts that validate CI/workflow configuration files, issue metadata,
and miscellaneous repository hygiene.

| Filename | Purpose | Source-of-Truth Read | Emits / Asserts |
|----------|---------|----------------------|-----------------|
| `check_benchmark_cases.py` | Validate optional benchmark-case metadata | `Benchmark/*/case.yaml`, `Benchmark/*/FormalAudit.lean` | Metadata completeness and proof status consistency |
| `check_docs_workflow_sync.py` | Validate docs workflow trigger paths | `.github/workflows/docs.yml` | Expected trigger paths present |
| `check_feature_ownership.py` | Validate the `feature_ownership.json` artifact structure | `artifacts/feature_ownership.json` | Required fields present and schema valid |
| `check_issue_1060_integrity.py` | Validate Issue #1060 progress ledger schema and anti-inflation invariants | `artifacts/issue_1060_progress.json` | Roadmap items and semantic theorem tracking correct |
| `check_issue_submission.py` | Detect placeholder/template-only GitHub issue submissions | GitHub issue text (stdin/args) | Fails if issue contains placeholder text |
| `check_issue_templates.py` | Validate GitHub issue form YAML structure | `.github/ISSUE_TEMPLATE/*.{yml,yaml}` | YAML structure valid; no CI runner artifact contamination |
| `check_parity_pack_metrics.py` | Validate parity-pack identity metrics from a generated diff report | Yul identity diff report JSON | Divergence metrics within acceptable bounds |
| `check_paths.py` | Validate path safety invariants (case-insensitive collision detection) | Git-tracked files | No case-insensitive path collisions on case-sensitive filesystems |
| `check_solc_pin.py` | Enforce pinned solc version consistency across CI, tooling, and docs | `.github/workflows/verify.yml`, `foundry.toml`, `TRUST_ASSUMPTIONS.md` | Single solc version across all config sources |
| `check_verify_sync.py` | Unified verify.yml sync validator (table-driven, 57 KB) | `.github/workflows/verify.yml` | Workflow job configuration matches consistency rules |
| `check_yul.py` | Run Yul-related CI checks | `Compiler/Proofs/IRGeneration/IRInterpreter.lean`, `artifacts/yul/` | Yul builtin boundary and compilation consistency |

---

## artifact-generator (10)

`generate_*.py` scripts that compute and write deterministic JSON (or Lean) artifacts.
All support `--check` mode to fail if the committed artifact is stale.

| Filename | Purpose | Source-of-Truth Read | Emits / Asserts |
|----------|---------|----------------------|-----------------|
| `generate_contract.py` | Generate scaffold files for a new Verity contract | Template strings in script | Creates `Contracts/{Name}/`, `test/Property{Name}.t.sol`, compiler spec stub |
| `generate_evmyullean_capability_report.py` | Generate EVMYulLean capability and unsupported-node reports | `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeLowering.lean`, `evmyullean_capability.py` | `artifacts/evmyullean_capability_report.json`, `artifacts/evmyullean_unsupported_nodes.json` |
| `generate_evmyullean_fork_audit.py` | Generate EVMYulLean fork-audit artifact recording divergence from upstream | Hardcoded fork divergence data | `artifacts/evmyullean_fork_audit.json` |
| `generate_evmyullean_native_lowering_report.py` | Generate native lowering coverage artifact | Five Lean files in `Compiler/Proofs/YulGeneration/Backends/` | `artifacts/evmyullean_native_lowering_report.json` |
| `generate_layer2_boundary_catalog.py` | Generate the Layer 2 proof-boundary machine-readable catalog | Hardcoded Python dict (no external deps) | `artifacts/layer2_boundary_catalog.json` |
| `generate_macro_property_tests.py` | Generate Foundry property-test stubs from `verity_contract` declarations | `Contracts/` (scans for `verity_contract` macros) | `artifacts/macro_property_tests/`, `test/Property*.t.sol` |
| `generate_print_axioms.py` | Generate `PrintAxioms.lean` that audits axiom dependencies of all theorems | All `.lean` files in proof directories | `Compiler/Proofs/PrintAxioms.lean` |
| `generate_verification_status.py` | Generate verification status artifact from live repository metrics | `verification_metrics.collect_metrics()` (scans Lean + test files) | `artifacts/verification_status.json` |
| `generate_verify_sync_spec.py` | Regenerate verify workflow sync spec from the authoritative Python module | `verify_sync_spec_source.build_spec()` (hardcoded Python dict) | `scripts/verify_sync_spec.json` |
| `generate_yul_identity_diff_report.py` | Generate deterministic Yul identity diff report | Verity-generated and solc-generated `.yul` files | `artifacts/yul/` diff report |

---

## Verification: Prototype Parity

The following commands confirm that `sync_engine.py` reproduces the three
simplest `generate_*.py` scripts byte-for-byte.

### Setup

```
cd <repo-root>
```

### Rule: `verify-sync-spec`

```
$ python3 scripts/sync_engine.py --rule verify-sync-spec --check
[verify-sync-spec] scripts/verify_sync_spec.json is up to date

$ python3 scripts/generate_verify_sync_spec.py --check
verify_sync_spec.json is up to date
```

**Side-by-side diff (engine → temp file vs. committed artifact):**
```
$ TMPDIR=$(mktemp -d)
$ python3 scripts/sync_engine.py --rule verify-sync-spec --output "$TMPDIR/vss.json"
[verify-sync-spec] wrote /tmp/.../vss.json
$ diff "$TMPDIR/vss.json" scripts/verify_sync_spec.json
(no output — files are identical)
DIFF EMPTY: verify-sync-spec matches
```

### Rule: `layer2-catalog`

```
$ python3 scripts/sync_engine.py --rule layer2-catalog --check
[layer2-catalog] artifacts/layer2_boundary_catalog.json is up to date

$ python3 scripts/generate_layer2_boundary_catalog.py --check
Layer 2 boundary artifact is up to date: .../artifacts/layer2_boundary_catalog.json
```

**Side-by-side diff:**
```
$ python3 scripts/sync_engine.py --rule layer2-catalog --output "$TMPDIR/l2.json"
[layer2-catalog] wrote /tmp/.../l2.json
$ diff "$TMPDIR/l2.json" artifacts/layer2_boundary_catalog.json
(no output — files are identical)
DIFF EMPTY: layer2-catalog matches
```

### Rule: `verification-status`

```
$ python3 scripts/sync_engine.py --rule verification-status --check
[verification-status] artifacts/verification_status.json is up to date

$ python3 scripts/generate_verification_status.py --check
Verification artifact is up to date: .../artifacts/verification_status.json
```

**Side-by-side diff:**
```
$ python3 scripts/sync_engine.py --rule verification-status --output "$TMPDIR/vs.json"
[verification-status] wrote /tmp/.../vs.json
$ diff "$TMPDIR/vs.json" artifacts/verification_status.json
(no output — files are identical)
DIFF EMPTY: verification-status matches
```

All three diffs are empty. The engine produces byte-for-byte identical output
to the original scripts for all three rules.
