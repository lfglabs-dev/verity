# Scripts Reference

This document is the long-form reference for script responsibilities.

## Verify workflow sync

- `check_verify_sync.py`: unified table-driven validator for workflow invariants.
- `verify_sync_spec_source.py`: authoritative verify workflow sync contract.
- `generate_verify_sync_spec.py`: regenerates/checks the committed JSON artifact from the Python source.
- `verify_sync_spec.json`: generated mirror of the verify workflow contract for easy inspection and diff review.
- `ci_timeout_watchdog.py`: warns when recent verify jobs spend too much of their timeout budget.
- `check_docs_workflow_sync.py`: keep the docs workflow self-triggering and aligned across push/pull_request path filters.

## Issue #1060 automation

- `check_issue_1060_integrity.py`: ledger schema + anti-inflation + repository-fact checks (run in CI).
- `check_issue_templates.py`: validate GitHub issue form structure and fail on accidental CI-log contamination.

## Artifacts and documentation consistency

- `docsync.py`: schema-driven doc-sync engine (P7 consolidation). One declarative registry of artifact/doc bindings; run `python3 scripts/docsync.py --check [--only <entry>]` or `--list`. Migrated entries: `low_level_call_boundary`, `linear_memory_boundary`, `axiomatized_primitive_boundary`, `struct_mapping_surface`, `layer2_boundary`, `interpreter_feature_boundary_catalog`. The legacy `check_*_sync.py` paths below remain as thin shims.
- `generate_verification_status.py`: refresh/check `artifacts/verification_status.json`.
- `generate_layer2_boundary_catalog.py`: refresh/check `artifacts/layer2_boundary_catalog.json`.
- `check_feature_ownership.py`: validate `artifacts/feature_ownership.json`, the major feature-surface ownership and proof-boundary registry.
- `check_verification_status_doc.py`: keep `docs/VERIFICATION_STATUS.md` aligned with the artifact-backed live totals.
- `check_layer2_boundary_sync.py`: shim for `docsync.py --only layer2_boundary` (Layer 2 proof-boundary claims across README/trust/docs/docs-site surfaces).
- `check_layer2_boundary_catalog_sync.py`: keep Layer 2 docs aligned with the machine-readable boundary catalog.
- `verification_metrics.py`: shared metric collection and strict artifact validation.
- `refresh_verification_artifacts.sh`: regenerate and validate the verification artifact.

## Property and proof boundaries

Primary guards:
- `property_pipeline.py`: consolidated property manifest/coverage pipeline (P7 Cluster C). Subcommands: `check [--only manifest|coverage|lean-sync]` (single manifest parse for all three checks), `extract` (regenerate `test/property_manifest.json`), `report` (coverage statistics; `--format`, `--fail-below`). The five legacy scripts (`check_property_manifest.py`, `check_property_coverage.py`, `check_property_manifest_sync.py`, `extract_property_manifest.py`, `report_property_coverage.py`) remain as thin shims.
- `lean_lint.py`: consolidated Lean structure/hygiene lint runner (P7 Cluster E). Dispatcher over rule modules with `--only/--skip/--list`; rules: `contract_structure`, `paths`, `compilationmodel_split`, `axioms`, `trust_surface_registry`, `storage_layout`, `lean_hygiene`, `split_compiler_test_artifacts`, `rewrite_proof_metadata`, `proof_length`. Each rule module (the legacy `check_*.py` file) keeps its logic and stays directly runnable for arg-bearing CI invocations.
- `check_axioms.py`: validate AXIOMS.md registry locations and parse `PrintAxioms.lean` dependency output (lean_lint rule `axioms`).
- `check_paths.py`: detect case-insensitive checkout hazards and enforce universal Layer-2 bridge quantification (lean_lint rule `paths`).
- `check_property_manifest.py`: shim for `property_pipeline.py check --only manifest`.
- `check_property_coverage.py`: shim for `property_pipeline.py check --only coverage`.
- `check_property_manifest_sync.py`: shim for `property_pipeline.py check --only lean-sync`.
- `check_builtin_bridge_matrix_sync.py`: keep the builtin bridge matrix artifact and docs in sync, including delegated env builtins.
- `check_interpreter_feature_boundary_catalog_sync.py`: shim for `docsync.py --only interpreter_feature_boundary_catalog`.
- `check_interpreter_feature_summary_sync.py`: keep the interpreter feature summary table aligned with the machine-readable feature matrix artifact.
- `check_low_level_call_boundary_sync.py`: shim for `docsync.py --only low_level_call_boundary`.
- `check_linear_memory_boundary_sync.py`: shim for `docsync.py --only linear_memory_boundary`.
- `check_axiomatized_primitive_boundary_sync.py`: shim for `docsync.py --only axiomatized_primitive_boundary`.
- `check_struct_mapping_surface_sync.py`: shim for `docsync.py --only struct_mapping_surface`.
- `check_storage_layout.py` (lean_lint rule `storage_layout`)
- `generate_storage_layout_report.py`: emit the per-contract storage layout JSON artifact (`artifacts/storage_layout_report.json`) and human-readable summary (`artifacts/STORAGE_LAYOUT_SUMMARY.md`) for migration/audit review (#1897). The Lean executable `verity-storage-layout-report` is the JSON source of truth; `--check --no-lean` is the drift gate run by `make check`.
- `check_lean_hygiene.py` (lean_lint rule `lean_hygiene`; the sorry/native_decide gate)
- `check_proof_length.py` (lean_lint rule `proof_length`)
- `check_macro_health.py`
- `check_compiler_boundaries.py`
- `test_check_struct_mapping_surface_sync.py`: unit coverage for the struct-mapping doc sync guard.

## Foundry/gas/selector pipeline

- `check_selectors.py`
- `check_yul.py`
- `check_gas.py`
- `check_patch_gas_delta.py`

## Helpers and generators

- `workflow_jobs.py`: shared workflow parsing and command matching helpers.
- `generate_print_axioms.py`
- `generate_contract.py`
- `generate_macro_property_tests.py`
