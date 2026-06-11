# Doc-Sync Consolidation Inventory (P7)

Seed document for collapsing the ~31 `*sync*`/`check_*` doc-sync checkers and
~19 `generate_*` generators in `scripts/` into one schema-driven pipeline.

Scope: inventory + design only. No checker is deleted or modified by this
document. Every script below remains authoritative until its replacement ships
and `make check` / CI parity is demonstrated.

Sources: the `check:` target in `Makefile` (lines 125–170), `scripts/REFERENCE.md`,
and `.github/workflows/*.yml`.

## 1. Full inventory

Legend for **Source**: `lean-grep` = greps/parses Lean sources; `artifact` =
reads `artifacts/*.json`; `doc-grep` = parses Markdown docs; `lake` = runs a
Lean executable; `repo` = other repo files (workflows, lakefiles, foundry.toml).
**Output**: `exit` = exit code only; `regen` = writes a file, with `--check`
drift mode unless noted.

### 1.1 Invoked by `make check`

| Script | Guards (pair / invariant) | Source | Output | Shared helpers |
|---|---|---|---|---|
| check_property_manifest.py | `test/property_manifest.json` ↔ `Property*.t.sol` theorem names | artifact + Foundry tests | exit | property_utils |
| check_property_coverage.py | manifest entries ↔ test coverage ↔ exclusions.json | artifact + Foundry tests | exit | property_utils |
| check_property_manifest_sync.py | manifest ↔ actual Lean proof theorems | lean-grep + artifact | exit | property_utils |
| check_contract_structure.py | `Contracts/` layout (Spec/Invariants/Proofs files present) | lean-grep + fs | exit | property_utils |
| check_paths.py | case-insensitive checkout collisions; bridge quantification | `git ls-files` | exit | property_utils |
| check_compilationmodel_split.py | `Compiler/CompilationModel.lean` facade ↔ submodules | lean-grep | exit | property_utils |
| check_axioms.py | `AXIOMS.md` ↔ discovered Lean `axiom` decls; PrintAxioms output | lean-grep + doc-grep | exit | property_utils |
| check_trust_surface_registry.py | non-axiom trust mechanisms ↔ AXIOMS.md / TRUST_ASSUMPTIONS.md / docs | lean-grep + doc-grep | exit | property_utils |
| check_benchmark_cases.py | `Benchmark/Cases/*/case.yaml` metadata ↔ FormalAudit.lean presence | repo (yaml) + fs | exit | property_utils |
| generate_verification_status.py | `artifacts/verification_status.json` | lean-grep (via collect_metrics) | regen + `--check` | verification_metrics |
| generate_layer2_boundary_catalog.py | `artifacts/layer2_boundary_catalog.json` (static catalog) | hardcoded dict | regen + `--check` | property_utils |
| check_verification_status_doc.py | `docs/VERIFICATION_STATUS.md` ↔ verification_status.json | artifact + doc-grep | exit | verification_metrics, property_utils |
| check_layer2_boundary_sync.py | Layer-2 claims across README / AXIOMS.md / docs / docs-site | doc-grep (expected snippets) | exit | — |
| check_layer2_boundary_catalog_sync.py | Layer-2 docs ↔ layer2_boundary_catalog.json | artifact + doc-grep | exit | — |
| generate_verify_sync_spec.py | `scripts/verify_sync_spec.json` ↔ verify_sync_spec_source.py | python source | regen + `--check` | verify_sync_spec_source |
| check_verify_sync.py | verify.yml ↔ Makefile ↔ verify_sync_spec.json (jobs, paths, commands) | repo + artifact | exit | workflow_jobs |
| check_bridge_coverage_sync.py | bridge coverage docs ↔ native lowering report | artifact + doc-grep | exit | — |
| check_builtin_bridge_matrix_sync.py | builtin bridge docs ↔ interpreter_feature_matrix.json + lowering report | artifact + lean-grep + doc-grep | exit | interpreter_feature_matrix |
| check_interpreter_feature_boundary_catalog_sync.py | proof-boundary category note ↔ feature matrix | artifact + doc-grep | exit | interpreter_feature_matrix |
| check_interpreter_feature_summary_sync.py | `docs/INTERPRETER_FEATURE_MATRIX.md` summary table ↔ feature matrix counts | artifact + doc-grep | exit | interpreter_feature_matrix |
| check_low_level_call_boundary_sync.py | low-level-call boundary note ↔ feature matrix status | artifact + doc-grep | exit | interpreter_feature_matrix |
| check_linear_memory_boundary_sync.py | linear-memory boundary note ↔ feature matrix status | artifact + doc-grep | exit | interpreter_feature_matrix |
| check_axiomatized_primitive_boundary_sync.py | keccak256 axiomatized-primitive note ↔ feature matrix status | artifact + doc-grep | exit | interpreter_feature_matrix |
| check_struct_mapping_surface_sync.py | struct-mapping docs ↔ `Compiler/CompilationModel/Types.lean` surface | lean-grep + doc-grep | exit | — |
| check_solc_pin.py | solc pin across verify.yml / foundry.toml / TRUST_ASSUMPTIONS.md | repo + doc-grep | exit | — |
| check_issue_templates.py | `.github/ISSUE_TEMPLATE/*.yaml` structure + log contamination | repo (yaml) | exit | property_utils |
| check_docs_workflow_sync.py | docs.yml push paths ↔ pull_request paths | repo (yaml) | exit | — |
| check_macro_health.py | dispatcher → check_macro_property_test_generation.py | sub-script | exit | — (dispatch) |
| check_storage_layout.py | storage slots: EDSL ↔ Spec ↔ Compiler layers | lean-grep | exit | property_utils |
| generate_storage_layout_report.py | `artifacts/storage_layout_report.json` + `STORAGE_LAYOUT_SUMMARY.md` | lake (`verity-storage-layout-report`) | regen + `--check --no-lean` | property_utils |
| check_lean_hygiene.py | no debug commands / sorry / unsafe reducibility in proofs | lean-grep | exit | property_utils |
| check_gas.py coverage | dispatcher → check_gas_model_coverage.py (also report/calibration subcmds) | sub-scripts | exit | — (dispatch) |
| check_compiler_boundaries.py | dispatcher → 7 boundary sub-checkers (builtin-list, contract/package/layer imports, mapping-slot, evmyullean-capability, package-glob) | sub-scripts | exit | — (dispatch) |
| check_split_compiler_test_artifacts.py | `packages/verity-compiler/lakefile.lean` globs ↔ `Compiler/*Test.lean` | repo + fs | exit | property_utils |
| check_yul.py --builtin-boundary-only | native bridge lemma presence for Yul builtins | lean-grep | exit | property_utils |
| check_rewrite_proof_metadata.py | rewrite rules ↔ proofId refs ↔ ParityPacks composition proofs | lean-grep | exit | property_utils |
| generate_evmyullean_capability_report.py | `artifacts/evmyullean_capability_report.json` + `evmyullean_unsupported_nodes.json` | lean-grep | regen + `--check` | evmyullean_capability |
| generate_evmyullean_native_lowering_report.py | `artifacts/evmyullean_native_lowering_report.json` | lean-grep (bridge files) | regen + `--check` | — |
| generate_evmyullean_fork_audit.py | `artifacts/evmyullean_fork_audit.json` ↔ lake-manifest pinned commit | repo + hardcoded FORK_AUDIT | regen + `--check` | — |
| generate_print_axioms.py | `PrintAxioms.lean` ↔ all theorem decls | lean-grep | regen + `--check` | property_utils |
| check_proof_length.py | proof line limits (soft 30 / hard 50, allowlist) | lean-grep | exit | property_utils |
| check_issue_1060_integrity.py | `artifacts/issue_1060_progress.json` ledger schema + repo facts | artifact + repo | exit | — |
| update_doc_numbers.py --check | README.md + docs-site/public/llms.txt metric markers ↔ verification_status.json | artifact + doc-grep | regen + `--check` | — |
| (unittest discover `test_*.py`) | unit coverage of the above checkers | — | exit | — |

### 1.2 CI-only (workflows, not `make check`)

| Script | Guards | Source | Output | Helpers |
|---|---|---|---|---|
| check_selectors.py | selector uniqueness / signature ↔ Yul labels / constants | lean-grep + Yul + keccak | exit | keccak256, property_utils, check_selector_fixtures |
| check_selector_fixtures.py | selector hashing ↔ `solc --hashes` fixtures | repo + solc | exit | keccak256 |
| check_lean_warning_regression.py | lake build warnings ↔ `artifacts/lean_warning_baseline.json` | build log + artifact | exit / `--write-baseline` | — |
| check_patch_gas_delta.py | gas regression: baseline vs patch TSV reports | TSV reports | exit (+ markdown summary) | — |
| check_split_package_builds.py | per-package lake builds succeed | lake | exit | — |
| check_issue_submission.py | issue-intake guard (issue body validation) | GitHub event | exit | — |
| check_macro_roundtrip_fuzz_coverage.py | macro roundtrip fuzz coverage | lean-grep | exit | — |
| report_property_coverage.py | coverage statistics report (informational) | artifact + tests | report (md/json/text) | property_utils |
| sync_verification_status_doc.py | writer twin of check_verification_status_doc (patches doc + hygiene baseline) | artifact | regen (no --check) | verification_metrics, property_utils |
| extract_property_manifest.py | writer twin of check_property_manifest_sync (emits manifest) | lean-grep | regen | property_utils |

## 2. Consolidation clusters

### Cluster A — "Lean decl → JSON artifact → Markdown doc" pipelines (16 scripts → 1)

The dominant pattern: a generator scrapes Lean source (or runs a Lean exe) into
an `artifacts/*.json` snapshot, and one or more checkers grep Markdown docs to
assert they match that snapshot.

Members:
- generate_verification_status.py / check_verification_status_doc.py / sync_verification_status_doc.py / update_doc_numbers.py
- generate_layer2_boundary_catalog.py / check_layer2_boundary_sync.py / check_layer2_boundary_catalog_sync.py
- generate_evmyullean_capability_report.py / generate_evmyullean_native_lowering_report.py / generate_evmyullean_fork_audit.py / check_bridge_coverage_sync.py
- check_builtin_bridge_matrix_sync.py / check_interpreter_feature_boundary_catalog_sync.py / check_interpreter_feature_summary_sync.py
- generate_storage_layout_report.py
- generate_print_axioms.py

Proposal: **`scripts/docsync.py`** driven by a declarative schema
(`scripts/docsync_spec.json` or a Python source module mirroring the
`verify_sync_spec_source.py` pattern, which is already the house style for
schema-driven checking). Each pipeline entry declares:

```
{ "id": "verification_status",
  "extract": {"kind": "lean-grep" | "lake-exe" | "static" | "python-fn", ...},
  "artifact": "artifacts/verification_status.json",
  "doc_bindings": [ {"doc": "docs/VERIFICATION_STATUS.md",
                     "binding": "marker" | "table" | "snippet" | "count",
                     ...} ] }
```

Modes: `docsync.py generate [id...]` (replaces all `generate_*` + `sync_*` +
`update_doc_numbers.py` writers), `docsync.py check [id...]` (replaces the
paired checkers; exit-code semantics identical to today). The
`interpreter_feature_matrix.py` loader becomes one `extract.kind`.

### Cluster B — conditional proof-boundary note checkers (4 scripts → schema rows in Cluster A)

check_low_level_call_boundary_sync.py, check_linear_memory_boundary_sync.py,
check_axiomatized_primitive_boundary_sync.py,
check_struct_mapping_surface_sync.py.

These are already near-identical thin wrappers: read
`artifacts/interpreter_feature_matrix.json` (or one Lean file), decide whether
a boundary note is required, then grep docs for the note. They differ only in
feature keys and note text. Proposal: a `"binding": "conditional-note"` row
type in the Cluster A schema (`when: feature X not fully proved → require
snippet S in docs D1..Dn`). 4 scripts collapse into 4 JSON rows.

### Cluster C — property manifest / coverage family (5 scripts → 1)

check_property_manifest.py, check_property_coverage.py,
check_property_manifest_sync.py, extract_property_manifest.py,
report_property_coverage.py.

All are already thin consumers of `property_utils.py` (load_manifest,
collect_covered, THEOREM_RE...). Proposal: **`scripts/property_pipeline.py`**
with subcommands `extract`, `check` (manifest + coverage + lean-sync in one
pass — they currently re-parse the same files three times), `report`.
property_utils.py stays as the shared library.

### Cluster D — cross-file constant/pin sync checks (4 scripts → 1)

check_solc_pin.py, check_docs_workflow_sync.py, check_builtin_list_sync.py
(via check_compiler_boundaries), generate_verify_sync_spec.py +
check_verify_sync.py.

Pattern: assert the same literal value/list appears consistently across N repo
files (workflow yaml, foundry.toml, Lean string lists, Makefile). Proposal:
extend the existing **check_verify_sync.py table-driven validator** (and
`verify_sync_spec_source.py` contract) with generic "literal pin" and
"list-equality" rule kinds; solc-pin, docs-workflow paths, and
builtin-list become spec entries. check_verify_sync.py is the surviving
binary; `workflow_jobs.py` remains its parser library.

### Cluster E — Lean structure/hygiene lints (9 scripts → 1 + rule modules)

check_contract_structure.py, check_compilationmodel_split.py,
check_lean_hygiene.py, check_proof_length.py, check_paths.py,
check_storage_layout.py, check_rewrite_proof_metadata.py,
check_split_compiler_test_artifacts.py, check_trust_surface_registry.py and
check_axioms.py (the lean-grep halves).

Pure lints: grep Lean sources, no artifact/doc pairing. They share
property_utils scrubbers but each re-walks the tree. Proposal:
**`scripts/lean_lint.py`** — one tree walk, pluggable rule registry, `--only` /
`--skip` flags matching the current dispatcher conventions
(check_compiler_boundaries.py / check_macro_health.py / check_gas.py already
prove the dispatcher pattern works; lean_lint generalizes it with a single
parse pass instead of N subprocesses).

### Cluster F — external-toolchain checks (keep separate)

check_selectors.py, check_selector_fixtures.py, check_yul.py, check_gas.py
family, check_patch_gas_delta.py, check_lean_warning_regression.py,
check_split_package_builds.py, check_benchmark_cases.py,
check_issue_templates.py, check_issue_1060_integrity.py,
check_issue_submission.py.

These depend on solc/Foundry/lake build logs/GitHub events rather than the
Lean↔artifact↔doc axis. Consolidating them buys little and risks much; out of
scope for the doc-sync pipeline. (check_gas.py already is its own dispatcher.)

## 2.1 Migrated so far (P7 status)

`scripts/docsync.py` (declarative entry registry + engine, `--check` / `--only` /
`--list`) has landed. Migrated entries — each legacy script is now a thin shim
that delegates to docsync, its Makefile line invokes
`python3 scripts/docsync.py --check --only <entry>`, and its unit tests target
docsync directly:

- [x] check_low_level_call_boundary_sync.py → `low_level_call_boundary` (Cluster B)
- [x] check_linear_memory_boundary_sync.py → `linear_memory_boundary` (Cluster B)
- [x] check_axiomatized_primitive_boundary_sync.py → `axiomatized_primitive_boundary` (Cluster B)
- [x] check_struct_mapping_surface_sync.py → `struct_mapping_surface` (Cluster B)
- [x] check_layer2_boundary_sync.py → `layer2_boundary` (Cluster A)
- [x] check_interpreter_feature_boundary_catalog_sync.py → `interpreter_feature_boundary_catalog` (Cluster A)

Still pending from Cluster A: the verification-status trio +
update_doc_numbers.py, layer2 catalog generator/checker, the EVMYulLean report
generators, builtin-bridge / feature-summary matrix checkers,
generate_storage_layout_report.py, generate_print_axioms.py.
`verify_sync_spec_source.py` pins the new docsync Makefile commands
(regenerate `verify_sync_spec.json` after any further migration).

## 3. Summary

| Cluster | Today | Proposed | Surviving entry point |
|---|---|---|---|
| A. Lean→artifact→doc pipelines | 16 | 1 | `docsync.py` + `docsync_spec` |
| B. Conditional boundary notes | 4 | 0 (schema rows in A) | — |
| C. Property manifest family | 5 | 1 | `property_pipeline.py` |
| D. Constant/pin sync | 5 | 1 | `check_verify_sync.py` (extended spec) |
| E. Lean structure lints | 10 | 1 | `lean_lint.py` |
| F. External toolchain | 11 | 11 (unchanged) | as-is |
| **Total in scope (A–E)** | **40** | **4** | |

Already-thin wrappers over shared helpers (lowest-risk migrations first):
- `interpreter_feature_matrix.py` consumers (Cluster B + the three matrix-sync checkers).
- `property_utils.py` consumers in Cluster C.
- `verification_metrics.py` trio (generate/check/sync verification status).
- The dispatcher scripts (check_compiler_boundaries.py, check_macro_health.py, check_gas.py) — proof that the `--only/--skip` consolidation UX is already accepted.

Migration constraints:
1. Each replaced checker must keep an alias shim (or Makefile line) until
   `verify_sync_spec.json` is updated, since check_verify_sync.py pins the
   Makefile/workflow command lists.
2. `make check` exit-code semantics and per-check error messages must be
   preserved verbatim where tests (`test_check_*.py`) assert on them; the unit
   tests migrate cluster-by-cluster.
3. AUDIT.md / TRUST_ASSUMPTIONS.md / AXIOMS.md sync rules (CLAUDE.md
   non-negotiable #1) apply when Cluster A lands, since it moves trust-surface
   checking into a schema.
