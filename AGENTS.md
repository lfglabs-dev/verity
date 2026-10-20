# Agent Guide for Verity (`AGENTS.md` / `CLAUDE.md`)

Both `AGENTS.md` and `CLAUDE.md` are authoritative for all coding agents (`claudecode`, `codex`, `opencode`) working on `verity`. Keep them synchronized whenever agent workflows or conventions evolve.

---

## 1. Non-Negotiables & Hard Rules

1. **Zero ProofShortcuts**:
   - **No `sorry`**, **no new project `axiom`s**, and **no `native_decide`** in compiler, importer, or proof modules (enforced by `scripts/check_lean_hygiene.py` and `scripts/check_axioms.py`).
   - No `#eval`, `#check`, or `#print` left in proof files.
   - Proofs must stay **under 30 lines** (over 50 fails `scripts/check_proof_length.py`). Decompose long proofs into small helper lemmas.
2. **Never Weaken Checks or Goldens**:
   - Never weaken a lint, boundary check, golden model (`model.golden`), or mutation test to make CI green.
   - Any change to `model.golden`, `docs/TRUST_ASSUMPTIONS.md`, or `docs/AXIOMS.md` must be justified in the PR description and kept synchronized in the same commit.
3. **100% Construct-Generic Design (Zero Benchmark Coupling)**:
   - Every compiler pass (`Compiler/`), Solidity importer feature (`Compiler/SolidityImport/`), standard library module (`Verity/Stdlib/`), proof (`Compiler/Proofs/`), and smoke/differential fixture (`Contracts/SolidityImportSmoke/`, `scripts/solidity_differential/`) **must be 100% generic and named after the Solidity/EVM language construct**.
   - **Never** hardcode benchmark-specific contract names (`Midnight`, `Market`, `Offer`), library names, or struct/function identifiers (`popFront`, `popBack`, `_begin`, `_end`, `value`, `wExp` domain constants) inside `verity`.
   - External benchmark contracts (such as Morpho Midnight, Uniswap, OpenZeppelin, Pareto) belong **only** in `scripts/solidity_import_corpus/manifest.json` (to prioritize which generic Solidity constructs to implement next) or in their own downstream verification repositories (e.g., `morpho-midnight-verity`).
4. **Required Pre-Merge Gates (Run on the Exact PR Head)**:
   ```bash
   if [ -d /var/lib/sandboxed-node/caches ]; then
     export PATH="/var/lib/sandboxed-node/caches/elan/bin:$PATH"
     export TURBO_LEAN_HOME="/var/lib/sandboxed-node/caches/turbo-lean"
   else
     export TURBO_LEAN_HOME="${TURBO_LEAN_HOME:-$HOME/.cache/turbo-lean}"
   fi
   export LEAN_NUM_THREADS=$(nproc)
   turbo-lean pr-verify --base origin/main --json
   turbo-lean pr-verify --base origin/main --project-dir . --receipt .lake/turbo-receipt.json
   turbo-lean verify-receipt .lake/turbo-receipt.json
   python3 scripts/check_proof_length.py
   make check
   python3 scripts/solidity_import_mutations.py
   # Plus smoke + loss + programs differential campaigns & PrintAxioms check:
   python3 scripts/generate_print_axioms.py --check
   ```
   Never claim completion without passing evidence on the exact commit SHA.

---

## 2. Turbo-Lean Season 9 (`e7b256a` / Wave 5) + `lean-native v0.5.0` Productivity Protocol (Mandatory for All Lean Edits)

Because each agent shell tool call runs in a fresh subshell, running `lake build <TargetFile>` or `lake env repl` in an edit loop wastes 2–10 minutes per edit re-loading `.olean` imports and bloats RAM (8–16 GiB RSS per worktree).

**Every Lean agent MUST exclusively use `turbo-lean` and its persistent in-memory Zygote REPL daemon (`TurboLean.ZygoteWorker` + `lean-native-core v0.5.0`), NEVER raw `lake build`, `lake env lean`, or `lake env repl` in edit loops:**

### Rule 1 — Mandatory Shared CAS, Worktree Deduplication & Persistent Worker Environment
On `sandboxed-node` hosts, always export `TURBO_LEAN_HOME=/var/lib/sandboxed-node/caches/turbo-lean` and `PATH="/var/lib/sandboxed-node/caches/elan/bin:$PATH"` (falling back to `${TURBO_LEAN_HOME:-$HOME/.cache/turbo-lean}` on standard local machines) in every shell invocation so all agents and worktrees share the two-level `InterfaceCAS` and `TheoremProofCAS`, the `/dev/shm` `cone_env_hash` dependency-cone cache, the per-device shared hardlink pool (`turbo-lean worktree-dedup`), and the persistent `ZygoteWorker` + `lean-native-core` JSON-RPC worker (`0.04 ms/req`):
```bash
if [ -d /var/lib/sandboxed-node/caches ]; then
  export PATH="/var/lib/sandboxed-node/caches/elan/bin:$PATH"
  export TURBO_LEAN_HOME="/var/lib/sandboxed-node/caches/turbo-lean"
else
  export TURBO_LEAN_HOME="${TURBO_LEAN_HOME:-$HOME/.cache/turbo-lean}"
fi
```

### Rule 2 — Mandatory Unified Agent Loop (`agent-step`), Spec Vacuity Audit (`audit-spec`), and Counterexample Gate (`fast-check`)
Before spending any time writing tactics for a new auxiliary lemma (`theorem` / `private theorem` over `Uint256`, `BitVec`, offsets, masks, memory/calldata bounds, or state invariants), agents **MUST** use `turbo-lean --json agent-step` (which chains Stage 0 hygiene & dependency-cone cache $\to$ Stage 1 `audit-spec` vacuity check & `lean-native-core v0.5.0` certified counterexample search with hypothesis suggestion $\to$ Stage 2 warm `ZygoteWorker` kernel verification with structured `mismatch_diagnostics`, `heartbeats_used`, `proof_term_nodes`, `rss_delta_mb`, and `peak_rss_mb`):
```bash
# Unified 3-stage agent verification funnel (hygiene -> audit-spec/fast-check -> Zygote kernel check):
turbo-lean --json agent-step Path/To/File.lean --decl <lemma_name> --project-dir . --max-memory-mb 1800

# Standalone spec vacuity audit or SIMD/GPU counterexample search on a candidate lemma (with := by sorry):
turbo-lean --json audit-spec Path/To/File.lean --decl <lemma_name>
turbo-lean --json fast-check --transpile-lean Path/To/File.lean --decl <lemma_name>
```
**Why this is mandatory**: Empirical telemetry shows that ~30–40% of LLM proof time is wasted attempting to prove a false or vacuous helper lemma missing an overflow (`offset + 32 <= 2^256`), alignment, or slot-disjointness precondition, or miscalculating numeric offset deltas on `type mismatch` errors. `agent-step` falsifies untrue lemmas in `0.1 ms - 4 ms` and returns structured `mismatch_diagnostics` (`inferred_type`, `expected_type`, `inferred_rhs`, `expected_rhs`, `numeric_delta`) on proof errors.

### Rule 3 — Incremental Declaration Checking (`check`), Deterministic Warm Evaluation (`eval`), & 8 Segregated Accelerators
`turbo-lean check` automatically reuses the persistent `TurboLean.ZygoteWorker` REPL daemon (`Shared_Clean` `.olean` memory across workers, global LRU RSS governor `TURBO_LEAN_MAX_TOTAL_ZYGOTE_RSS_MB`, `LEAN_STACK_SIZE_KB=262144`, `O(N)` closed-section pruning, `theorem ... where` stubbing, and safe `have`-block fission guard `canSafelyFissionHavePrologue`) alongside 8 built-in segregated accelerators (`simd-simp-distiller`, `lean-native-fastreject`, `cut-fission`, `simd-discr-tree-pruner`, `simd-tactic-chain-optimizer` for `rw`-chain fusion, `simd-bv-decide-fastcheck`, `simd-omega-fastcheck`, and `simd-ac-ring-normalizer` for `ac_rfl`). For `#eval` / `#check` smoke and differential drivers, use `turbo-lean eval` (`~10.9 ms` warm, `7.2 MB` RSS vs `465 MB` cold `lean`, with `Law 11b` line-number preservation):
```bash
# Enforce zero statement drift during proof decomposition/refactoring:
turbo-lean --json check Path/To/File.lean --decl <theorem_name> --project-dir .

# Check all uncached theorem shards in a file in parallel:
turbo-lean --json check Path/To/Target.lean --parallel-shards --project-dir .

# Deterministic warm evaluation for #eval / smoke / differential drivers (~65x less RAM than raw lean):
turbo-lean --json eval Path/To/SmokeDriver.lean --project-dir . --timeout-ms 30000
```

### Rule 4 — Pre-PR Verification & Scoped In-Kernel Axiom Gate (`< 1 s`)
Before opening or updating a PR, run `turbo-lean --json pr-verify --base origin/main` (supports `--scope <dir>` and baseline-aware hygiene regression checking `regression_items_against`, verifying all modified theorem shards against `origin/main` and running the in-kernel `collectAxioms` gate inside `ZygoteWorker` in `< 1 s`) alongside `python3 scripts/check_proof_length.py`:
```bash
turbo-lean --json pr-verify --base origin/main --project-dir . --receipt .lake/turbo-receipt.json
turbo-lean --json verify-receipt .lake/turbo-receipt.json
python3 scripts/check_proof_length.py
```

### Step 5 — Rebuild `.olean` interfaces ONLY when module signatures/imports change
When you add or change a public `def`, `structure`, `inductive`, or theorem statement imported by downstream modules, run `turbo-lean build` (which wraps Lake with CAS caching and seeds theorem shards) and `turbo-lean worktree-dedup`:
```bash
export LEAN_NUM_THREADS=$(nproc)
turbo-lean --json worktree-dedup --project-dir .
turbo-lean --json build --seed-shards --project-dir .
```
Note: `scripts/lean_repl_daemon.py check --file F --decl D` is retained only as a compatibility shim that delegates to `turbo-lean check F --decl D --project-dir .`. Always invoke `turbo-lean` directly.

---

## 3. Agent Speed & Efficiency: What To Do vs. What To Avoid

### DO (Fast & Reliable)
- **Always configure `TURBO_LEAN_HOME` (`/var/lib/sandboxed-node/caches/turbo-lean` on fleet nodes or `${TURBO_LEAN_HOME:-$HOME/.cache/turbo-lean}` locally) and `/var/lib/sandboxed-node/caches/elan/bin` in `PATH`** so all subagents share the warm `InterfaceCAS` and `TheoremProofCAS`.
- **Always run `turbo-lean fast-check --transpile-lean <File.lean> --decl <lemma_name>`** on every new helper lemma (`:= by sorry`) before writing tactics (`0.1 ms - 4 ms` via `lean-native-core`).
- **Always use `turbo-lean check <File.lean> --decl <name> --disallow-statement-changes --json`** during proof refactoring and `--project-dir .` for interactive edits (`~18–45 ms` via the persistent Zygote REPL daemon, `~4 ms` on warm CAS hit).
- **Always use `turbo-lean pr-verify --base origin/main --json` + `python3 scripts/check_proof_length.py`** to validate PR diffs and in-kernel `collectAxioms` before committing/pushing.
- **Reuse local `.lake` build caches on worker nodes**: In a fresh workspace clone, run `scripts/ci_local_persistence.sh restore-lean` or copy/hardlink an existing `/var/lib/sandboxed-node/*/verity/.lake` cache before running `turbo-lean`.
- **Search existing lemmas first** (`git grep`) before proving arithmetic, bitvector, memory, or storage frame properties from scratch.
- **Test single fixtures/mutants during development** (e.g., `python3 scripts/solidity_import_mutations.py --task <name>`) and use `--jobs auto` (or `--shard I/N --jobs auto`) for full campaigns.
- **Check zero Lean warning regressions before pushing**: Prefix intentionally unused proof hypotheses with `_` (e.g. `_aligned`) and verify `python3 scripts/check_lean_warning_regression.py --log lake-build.log`.
- **Keep PRs small and single-purpose**: one Solidity construct family, one proof refactoring slice, or one CI/harness instrument per PR. Stage files explicitly (`git add <paths>`), never `git add -A`.

### AVOID (Slow & Error-Prone Anti-Patterns Observed in Subagents)
- **NEVER run raw `lake build`, `lake env lean`, or `lake env repl` in an edit loop**. Every agent is monitored for rogue `lean`/`lake`/`repl` processes not spawned by `turbo-lean`.
- **NEVER attempt to prove a new arithmetic/word/memory helper lemma without first running `turbo-lean fast-check --transpile-lean`**.
- **NEVER poll background builds with `sleep 60` / `sleep 240` loops**. Debug tactics exclusively with `turbo-lean check <File.lean> --decl <name> --project-dir .`.
- **NEVER run serial unsharded 293-mutant loops or two concurrent full mutation campaigns on the same host** (each mutant rebuilds `Import.lean` using ~2.7 GiB RAM; running two full suites concurrently starves CPU/RAM and hits 600s timeouts).
- **NEVER rely on `cd` persisting across separate `Bash` tool calls** (each tool call resets `cwd` to the workspace root; always pass `--project-dir` / `-C <dir>` or chain `cd <dir> && ...` in the same command).
- **NEVER leave scratch notes or status files** (`PROGRESS.md`, `NOTES.md`, `TODO.md`, `.bak` files) in the git worktree, and never stage borrowed helper scripts (`git add -A`) into unrelated feature PRs.
- **NEVER write monolithic tactic scripts (>30 lines)** or unconstrained `simp` calls over huge definitions; they cause `maxHeartbeats` timeouts and brittle proofs.
- **NEVER drop work silently during rebases/merges**: inspect both sides of every conflict, keep every improvement, and fold duplicate PRs explicitly before closing.

---

## 4. Mathlib4 Code Style & Naming Conventions

All new and refactored Lean code in `Verity/` and `Compiler/` must adhere to **Mathlib4** conventions:

1. **Naming Conventions**:
   - **`UpperCamelCase`** for types, structures, inductive types, typeclasses, and named `Prop` predicates (e.g., `CompilationModel`, `ContractState`, `SupportedStmtList`, `MemoryCoherent`).
   - **`lowerCamelCase`** for functions, definitions returning data/terms, local variables, and parameters (e.g., `evalExpr`, `compileStmt`, `execIRStmt`, `byteMemory`).
   - **`snake_case`** for theorems and lemmas (terms of `Prop`), named descriptively after their conclusion and key hypotheses using standard Mathlib connectors:
     - Connectors: `_of_`, `_iff`, `_eq`, `_ne`, `_lt`, `_le`, `_zero`, `_add`, `_sub`, `_mul`, `_append`, `_mem`, `_get`, `_set`, `_none`, `_some`.
     - Example: `exec_stmt_mstore_eq_of_memory_coherent`, `read_word_write_word_ne`, `decode_uint256_encode_uint256`.
2. **Formatting & Structure**:
   - **Indentation**: 2 spaces; never use tabs.
   - **Line length**: Maximum 100 characters per line.
   - **Declaration headers**: Keep `:= by` on the end of the declaration header line (or after the return type line for multi-line signatures), with the tactic block indented by 2 spaces.
   - **Structured Proof Focusing (`· `)**: Always use middle-dot (`· `) focusing for multi-goal branches (`rcases`, `induction`, `constructor`, `by_cases`), indented consistently. Avoid unstructured multi-goal tactic sequences.
   - **Explicit `have` steps**: State intermediate proof obligations with explicit types (`have hSlot : slot < 2^256 := by ...`) to keep elaboration fast and error messages local.
   - **Docstrings**: Document every public definition, structure, and key theorem with `/-- ... -/`.

---

## 5. Abstractions for Maintainability, Reliability & Proof Performance

When writing or refactoring compiler passes, specifications (`Denote`), and proofs (`Compiler/Proofs/`):

1. **Good Simp Normal Forms & Abstraction Barriers**:
   - Establish small, orthogonal `@[simp]` lemmas for projections, state reads-over-writes, and constructor inversions (`@[simp] theorem get_set_self`, `@[simp] theorem get_set_ne`).
   - Do **not** unfold large recursive evaluators (`evalExpr`, `execStmt`, `lowerCall`) directly with `simp` in downstream proofs. Instead, prove dedicated unfolding/step equations (`exec_stmt_assign`, `exec_stmt_mstore`, `lower_call_static`) and keep implementation internals behind clean API lemmas (or `irreducible` barriers where appropriate).
2. **Compositional State & Frame Lenses**:
   - Express state transitions and invariants via reusable frame/lens predicates (e.g., storage-only updates preserve `memory`, `byteMemory`, `calldata`, `events`, and `sender`; memory-only updates preserve `storage` and `transientStorage`) rather than repeating field-by-field record destruction in every statement proof.
   - `Compiler/Proofs/StateLenses.lean` provides `StorageWordsFrame` (with `refl`/`trans`) plus `@[simp]` projection lenses (`memory_writeUintSlots`, `events_writeAddressFieldSlots`, …) and storage-channel lenses (`transientStorage_writeUintSlots`, `storage_writeTransientTargets`, …) for the source-semantics storage writers; extend it (prove the writer's `StorageWordsFrame` once, derive the lenses) instead of unfolding a writer to read an untouched field.
   - `Compiler/Proofs/Frames.lean` provides `execStmt_*_continue_inv` inversions and `ownedEq_*_of_disjoint` resource lenses; use them instead of `rw [show execStmt … = (match …) from rfl]` + `cases` in statement proofs.
3. **Modular File Decomposition (Avoid Monoliths)**:
   - Split oversized files (`Import.lean`, `Stmt.lean`, `SourceSemantics.lean`, etc.) by construct family or semantic layer with minimal `import` dependencies. Smaller modules reduce `.olean` load times in `turbo-lean`, enable parallel shard verification, and isolate proof maintenance.
4. **Heartbeat Hygiene (Zero `maxHeartbeats` Escalation)**:
   - Never paper over slow elaboration by raising `set_option maxHeartbeats`. If a lemma exceeds default heartbeats:
     1. Replace unconstrained `simp` with `simp only [...]` or `rw [...]`.
     2. Extract complex sub-expressions into `let` / `have` bindings with explicit types.
     3. Split case analyses into standalone helper lemmas (<30 lines each).

---

## 6. Core Commands & Reference Docs

```bash
if [ -d /var/lib/sandboxed-node/caches ]; then
  export PATH="/var/lib/sandboxed-node/caches/elan/bin:$PATH"
  export TURBO_LEAN_HOME="/var/lib/sandboxed-node/caches/turbo-lean"
else
  export TURBO_LEAN_HOME="${TURBO_LEAN_HOME:-$HOME/.cache/turbo-lean}"
fi
export LEAN_NUM_THREADS=$(nproc)
turbo-lean --json agent-step F.lean --decl NAME --project-dir .           # Unified Stage 0-2 funnel (hygiene -> audit-spec/fast-check -> Zygote)
turbo-lean --json audit-spec F.lean --decl NAME                           # Pre-proof vacuous precondition & postcondition audit
turbo-lean --json fast-check --transpile-lean F.lean --decl NAME          # 0.1-4ms SIMD/PTX counterexample gate
turbo-lean --json check F.lean --decl NAME --project-dir .                # ~4-20ms Zygote REPL check (0 interface drift)
turbo-lean --json eval F.lean --project-dir . --timeout-ms 30000          # ~10.9ms deterministic warm #eval driver (~65x less RAM)
turbo-lean --json worktree-dedup --project-dir .                          # Multi-worktree CAS hardlink deduplication (4.26ms lease)
turbo-lean --json accelerators --project-dir .                            # List 8 active segregated tactic & SIMD accelerators
turbo-lean --json pr-verify --base origin/main --project-dir .            # <1s incremental PR + in-kernel collectAxioms gate
python3 scripts/check_proof_length.py                                     # Verify all proofs <= 50 lines
turbo-lean --json build --seed-shards --project-dir .                     # Full CAS build when interfaces change
make check                                                                # Run local CI-equivalent validation
make test-python                                                          # Run Python unit tests
make test-foundry                                                         # Run Foundry differential tests
```

- Project overview and review order: [README.md](README.md)
- Contribution conventions: [CONTRIBUTING.md](CONTRIBUTING.md)
- Roadmap: [docs/ROADMAP.md](docs/ROADMAP.md)
- Telemetry & `turbo-lean` benchmarks: [docs/TELEMETRY_AND_TURBO_LEAN_BENCHMARKS.md](docs/TELEMETRY_AND_TURBO_LEAN_BENCHMARKS.md)
- Solidity import guide & per-family checklist: [docs/SOLIDITY_IMPORT.md](docs/SOLIDITY_IMPORT.md)
- Trust assumptions & axioms: [docs/TRUST_ASSUMPTIONS.md](docs/TRUST_ASSUMPTIONS.md), [docs/AXIOMS.md](docs/AXIOMS.md)
