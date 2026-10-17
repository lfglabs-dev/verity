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
   export LEAN_NUM_THREADS=$(nproc)
   lake build
   make check
   python3 scripts/solidity_import_mutations.py
   # Plus smoke + loss + programs differential campaigns & PrintAxioms check:
   python3 scripts/generate_print_axioms.py --check
   ```
   Never claim completion without passing evidence on the exact commit SHA.

---

## 2. Fast & Persistent Lean REPL Workflow (Mandatory for All Lean Edits)

Because each agent shell tool call runs in a fresh subshell, running `lake build <TargetFile>` in an edit loop or piping one-shot `echo ... | lake env repl` wastes 2–10 minutes per edit re-loading `.olean` imports and re-elaborating multi-thousand-line files.

**Every Lean agent MUST use `scripts/lean_repl_daemon.py` to keep a single persistent `repl` process alive over a Unix socket:**

### Step 1 — Build imported dependency `.olean`s once
Before editing `Path/To/Target.lean`, build its *imported* dependencies once (not `Target.lean` in a loop):
```bash
export LEAN_NUM_THREADS=$(nproc)
lake build <ImportedModule1> <ImportedModule2>
```

### Step 2 — Start the persistent REPL daemon once per workspace
`scripts/lean_repl_daemon.py start` automatically clones/builds `leanprover-community/repl` at the tag matching `lean-toolchain` (`v4.31.0`) under `/tmp/lean-repl` if not yet present, and starts a persistent `lake env repl` server bound to `/tmp/verity-lean-repl.sock`:
```bash
python3 scripts/lean_repl_daemon.py start
```

### Step 3 — Load the file's imports (and unchanged prefix) ONCE into `header_env` (`env: 0`)
- To load only the `import` / `open` / `variable` / `namespace` header of the file you are editing:
  ```bash
  python3 scripts/lean_repl_daemon.py load-header --file Compiler/Proofs/IRGeneration/FunctionBody/Stmt.lean
  ```
- Or, when editing a theorem at line `4190` of a large file, load lines `1..4189` once into `header_env`:
  ```bash
  python3 scripts/lean_repl_daemon.py load-header \
    --file Compiler/Proofs/IRGeneration/FunctionBody/Stmt.lean \
    --until-line 4189
  ```

### Step 4 — Typecheck edits in ~1 second against the warm environment
After editing `Target.lean` on disk with your file-editing tool, check just the edited declaration/theorem line range (`start-line..end-line`) against the cached `header_env`—no JSON escaping or full-file rebuild required:
```bash
python3 scripts/lean_repl_daemon.py check \
  --file Compiler/Proofs/IRGeneration/FunctionBody/Stmt.lean \
  --start-line 4190 --end-line 4245
```
Or send ad-hoc commands / interactive tactics directly:
```bash
python3 scripts/lean_repl_daemon.py send --env 0 --cmd "theorem my_helper (x : Nat) : x + 0 = x := by simp"
python3 scripts/lean_repl_daemon.py send --proof-state 0 --tactic "simp"
```

### Step 5 — Run `lake build` ONLY before `git commit` / merge
Only after your edited definitions and proofs typecheck cleanly via `lean_repl_daemon.py check`, run:
```bash
LEAN_NUM_THREADS=$(nproc) lake build <TouchedModule>
```
once before committing, and run the full merge gates once before merging.

---

## 3. Agent Speed & Efficiency: What To Do vs. What To Avoid

### DO (Fast & Reliable)
- **Always set `LEAN_NUM_THREADS=$(nproc)`** on every `lake` or `lean` command.
- **Reuse local `.lake` build caches on worker nodes**: In a fresh workspace clone, run `scripts/ci_local_persistence.sh restore-lean` or copy an existing `/var/lib/sandboxed-node/work/*/verity/.lake` cache before building imported `.olean` dependencies.
- **Keep one persistent REPL daemon** (`python3 scripts/lean_repl_daemon.py start`) and iterate on individual lemmas in `<1–3s` using `load-header` + `check`.
- **Search existing lemmas first** (`git grep`) before proving arithmetic, bitvector, memory, or storage frame properties from scratch.
- **Test single fixtures/mutants during development** (e.g., `python3 scripts/solidity_import_mutations.py --task <name>`) and use `--jobs auto` (or `--shard I/N --jobs auto`) for full campaigns.
- **Check zero Lean warning regressions before pushing**: Prefix intentionally unused proof hypotheses with `_` (e.g. `_aligned`) and verify `python3 scripts/check_lean_warning_regression.py --log lake-build.log`.
- **Keep PRs small and single-purpose**: one Solidity construct family, one proof refactoring slice, or one CI/harness instrument per PR. Stage files explicitly (`git add <paths>`), never `git add -A`.

### AVOID (Slow & Error-Prone Anti-Patterns Observed in Subagents)
- **NEVER run `lake build <Module>` in a background loop with `sleep 60` / `sleep 240` polling build logs** to debug tactic errors.
- **NEVER run serial unsharded 293-mutant loops or two concurrent full mutation campaigns on the same host** (each mutant rebuilds `Import.lean` using ~2.7 GiB RAM; running two full suites concurrently starves CPU/RAM and hits 600s timeouts).
- **NEVER invoke `repl` as a one-shot pipe** (`echo '{"cmd": ...}' | lake env repl`) per edit; when the command exits, the loaded environment is destroyed and every call pays the full import cost.
- **NEVER rely on `cd` persisting across separate `Bash` tool calls** (each tool call resets `cwd` to the workspace root; always pass `-C <dir>` or chain `cd <dir> && ...` in the same command).
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
3. **Modular File Decomposition (Avoid Monoliths)**:
   - Split oversized files (`Import.lean`, `Stmt.lean`, `SourceSemantics.lean`, etc.) by construct family or semantic layer with minimal `import` dependencies. Smaller modules reduce `.olean` load times in `repl`, enable parallel `lake build`, and isolate proof maintenance.
4. **Heartbeat Hygiene (Zero `maxHeartbeats` Escalation)**:
   - Never paper over slow elaboration by raising `set_option maxHeartbeats`. If a lemma exceeds default heartbeats:
     1. Replace unconstrained `simp` with `simp only [...]` or `rw [...]`.
     2. Extract complex sub-expressions into `let` / `have` bindings with explicit types.
     3. Split case analyses into standalone helper lemmas (<30 lines each).

---

## 6. Core Commands & Reference Docs

```bash
export LEAN_NUM_THREADS=$(nproc)
python3 scripts/lean_repl_daemon.py start  # Start persistent Lean REPL daemon
lake build                                 # Verify all Lean proofs (pre-PR / pre-merge)
make check                                 # Run local CI-equivalent validation (no Lean build)
make test-python                           # Run Python unit tests
make test-foundry                          # Run Foundry differential tests
```

- Project overview and review order: [README.md](README.md)
- Contribution conventions: [CONTRIBUTING.md](CONTRIBUTING.md)
- Roadmap: [docs/ROADMAP.md](docs/ROADMAP.md)
- Solidity import guide & per-family checklist: [docs/SOLIDITY_IMPORT.md](docs/SOLIDITY_IMPORT.md)
- Trust assumptions & axioms: [docs/TRUST_ASSUMPTIONS.md](docs/TRUST_ASSUMPTIONS.md), [docs/AXIOMS.md](docs/AXIOMS.md)
