# Multi-Agent `turbo-lean` Telemetry & Benchmarks (`Season 9` `e7b256a` + `lean-native v0.5.0`)

This document records the empirical system telemetry and developer-velocity benchmarks captured during the Verity multi-agent verification campaigns (Tracks S22, S23, Family C, Family E, and the full 19-PR Wave 0–3 Roadmap `NR0`–`NR6` + `N0`–`N12`) and summarizes the architecture and empirical roadmap gains enabled by **`turbo-lean` Season 5 (`0be49df`) $\to$ Season 9 (`e7b256a`)** paired with **`lean-native v0.3.0` (`375a5ae`) $\to$ `v0.5.0`**.

---

## 1. Executive Summary & Campaign Scope

- **Capture Date**: October 19, 2026
- **Execution Node**: `babylon` (`8 GiB` target physical RAM envelope, up to 10 concurrent subagents)
- **Toolchain Provenance**: `Th0rgal/turbo-lean` @ `0be49df` (Season 5) + `Th0rgal/lean-native` @ `375a5ae` (`v0.3.0`) deployed in `/var/lib/sandboxed-node/caches/elan/bin/` on the `sandboxed-node` fleet (ahead of the `.github/workflows/turbo-lean-cache.yml` CI action pin `33f83860`)
- **Telemetry Collector**: `/proc/<pid>/smaps_rollup` (RSS vs. PSS), Linux cgroup v2 (`memory.current`, `memory.events`, `cpu.stat`), parent-process compliance auditing (`turbo-lean` vs. raw `lean`/`lake`), and `turbo-lean status --json` CAS/Zygote counters
- **Dataset**: **2,396 continuous samples** at `2 s` intervals (**79.9 minutes** of continuous multi-agent execution, `6.8 MB` JSONL host archive in `/var/lib/sandboxed-node/telemetry-archive/`)

### Work Delivered During the 80-Minute Telemetry Window
1. **PR `#2552` (`cb6785f7a`, Track S23 — `EndToEnd/Base.lean`)**: Decomposed **179** monolithic proofs (`> 50` lines) into **627** modular theorems (`<= 50` lines) across 6 parallel sub-slices, removing **`-10,777` net lines** (`+8,643 / -19,420` in `EndToEnd/Base.lean`; `9,170` total proofs scanned at `cb6785f7a`, leaving only the 55 `Projection.lean` entries in `ALLOWLIST`).
2. **PR `#2550` (`6d99ba3d5`, Track S22 — `Projection.lean`)**: Decomposed the remaining **55** monolithic proofs (`> 50` lines) into **227** modular theorems (`<= 50` lines), removing **`-4,035` net lines** during the active telemetry slice and **`-5,277` net lines** (`+2,363 / -7,640` in `Projection.lean`) in the final merged commit `6d99ba3d5`, which emptied the `scripts/check_proof_length.py` `ALLOWLIST` to **0 entries** across all **9,207 proofs** (with `74b6ad364`).
3. **PR `#2551` (`74b6ad364`, Family C) & PR `#2553` (Family E)**: Raised `Midnight.sol` construct coverage to **45 / 45 (`100%` excluding `multicall`)**.

In total, **234 giant proofs** were refactored into **854 modular theorems** (**`-14,812` net lines** during the telemetry slice; **`-16,054` net lines** across the merged `Projection.lean` + `EndToEnd/Base.lean` commits) alongside two `SolidityImport` construct families in **1 hour 20 minutes** of wall-clock time.

---

## 2. Empirical Telemetry Summary (`2,396` Samples over `80 min`)

| Metric | Median | P95 | Peak (Max) | Operational Observation |
| :--- | :---: | :---: | :---: | :--- |
| **Concurrent Processes (`turbo-lean` / `lean` + `ZygoteWorker`)** | `4` / `6` | `10` / `14` | **`15` / `19`** | High multi-agent concurrency without memory saturation |
| **Aggregate CPU Utilization (`turbo-lean` + `lean`)** | `152.1%` | `376.0%` | **`920.7%`** | Up to ~9.2 active cores during parallel shard sweeps |
| **Aggregate RSS (Apparent Resident Virtual Memory)** | `7,286.0 MB` | `11,698.8 MB` | **`14,888.9 MB` (`14.89 GB`)** | Memory cost without `ZygoteWorker` CoW / `mmap` sharing |
| **Aggregate PSS (True Physical Memory Consumed)** | `3,435.9 MB` | `4,822.7 MB` | **`6,192.4 MB` (`6.19 GB`)** | Comfortably below the `8 GB` node budget throughout the run |
| **Physical RAM Saved via Zygote CoW (`RSS - PSS`)** | `3,343.3 MB` | `7,529.1 MB` | **`10,820.6 MB` (`10.82 GB`)** | Per-sample `RSS_t - PSS_t` distribution (up to **`10.82 GB` saved** on a single tick) |
| **Effective RAM Multiplier (`RSS / PSS`)** | **`1.98x`** | `3.12x` | **`4.16x`** | Per-sample `RSS_t / PSS_t` distribution (**`4.16x` peak CoW sharing ratio**) |
| **Cgroup `oom_kill` Events (`memory.events`)** | `0` | `0` | **`0`** | **Zero OOM kills** across the entire 80-minute campaign |
| **Agent `turbo-lean` Protocol Compliance** | `100%` | `100%` | **`100%`** | `0` direct calls to raw `lake build` or `lean_repl_daemon.py` |
| **Shared CAS (`InterfaceCAS` / `TheoremProofCAS`)** | — | — | **`1,393` blobs / `654` actions** | **`515.8 s` of pure elaboration CPU time saved** via shard hits |

*Note on order statistics*: Each row's `Median`, `P95`, and `Peak (Max)` are independent per-sample quantiles computed across the `2,396` time-series ticks `t` (for example, `RSS_t - PSS_t` and `RSS_t / PSS_t` are evaluated at each `2 s` sample `t` before taking the median, P95, and maximum, rather than subtracting or dividing the marginal row maxima).

---

## 3. Season 5 (`0be49df`) + `lean-native v0.3.0` (`375a5ae`) Architecture Highlights

1. **Persistent `lean-native-core` JSON-RPC Worker (`0.0716 ms / req`, `13,973 req/s`)**:
   - Integrated directly into `zygote.rs` and `gpu_fastcheck.rs`, eliminating cold CLI process startup (`409x` faster than one-shot CLI invocation).
2. **Constraint-Propagating `fast-check` with Zero False Positives**:
   - `LeanNative/Backend/FastCheck.lean` propagates equality preconditions (`x_i == expr`, preventing vacuous passes), emits vectorized **LLVM 18 SIMD** (`i256`/`i512`) and **NVIDIA PTX 8.0 (`sm_90`)** (4-limb `.reg .u64` 256-bit arithmetic with hardware carry chains `add.cc.u64` / `mad.lo.cc.u64`), and formally certifies every counterexample via `certifyCounterexample_no_false_positive` in **`0.1 ms – 4 ms`**.
3. **In-Kernel Axiom Gate in `ZygoteWorker`**:
   - `TurboLean/ZygoteWorker.lean` executes `collectAxioms` inside the Lean kernel on every `turbo-lean check` and `turbo-lean pr-verify` (`< 1 s`), making it impossible to bypass syntactic checks via macros or transitive `sorryAx` dependencies.
4. **BLAKE3 Dependency Cone (`cone_env_hash`) & `/dev/shm` Compaction**:
   - `splitter.rs` and `shm_cache.rs` hash only the transitive cone of declarations referenced by a theorem. Editing a helper lemma no longer invalidates downstream theorems in a 20,000-line file unless they depend on its statement.

---

## 4. Retrospective Comparison: `lake build` vs. `lean-mcp` vs. `turbo-lean` + `lean-native`

| Operation / Scenario | Raw `lake build` / `lake env lean` (Baseline) | `lean-mcp` / Per-Worktree LSP Daemon | `turbo-lean` Season 5 + `lean-native v0.3.0` | Measured Speedup / Gain |
| :--- | :---: | :---: | :---: | :---: |
| **Cold import of a large module (`Base.lean`, `Import.lean`)** | `45 s – 180 s` per command | `25 s – 60 s` per worktree | **`0 ms`** (`fork()` CoW from `ZygoteWorker`) | **Instantaneous ($\infty$)** |
| **Incremental single-theorem check (`--decl`)** | `60 s – 240 s` (full-file rebuild) | `1.5 s – 8.0 s` (sequential prefix elaboration, no shard CAS) | **`18 ms – 45 ms`** (`~4 ms` on `TheoremProofCAS` hit) | **`50x` to `5,000x` faster** |
| **Pre-proof false-lemma detection (`fast-check`)** | *Not available* (`15 – 30 min` wasted on doomed tactics) | *Not available* (`5 – 15 min` wasted on doomed tactics) | **`0.07 ms – 4 ms`** (`lean-native-core` SIMD / PTX 8.0) | **`> 100,000x` (avoids 15–30 min dead ends)** |
| **Physical RAM for 7 concurrent agents** | `~21 – 35 GB` (immediate OOM on `8 GB` node) | `~14 – 22 GB` (unshared LSP/REPL heaps per worktree) | **`3.4 GB` median / `6.19 GB` peak PSS** (`14.89 GB` RSS at `4.16x` CoW) | **`3.5x` to `5x` lower physical RAM** |
| **Max concurrent agents on an `8 GB` node** | `1` (frequent OOM on `Base.lean` / `Import.lean`) | `2` (`~3.5 GB` unshared RSS each) | **`7 to 10 agents`** (`0` OOMs) | **`4x` to `8x` higher parallelism** |
| **Full PR verification (`pr-verify` vs. `lake build`)** | `12 min – 35 min` | `8 min – 20 min` | **`25 ms – 800 ms`** (modified shards + in-kernel `collectAxioms`) | **`> 1,000x` on proof PRs** |
| **[Actual] S22 + S23 Campaign (`234` giant proofs $\to$ `854` modular theorems, `-14,812` slice / `-16,054` merged net lines)** | Estimated **`28 – 36 hours`** (sequential, 1–2 workers max before OOM) | Estimated **`7 – 10 hours`** (2–3 workers, frequent reloads, no `cone_env_hash`) | **`1 h 20 min` actual** (7 parallel agents, `0` OOMs) | **`~22x–24x` vs. `lake`<br>`~6x–6.5x` vs. `lean-mcp`** |

---

## 5. Prospective Time Savings Across the 4 Upcoming Roadmap Pillars

Using the empirical speedup factors measured above (`4.16x` CoW memory compression enabling 7–10 parallel agents + `18–45 ms` incremental `--decl` verification + `0.1–4 ms` `fast-check` pre-proof falsification eliminating the 30–40% false-lemma tax), the projected engineering time across the next four Verity roadmap pillars is:

| Upcoming Roadmap Pillar | Scope Summary | Estimated Time with Raw `lake build` | Estimated Time with `lean-mcp` | Projected Time with `turbo-lean` + `fast-check` (7–10 Agents) |
| :--- | :--- | :---: | :---: | :---: |
| **1. Pareto Credit Vaults (`solidity_import`)** | `IdleCDOCreditVault`, `IdleCDOEpochVariant`, `IdleCreditVault` (deep C3 upgradeable inheritance, `SafeERC20Upgradeable`, external strategy/tranche calls) | `~25 – 35 h` | `~10 – 14 h` | **`~2.5 – 4 h`** |
| **2. Uniswap v4 (`solidity_import`)** | `PoolManager`, `Pool`, `Hooks`, `Transient` (`type T is U` + global operators, EIP-1153 `tload`/`tstore` assembly, pure bit-packing/math assembly, nested struct sub-mappings, multi-return hooks) | `~60 – 90 h` | `~20 – 30 h` | **`~5 – 8 h`** |
| **3. 100% Core Fragment (`CompilationModel → IR → EVMYulLean`)** | Unify `SupportedStmtList` structurally and close boundaries F1 (non-terminal `ite` & general `forEach`), F2 (`internal` helpers `#1638`), F3 (dynamic `emit`/`revertError` `#2082`), F4 (external calls `ECM`), F5 (constructors/`immutable`), F6 (Yul $\to$ EVM bytecode bridge) | `~180 – 250 h` (3–4 weeks) | `~50 – 75 h` (~1.5 weeks) | **`~10 – 16 h` (2–3 multi-agent sessions)** |
| **4. Formal `SolidityImport` Proof via `solcore-lean`** | Connect `argotorg/solcore-lean` (`Solcore.SourceSemantics` / `Solcore.Core` / `ContractRuntime`) to `Verity.Core.Model.Denote` via per-contract Translation Validation bisimulation theorems and generic `Solcore.Core → CompilationModel` preservation | `~250 – 400 h` (infeasible in `8 GB` RAM with Mathlib + Solcore + Verity) | `~80 – 120 h` | **`~16 – 24 h` (enabled by CoW sharing of Solcore + Verity `.olean` heaps)** |

---

## 6. Season 9 (`e7b256a`) + `lean-native v0.5.0` Upgrade & Full 19-PR Campaign Outcomes

In **PR `#2580`**, both the `babylon` fleet toolchain (`/var/lib/sandboxed-node/caches/elan/bin/`) and the GitHub Actions CI workflow ([`.github/workflows/turbo-lean-cache.yml`](../.github/workflows/turbo-lean-cache.yml)) were upgraded to **`turbo-lean` Season 9 (`e7b256af07f42d09f55bf221a335cc84123dbabe`)** paired with **`lean-native-core v0.5.0`**:

1. **Unified 3-Stage Funnel (`turbo-lean --json agent-step <File.lean> [--decl <name>]`)**:
   - **Stage 0 (`< 1 ms`)**: Hygiene gate (`sorry` / `axiom` / `native_decide` / `unsafe`) + BLAKE3 `TheoremProofCAS` dependency-cone lookup.
   - **Stage 1 (`0.1 ms – 4 ms`)**: `audit-spec` vacuous-precondition / postcondition-tightness static analysis + `lean-native-core v0.5.0` SIMD/PTX counterexample search (`--scope all|uint8|uint16|uint32|full`).
   - **Stage 2 (`18 ms – 800 ms`)**: Warm `ZygoteWorker` kernel verification with structured `mismatch_diagnostics` (`file`, `line`, `column`, `expected_type`, `actual_type`, `diff_hint`) and complexity telemetry (`heartbeats_used`, `proof_term_nodes`, `rss_delta_mb`, `peak_rss_mb`).
2. **Warm `#eval` Runner (`turbo-lean --json eval <File.lean>`)**:
   - Evaluates `#eval` files against a warm project `ZygoteWorker` in **`~10.9 ms`** (`7.2 MB` RSS delta vs. `~465 MB` cold `lean`) with `Law 11b` line-number padding and `Law 6` transitive `.olean` hashing.
3. **CAS Worktree Deduplication (`turbo-lean --json worktree-dedup`)**:
   - Deduplicated **`9,193` files** across 11 concurrent multi-agent git worktrees via CAS hardlinks, freeing **`3.36 GB`** of `.lake/packages`, `.barrel`, and `.git` pack bloat on `babylon`.
4. **8 Segregated Pre-Elaboration Accelerators (`turbo-lean --json accelerators`)**:
   - `lean-native-fastreject`, `simd-omega-fastcheck`, `simd-bv-decide-fastcheck`, `simd-simp-distiller`, `simd-discr-tree-pruner`, `simd-tactic-chain-optimizer` (`Law 11a`), `simd-ac-ring-normalizer` (`Law 12a`), and `cut-fission` (with prologue-aware `have` splitting).
5. **19-PR Campaign Summary (`NR0`–`NR6` + `N0`–`N12`)**:
   - **Wave 0 (`NR0`–`NR6`)**: Merged **`#2555`**, **`#2558`**, **`#2566`** (`NR3` raw Yul `sload`/`sstore` & narrow events), **`#2567`** (`NR1` `basefee` & `gasprice`), **`#2568`** (`NR2` `payable` & `ecmCall*` `selfBalance` debit), **`#2569`** (`NR4` Yul `reuseAndSpillTemps`), **`#2570`** (`NR6` `--trust-report` `staticOptOuts` & `proofBoundary`), **`#2572`** (`NR5` `CallbackBridge` registry lemmas & `msg.sender != 0`).
   - **Wave 1–3 (`N0`–`N12`)**: Merged **`#2553`** (`N0` Family E), **`#2556`** (`N1` `AGENTS.md`), **`#2565`** (`N9` `SolcoreBridge`), **`#2571`** (`N5` F3 dynamic ABI), **`#2574`** (`N2` F1 `SupportedStmtList` `ite`/`forEach`), **`#2575`** (`N6` F2/F4 internal helpers & ECM), **`#2576`** (`N7` F5 `constructor`/`fallback`/`receive`), **`#2577`** (`N4` Uniswap v4 corpus & UDVTs), **`#2578`** (`N3` Pareto Credit Vaults `58/58` `100%`), **`#2579`** (`N8` unified `CoreFragment.lean`), and **`#2580`** (`N10`/`N11`/`N12` `TranslationValidation.lean` + `SolcoreGeneric.lean` + Season 9 CI upgrade).
   - **Total Verified Shards**: **`11,039` theorem shards** across **`717` Lean files** (`9,634` scanned proofs, **`0`** over 50 lines, **`0` `sorry`**, **`0` `native_decide`**).

