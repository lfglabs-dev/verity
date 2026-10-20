# Verity 2.0 Architecture: Safe-by-Construction, Verified Compiler Shims & Bidirectional Transpilation

Verity 2.0 upgrades the Verity formal verification compiler from manual IR/Yul boundary glue to a **Safe-by-Construction** declarative verification and optimization stack. Every contract compilation path, arithmetic/memory/call shim, storage-frame clause, and Solidity import round-trip is backed by machine-checked Lean 4 proofs (`0 sorry`, `0 native_decide` in proof modules).

---

## 1. Safe-by-Construction Core (`0 unsafe_yul`, `0 sorry`, `0 native_decide`)

Verity 2.0 eliminates ad-hoc `unsafe_yul` escape hatches in standard protocol contracts in favor of first-class, denotationally modeled IR primitives and verified compiler shims:

- **Total Denotational Semantics (`Verity/Core/Model/Denote.lean`)**: All supported `Expr` and `Stmt` nodes have total, fuel-free or structurally recursive semantics over `Verity.ContractState` and `DenoteOracle`.
- **Kernel-Only Proof Hygiene**: `scripts/check_lean_hygiene.py` enforces zero `sorry`, zero `allowUnsafeReducibility`, and zero `native_decide` across `Compiler/Proofs/**` and `Verity/Proofs/**`. Executable finite witnesses use kernel-verified `by decide`.
- **Modular Proof Discipline**: `scripts/check_proof_length.py` and `scripts/check_dead_private_decls.py` keep proof scripts composable, short, and free of dead private lemmas.

---

## 2. Declarative Contracts & Auto-Frame (`by decide`)

In `verity_contract` v2, functions declare their storage footprint and postconditions directly in the contract header:

- **`modifies [...]` & `preserves [...]` Clauses**: Functions declare the exact set of storage fields they mutate. All remaining contract storage fields are automatically placed in the `preserves` frame.
- **Automatic Frame Discharge**: Physical and logical slot disjointness (`slotDisjointFromStmt`, `findFieldWriteSlots`) is decidable at compile time and discharged via `by decide` + `writeUintFieldSlots_storage_frame` / `eval_preserves_inferred_untouched_slot`.
- **`ensures` & `invariant` Clauses**: Declarative postconditions and contract-level invariants bind directly to `Denote.denoteFunction` outcomes without manual Yul state-threading boilerplate.

---

## 3. `VerifiedCompilerShim` & `SlotCoalescingShim` Catalog

Instead of inline assembly blocks for fixed-point arithmetic, hashing, token transfers, or packed/warm storage accesses, Verity 2.0 provides the **`VerifiedCompilerShim`** and **`SlotCoalescingShim`** catalog:

| Category | Shim Primitive | Semantics & Optimization |
| --- | --- | --- |
| Fixed-Point Math | `VerifiedCompilerShim.mulDivDown(a, b, c)` | Full-precision $\lfloor (a \cdot b) / c \rfloor \pmod{2^{256}}$ with zero-divisor guard |
| Fixed-Point Math | `VerifiedCompilerShim.mulDivUp(a, b, c)` | Full-precision $\lceil (a \cdot b) / c \rceil \pmod{2^{256}}$ with rounding-up guard |
| WAD Math ($10^{18}$) | `VerifiedCompilerShim.wMulDown(a, b)` | Specialized $10^{18}$ down-rounded multiplication |
| WAD Math ($10^{18}$) | `VerifiedCompilerShim.wDivUp(a, b)` | Specialized $10^{18}$ up-rounded division |
| Scratch Hashing | `VerifiedCompilerShim.keccak256Pair(offset)` | 64-byte scratch-space Keccak-256 pair hashing |
| ERC-20 Calls | `VerifiedCompilerShim.safeTransfer(token, to, amount)` | Verified optional-bool returndata ERC-20 `transfer` |
| ERC-20 Calls | `VerifiedCompilerShim.safeTransferFrom(token, from, to, amount)` | Verified optional-bool returndata ERC-20 `transferFrom` |
| Static Reads | `VerifiedCompilerShim.staticBalanceOf(token, owner)` | Read-only `staticcall` ERC-20 `balanceOf` |
| Storage Coalescing | `SlotCoalescingShim` | Coalesces redundant `SLOAD`/`SSTORE` and packed subfield updates under EIP-2929 warm/cold slot accounting |

---

## 4. `ShimArena` + `GasCostModel` Autoresearch Engine

Verity 2.0 pairs its verified shim catalog with a deterministic EVM gas-cost model (`GasCostModel`) and an equivalence-constrained search arena (`ShimArena`):

- **EIP-2929 & EIP-1153 Gas Accounting**: Models cold/warm `SLOAD` (2100 / 100 gas), dirty/clean `SSTORE` (20000 / 2900 / 100 gas), `TLOAD`/`TSTORE` (100 gas), memory expansion, and arithmetic opcodes.
- **Pareto Dominance Certification**: Candidate shim rewrites are accepted into the catalog only when accompanied by a machine-checked equivalence proof (`Denote.evalExpr` / `Denote.execStmt` preservation) and a non-increasing gas bound proved by `decide` / `omega`.

---

## 5. Uniswap v4 100% & Bidirectional Transpiler (`EmitVerity`)

### Uniswap v4 Full Coverage
Verity 2.0 models the full Uniswap v4 singleton architecture:
- **`PoolManager` & `PositionManager`**: Multi-word struct mappings (`mappingStruct`, `mappingStruct2`), nested pool-state mappings, and liquidity delta accounting.
- **EIP-1153 Transient Flash Accounting**: First-class `transient` storage fields (`isTransient := true`) lowered to `TLOAD`/`TSTORE` with frame-isolated proofs (`storage_writeTransientSlots`) guaranteeing that transient delta settlements never corrupt persistent pool storage.

### Bidirectional `import_verity` Transpiler (`Compiler/SolidityImport/EmitVerity.lean`)
To migrate existing Solidity codebases into idiomatic Verity 2.0 without manual rewriting:
1. **`emitVerityContract` (`importVerity`)**: Takes an imported `CompilationModel` and emits a complete `verity_contract <Name> where` v2 specification with typed `storage` slots (`Uint256`, `Int256`, `Address`, `Mapping`, `Mapping2`, `MappingStruct`, `transient`).
2. **Automatic `VerifiedCompilerShim` Recognition**: Detects WAD fixed-point idioms (`mulDivDown a b 10^18`, `mulDivUp a 10^18 b`), general `mulDivDown`/`mulDivUp`, 64-byte `keccak256`, and `SafeERC20` external call patterns (`detectExprShims`, `rewriteExprShimStep`), rewriting them into `VerifiedCompilerShim.*` calls.
3. **Automatic Footprint Inference (`inferFunctionFootprint`)**: Computes `modifiesFields`, `preservesFields`, `modifiesSlots`, and `preservesSlots` directly from statement writes and field slot/alias resolution, emitting `-- modifies [...] | preserves [...]` headers.
4. **Interactive `#emit_verity_contract` Command**: Allows inspecting the generated `verity_contract` v2 source directly inside Lean 4.
5. **Formal Round-Trip Bridge (`Compiler/Proofs/SolidityImport/EmitVerityBridge.lean`)**:
   - `inferredFootprint_sound` & `eval_preserves_inferred_untouched_slot`: Proves that `preservesFields` / `preservesSlots` are disjoint from `modifiesFields` / `modifiesSlots`, and every untouched slot is preserved by `.setStorage` execution.
   - `emitVerity_roundtrip_preserves_denote`: Proves that canonicalizing a `CompilationModel` and `FunctionSpec` through `emitVerityRoundtripModel` / `emitVerityRoundtripFunction` preserves `Denote.denoteFunction` across all execution states and transactions.
