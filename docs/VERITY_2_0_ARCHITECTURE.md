# Verity 2.0 Architecture: Safe-by-Construction, Verified Compiler Shims & Bidirectional Transpilation

Verity 2.0 upgrades the Verity formal verification compiler from manual IR/Yul boundary glue to a **Safe-by-Construction** declarative verification and optimization stack. Every contract compilation path, arithmetic/memory/call shim, storage-frame clause, and Solidity import round-trip is backed by machine-checked Lean 4 proofs (`0 sorry`, `0 native_decide` in proof modules).

---

## 1. Safe-by-Construction Core (`0 unsafe_yul`, `0 sorry`, `0 native_decide`)

Verity 2.0 eliminates ad-hoc `unsafe_yul` escape hatches in standard protocol contracts in favor of first-class, denotationally modeled IR primitives and verified compiler shims:

- **Total Denotational Semantics (`Verity/Core/Model/Denote.lean`)**: All supported `Expr` and `Stmt` nodes have total, fuel-free or structurally recursive semantics over `Verity.ContractState` and `DenoteOracle`.
- **Kernel-Only Proof Hygiene & Zero `constructorCompat`**: `scripts/check_lean_hygiene.py --forbid-constructor-compat` enforces zero `sorry`, zero `allowUnsafeReducibility`, zero `native_decide`, and zero `constructorCompat` initialization escape hatches across `Compiler/Proofs/**`, `Verity/Proofs/**`, and `Contracts/**`. Executable finite witnesses use kernel-verified `by decide`.
- **Fail-Closed Trust Surface for Unverified ECMs**: `Compiler/CompilationModel/TrustSurface.lean`, `Verity/Macro/EffectAnalysis.lean`, and `Verity/Macro/Elaborate.lean` enforce a fail-closed gate (`hasUnverifiedECMs` / `validateVerifiedECMsOnly`) that rejects any external call module lacking a formal certificate unless explicitly opted out.
- **Modular Proof Discipline**: `scripts/check_proof_length.py` and `scripts/check_dead_private_decls.py` keep proof scripts composable, short, and free of dead private lemmas.

---

## 2. Total Specifications (`FnSpec`), Generic Frames (`unchangedExcept`) & Exact `Nat` Conservation

Verity 2.0 unifies contract specifications and eliminates silent specification blind spots:

- **Total Function Specifications (`FnSpec` & `FnSpec.Satisfies` in `Verity/Specs/Common.lean`)**:
  - Every function specification bundles `requires : ContractState → Prop`, `ensures : ContractState → α → ContractState → Prop`, and `writes : List SpecStorageKey` (generated automatically via `#gen_fn_spec` in `Verity/Macro/SpecGen.lean`).
  - `FnSpec.Satisfies` couples both directions: when `requires s` holds, execution succeeds, satisfies `ensures`, and preserves all untouched storage keys (`unchangedExcept spec.writes s s'`); when `¬requires s` holds, execution is guaranteed to revert (`ContractResult.revert`).
- **Unified Storage Frame (`SpecStorageKey` & `unchangedExcept`)**:
  - Replaces the legacy ~20 combinatorial `sameStorage*Context` predicates with a single algebraic frame predicate `unchangedExcept : List SpecStorageKey → ContractState → ContractState → Prop` equipped with reflexivity, symmetry, transitivity, and monotonicity (`unchangedExcept_subset`) plus fine-grained Composition (`WritesOnly` in `Verity/Specs/Composition.lean`).
- **Typed `StorageSlot` Lenses & `@[storage_simps]` (`Verity/Core.lean`)**:
  - First-class typed storage lenses (`StorageSlot.readUint`/`writeUint`, `readAddr`/`writeAddr`, `readMap`/`writeMap`, `readMap2`/`writeMap2`) and `@[storage_simps]` read-over-write rules eliminate hardcoded numeric slot indices (`slot 0`, `slot 1`) and prevent slot drift between contracts and specifications.
- **Non-Truncating $\mathbb{N}$ Conservation (`sumBalancesNat` in `Verity/Specs/Common/Sum.lean`)**:
  - Complements modular `Uint256` sums with exact natural-number balance conservation (`sumBalancesNat`), proving `sumBalancesNat_WriteTransfer` and `no_phantom_mint_nat` (no $2^{256}$ wraparound phantom minting is possible when recipient addition is overflow-checked).
- **Automated Specification Proof Tactics (`verity_prove_spec` in `Verity/Proofs/Stdlib/Automation.lean`)**:
  - `verity_step`, `verity_frame`, and `verity_prove_spec` automate monadic unfolding, branch splitting, and `unchangedExcept` frame discharge, complemented by Poka-Yoke compile-time guards (`checkDeclaredWritesCoverActual`, `checkNoSlotDrift` in `Verity/Macro/EffectAnalysis.lean`) and `ValueType.normalize` canonicalization (`Verity/Macro/Types.lean`).

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
- **Proof-Carrying `CertifiedPatchRule` / `CertifiedRuleOn` & `VerifiedCompilerShim.applyCertified` (`Compiler/Yul/PatchFramework.lean`, `Compiler/Proofs/VerifiedECMShims.lean`)**:
  - Unifies `ExprPatchRule`, `StmtPatchRule`, `BlockPatchRule`, and `ObjectPatchRule` under `CertifiedPatchRule α Sem`, `CertifiedRuleOn denote`, and `CertifiedPatchPack`, bundling the syntax rewrite (`toCertified`) with machine-checked semantic preservation (`preserves_eval`, `applyPack_sound`, `seq_apply_sound`).
- **Intra-Block `SLOAD` CSE & Packed Subfield Coalescing (`Compiler/Proofs/SlotCoalescingShim.lean`)**:
  - Proves cache coherence (`CacheCoherent`, `runSloadCSE_sound`) for intra-block `SLOAD` common-subexpression elimination and gas optimality (`coalescedPackedWritesGas_lt_uncoalesced`) for coalescing adjacent packed subfield writes into a single `SLOAD + mask/shift + SSTORE`.
- **$O(\log N)$ Binary Selector Dispatch & Scratch-Space Keccak-256 (`Compiler/Selector.lean`, `Compiler/Modules/Hashing.lean`, `Compiler/CompilationModel/EventEmission.lean`)**:
  - `SelectorDispatchTree` (`buildSelectorDispatchTree_lookup_eq_linear`) replaces linear $O(N)$ `switch` chains on contracts with $\ge 4$ entrypoints by a balanced binary pivot tree, while `keccak256ScratchWordModule` hashes 32/64-byte words directly in EVM scratch space (`0x00..0x40`) without bumping the `0x40` free-memory pointer.

---

## 6. Structural Compiler & Proof Deduplication (`Wave 4`)

Verity 2.0 compresses the compiler verification surface through four structural abstractions:

1. **Unified Surface-Clean Bridge Predicates (`SourceStmtBridged`, `SourceFunctionBridged`, `SourceContractBridged` in `Compiler/Proofs/IRGeneration/SupportedSpec.lean`)**:
   - Unifies statement and contract feature classification via `SurfaceFeature`, `hasSurfaceFeature`, `stmtSurfaceClean`, and `stmtsSurfaceClean` (`SourceStmtBridged_iff_surfaceClean`).
2. **Canonical Zero-Fuel / No-Helper Interpreter Entrypoints (`Compiler/Proofs/IRGeneration/SourceSemantics.lean`, `Compiler/Proofs/IRGeneration/IRInterpreter.lean`)**:
   - Defines `evalExprCanonical`, `execStmtCanonical`, `execStmtsCanonical` (`fuel = 0`, `helpers = []`) and `evalIRExprCanonical`, `execIRStmtCanonical`, `execIRStmtsCanonical` (`emptyInternalsIRContract`) with `@[simp]` reduction lemmas and `IRState.getVar_setVar_*` state-preservation lenses.
3. **Unified 5-Channel `StorageLoc` & `PureWordBinOp` Algebra (`SourceSemantics.lean`, `Compiler/Proofs/HelperStepProofs.lean`)**:
   - Factorizes the 20 pure binary word operators into `PureWordBinOp` (`evalPureWordBinOp_lt_evmModulus`) and unifies the 5 storage channels (`word`, `addr`, `mapWord`, `mapWord2`, `transientWord`) under a single `StorageLoc` read-over-write algebra (`StorageLoc.read_write_same`, `StorageLoc.read_write_ne`).
4. **Single-Pass `StmtFeatureMask` Catamorphism (`Compiler/CompilationModel/UsageAnalysis.lean`)**:
   - Replaces 28 separate AST traversals (`stmtTouches*`) with a single $O(|\text{AST}|)$ pass computing a `StmtFeatureMask` join-semilattice (`merge_idem`, `merge_comm`, `merge_assoc`, `stmtsFeatureMask_append`).

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


---

## 7. Next Foundational Priority: `EVMYulLean 2.0` & Autonomous Ethereum Conformance (`fractal-autoresearch`)

Before wiring the remaining end-to-end optimization passes and launching the multi-month autonomous conformance campaign, execution prioritizes the foundational modernization of [`lfglabs-dev/EVMYulLean`](../.lake/packages/evmyul) (**`EVMYulLean 2.0`**):
- Full multi-fork Ethereum specification coverage (`Shanghai`, `Cancun`, `Prague`/`Pectra` EIP-7702/2537/2935/7623, `Osaka` EIP-7951) and EIP-6780 `SELFDESTRUCT` parity across `.EVM` and `.Yul`;
- Total, stack-safe gas accounting (`0` partial `s.stack[i]!` indexing) unified across `.EVM`, `.Yul`, and `Verity.GasCostModel`;
- `BitVec 256` / `Verity.Core.Uint256` word unification, `execYulMessageCall` deduplication, `0 partial def` (`D_J`), and `turbo-lean` + `lean-native` integration;
- 5 foundational **MetaSpecs** (`DialectCommutation`, `StateLensAlgebra`, `GasMonotonicityAndTermination`, `StaticCallImmutability`, `TransactionalRollback`) cross-reviewed against the Yellow Paper, EELS, KEVM, `Consensys/evm-dafny`, and Isabelle/HOL4-EVM.

See [`docs/EVMYULLEAN_AND_CONFORMANCE_LONGTERM_PLAN.md`](EVMYULLEAN_AND_CONFORMANCE_LONGTERM_PLAN.md) for the complete `fractal-autoresearch` (`research-governor` / The Maxwell Gate) execution plan.
