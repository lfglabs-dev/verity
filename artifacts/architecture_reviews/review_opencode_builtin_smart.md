# Architectural & Roadmap Review — OpenCode builtin/smart (`builtin/smart`)

The remaining work is not “more features.” It is a single simulation chain that is still broken in three places: the observation algebra is too narrow, several proofs are not the relation `Codegen` actually emits, and two large trusted fronts (`Import.lean`, `solc --strict-assembly`) sit outside that chain. Close those in dependency order. Do not promote gas patches or corpus results until the chain is the one the compiler runs.

The review below treats your fact base as the current architecture. Theorem names marked **(new)** are obligations to add; names you already listed are the ones to reuse, not reinvent.

---

## 0. The chain that must become the only theorem

Every later milestone is a conjunct on one relation. Widen it **before** wiring optimizers, or every `preserves_eval` proof will be redone.

```lean
structure Obs where
  status     : ExecStatus          -- success | revert | invalid
  returndata : ByteArray
  logs       : List Log            -- address × topics[≤4] × data
  storage    : List (SpecStorageKey × UInt256)
  transient  : List (SpecStorageKey × UInt256)

def ObsEquiv (a b : Obs) : Prop := a = b
-- gas is NOT in ObsEquiv
```

Target master statement, quantified by fork and pipeline config:

```lean
theorem compile_pipeline_correct
    (fork : EvmYul.Fork) (cfg : PipelineConfig fork)
    (c : CompilationModel) (h : SupportedSpec c)
    (w : TranslationWitness c)          -- empty if c came from verity_contract
    : ObsEquiv (Denote.obs c)
               (EvmYul.EVM.obs fork (Assemble.assemble (pipeline cfg c)))
```

Decomposition, each arrow a separate lemma already mostly named in your stack:

| Arrow | Existing / target lemma | File |
|---|---|---|
| Solidity AST → `CompilationModel` | `CertifiedContractTranslationWitness` | `Compiler/SolidityImport/TranslationValidation.lean` |
| `FnSpec.Satisfies` | success post + `¬requires → revert` | `Verity/Specs/Common.lean`, `Verity/Core/Model/Denote.lean` |
| Denote → IR | `compile_preserves_semantics` | `Compiler/Proofs/IRGeneration/*`, `SupportedSpec.lean` |
| IR → canonical Yul | codegen simulation, today implicit | `Compiler/Codegen.lean` |
| Yul → Yul | `CertifiedPatchPack.preserves_eval` **(new composition)** | `Compiler/Yul/PatchFramework.lean` |
| Yul step ↔ EVM step | `MetaSpec.DialectCommutation` | `EvmYul/Semantics.lean` + MetaSpecs |
| Yul object → bytecode | `Assemble.sim` **(new)** | proposed `EvmYul/Assemble.lean` |
| Gas, side inequality | `improves_cost` under `EvmYul/Yul/GasInterpreter.lean` | not in `ObsEquiv` |

`StaticCallAndRollback`, `StateLensAlgebra`, `GasTermination`, `MessageCallSimulation` stay side lemmas of the EVM/Yul interpreters. They are not substitutes for `Obs`.

**Axiom budget.** Keep a single keccak axiom, generalized, and derive the current one:

```lean
-- proposed EvmYul/Axioms/Keccak.lean
axiom keccak256_inj_on_lt_2_256
  (a b : ByteArray)
  (ha : a.size ≤ 128) (hb : b.size ≤ 128)  -- ABI key||slot or a single word
  (hk : keccak256 a = keccak256 b) : a = b

theorem solidityMappingSlot_injective ... :=  -- existing axiom becomes a corollary
  keccak256_inj_on_lt_2_256 (key₁ ++ slot₁) (key₂ ++ slot₂) ...
```

Array bases, event topics, and error selectors must be corollaries of that same axiom. Do not add `arrayBase_injective`, `topic_inj`, etc.

**Hygiene gate on every PR:** `scripts/check_lean_hygiene.py --forbid-constructor-compat` plus `sorryAx` count stays 0. Patch proofs do not use `native_decide`. `bv_decide` is allowed only if CI shows it adds no kernel axiom; otherwise discharge `BitVec 256` identities by the lemmas already backing `EvmYul.UInt256`.

---

## PART 1 — Dependency-ordered completion

### Phase A — Observation algebra and storage-key algebra (blocks everything)

**A1. Logs and revert data become part of Denote and of every interpreter.**

`Denote.execStmt` / `execStmtList` must accumulate `logs` and `revertData`, not only `ContractState` and a success bit. `EvmYul.Yul` execution and `EvmYul.EVM` execution already have log side effects in a real EVM; thread them into the same `Obs`. `EndToEnd.lean`’s current bridge via `EvmYul.Yul.callDispatcher` has to be restated as `ObsEquiv`, or later event work (#2082) is unprovable without rewriting the bridge.

**A2. Replace the overloaded mapping-slot formula before any more frame proofs.**

Solidity layout, which SourceSemantics does not match today:

```text
mapping:     keccak256(abi.encode(key, slot))     = keccak256(pad32(key) ++ pad32(slot))
dyn array:   length at slot s
             base   = keccak256(pad32(s))
             elem i = base + i * stride           -- stride = 1 for uint256/address
bytes/string:length at s; data at keccak256(pad32(s))
```

`solidityMappingSlot s i` is the mapping formula. Using it for array elements is a real semantics bug relative to Yul, not a proof gap.

```lean
inductive SpecStorageKey
  | word (slot : UInt256)
  | addr (slot : UInt256)                       -- low 160 of a word slot
  | mapWord (slot key : UInt256)
  | mapWord2 (slot k1 k2 : UInt256)
  | arrayElem (slot : UInt256) (i stride : Nat)
  | bytesData (slot : UInt256) (byteOff : Nat)  -- derived word = base + byteOff/32
  | transientWord (slot : UInt256)

def arrayBase (s : UInt256) : UInt256 :=
  keccak256 (pad32 s)

def keyAddr : SpecStorageKey → UInt256
  | .arrayElem s i stride => arrayBase s + i * stride
  | .mapWord s k          => solidityMappingSlot s k
  ...
```

Lemmas to prove in `Verity/Specs/Common.lean` next to `unchangedExcept`:

- `keyAddr_inj` on each constructor family, array and bytes cases from `keccak256_inj_on_lt_2_256` plus `Nat` addition disjointness when `stride > 0` and indices are in range (no wrap: `arrayBase + i*stride < 2^256`, else the model reverts — do not silently wrap).
- `unchangedExcept_update_comm` for distinct `keyAddr`.
- `arrayElem_not_mapWord` so a frame that says “only this array changed” is not discharged by a mapping write.

Then change `SourceSemantics` array indexing to `keyAddr (.arrayElem s i stride)` and re-prove the storage half of `SupportedBodyInterface.state`. Until that lands, do not claim whole-contract completeness for any contract with `T[]` or `bytes`.

`StorageLoc`’s five channels (`word`, `addr`, `mapWord`, `mapWord2`, `transientWord`) stay as the lens API; `arrayElem` / `bytesData` are additional lenses with the same `get/set/get_set/set_set/get_set_diff` algebra you already have from `StateLensAlgebra`. Do not invent a second frame predicate.

---

### Phase B — Layer 2 whole-contract completeness (#1630 / #1638)

The exclusion `helperSurfaceClosed` is a negative gate. Replace it with a positive witness computed by the same catamorphism that already builds `StmtFeatureMask`.

**B1. Catalog shape.**

```lean
structure HelperSummary where
  id        : InternalId
  params    : List Ty
  rets      : List Ty
  requires  : ContractState → Prop
  ensures   : ContractState → List UInt256 → ContractState → Prop
  frame     : List SpecStorageKey          -- unchangedExcept frame
  reads     : List SpecStorageKey
  writes    : List SpecStorageKey
  mayCall   : AdversaryModel               -- Phase C; until then `.none`
  gasBound  : EvmYul.Fork → Nat → Nat      -- fuel in terms of incoming gas

structure SupportedHelperSummaryProofCatalog where
  summaries : List HelperSummary
  agree     : ∀ s ∈ summaries, IR.denote s.id = HelperSummary.denote s
  complete  : ∀ id ∈ mask.helperIds, ∃ s ∈ summaries, s.id = id
```

`UsageAnalysis.lean` already folds the AST once into `StmtFeatureMask`. Extend the mask with `helperIds : Finset InternalId` (and later `ecmIds`, `eventSigs`). One pass, no second traversal that can drift.

**B2. How `CompiledStmtStepWithHelpersAndHelperIR` consumes the catalog.**

Prove a single step lemma parameterized by the catalog, by recursion on the statement and a call context, not by “helpers are closed so they don’t appear”:

```lean
theorem compiledStmtStep
    (cat : SupportedHelperSummaryProofCatalog)
    (fuel : Nat) (st : Stmt) (σ : State)
    (hmask : maskOf st ⊆ cat.mask)
    : ObsEquiv (Denote.execStmt st σ)
               (IR.exec (compileStmt cat st) σ)
```

Cases:

| Stmt | Proof |
|---|---|
| `internalCall` / `internalCallAssign` / `Expr.internalCall` | lookup `cat.summaries id`; apply `agree`; frame rule from `unchangedExcept` on `s.frame`; substitute return words into the LHS/RHS local env |
| nested block / `if` / `for` | IH on sub-statements; `StmtFeatureMask` is a catamorphism so submasks ⊆ parent mask |
| external / low-level | deferred to Phase C `AdversaryModel`; until then the mask bit `calls.foreign` / `calls.lowLevel` still excludes them |

**Mutual recursion.** Do not induct on “the helper body contains a call to itself” structurally. Build the internal call graph, Tarjan SCCs, and:

- acyclic SCCs: topological induction, catalog entries proved before their callers;
- non-trivial SCCs: well-founded induction on `GasTermination` fuel (EVMYulLean already), with the summary’s `gasBound` strictly decreasing on the recursive edge. If a helper has no gas measure, it stays outside `SupportedSpec` — an explicit mask bit, not a global `helperSurfaceClosed`.

**B3. Retire the gate.**

```lean
theorem helperSurfaceClosed_of_catalog
    (cat : SupportedHelperSummaryProofCatalog)
    (h : mask.helperIds ⊆ cat.ids) : helperSurfaceClosed mask
```

`compile_preserves_semantics` then takes `cat` instead of `h : helperSurfaceClosed`. The old theorem is the special case `cat.summaries = [] ∧ mask.helperIds = ∅`, so existing parity proofs keep working.

`SupportedBodyInterface` decomposition (`core | state | calls.helpers | calls.foreign | calls.lowLevel | effects`) stays. Only `calls.helpers` changes from “forbidden” to “catalogued.”

---

### Phase C — `AdversaryModel` in six PRs

One inductive family, one stepper. Every other module is a view.

```lean
inductive AdversaryModel
  | none
  | staticView (iface : ABIIface)                          -- STATICCALL, no writes
  | callback   (iface : ABIIface) (pol : ReenterPolicy)
  | lowLevel   (pol : LowLevelPolicy)                      -- call/delegatecall/staticcall + raw returndata
  | any        (bound : CallBound)

structure ReenterPolicy where
  mayReenter    : Bool
  victimWrites  : List SpecStorageKey   -- slots a reentering callback may change
  extHavoc      : Bool                   -- foreign storage arbitrary
  retBound      : Nat                    -- returndata length cap
```

Laws, all in one file (proposed `Verity/Specs/Adversary.lean`), used everywhere:

1. `frame`: keys outside `victimWrites` satisfy `unchangedExcept`.
2. `static_no_write`: `staticView` and `STATICCALL` imply `victimWrites = []` and no logs from the callee that the caller did not itself emit. Caller logs still append on success only.
3. `rollback`: failed callee restores storage and transient (this is `StaticCallAndRollback` + call-frame rollback in `MessageCallCombinator.lean`).
4. `ret_bound`: returndata length ≤ bound; ABI decode past that reverts.
5. `reenter_fuel`: each reentry consumes gas; `GasTermination` bounds depth.

PR split, in order, each mergeable alone:

| PR | Change | Done when |
|---|---|---|
| C1 | Define the type and the five laws. No call-site migration. | `lake build` of Specs |
| C2 | `Contracts.Common` and macro expansion (`Verity/Macro/*`) emit `AdversaryModel` into `FnSpec`. Delete the second enum. | elaboration tests round-trip |
| C3 | `SourceSemantics` external, `call`, `delegatecall`, `staticcall` all go through `execCall model`. | `Denote.execStmt` cases for calls are one function |
| C4 | `Reentrancy.lean` and `CallbackBridge.lean` become corollaries of `frame` + `rollback` under `callback`. No private adversary. | old theorem names are `abbrev`s |
| C5 | IR lowering of calls preserves the model: `STATICCALL` iff `staticView`; `DELEGATECALL` only under `lowLevel` with `extHavoc` interpreted as callee-context storage. | `SupportedBodyInterface.calls` proof |
| C6 | `SupportedSpec.effects` stores `AdversaryModel`. Whole-contract theorem quantifies over it. | `helperSurfaceClosed` no longer mentions callbacks |

Do not start C5 before Phase A `Obs`, because a callback that emits logs is otherwise invisible.

---

### Phase D — `nonreentrant` inside `SupportedSpec`

`attachNonReentrantGuard` running **after** `compileFunctionSpec` means `FnSpec.Satisfies` never saw the lock. A reentrant adversary is then “proved safe” because the spec’s body is not the code that runs. Fix the order, not the guard.

EIP-1153 shape to elaborate **in the `CompilationModel`, before denote/compile**:

```text
if tload(lock) = ENTERED then revert else
tstore(lock, ENTERED)
body
tstore(lock, UNLOCKED)     -- skipped on revert by call-frame rollback
```

Obligations inside `SupportedSpec`, not a post-pass:

- `transientWord lock` is in the function’s write set and in `unchangedExcept` of the **external** spec on the success path (net unlock).
- On the revert path, `StaticCallAndRollback` / `MessageCallCombinator` restores the transient slot. Do not model “we clear the lock in a Solidity `finally`” unless the Yul actually has a cleanup that runs on revert; EVM revert already rolls back `TSTORE`.
- `AdversaryModel.callback` with `mayReenter = true` plus “lock is `ENTERED` during `body`” implies the reentrant entry takes the `¬requires`-style revert branch of `FnSpec.Satisfies`. That is the actual non-reentrancy theorem.
- Mask bit `effects.nonreentrant` is set by `StmtFeatureMask` when the wrapper is present, so `compile_preserves_semantics` includes it.

`VerifiedECMShims.TransientLocks` then becomes a Yul-level proof that the elaborated wrapper lowers to `TLOAD`/`TSTORE`, not a second lock semantics. Fork constraint: `transientWord` is legal only for `Fork ≥ Cancun`. Shanghai pipeline must reject the mask bit.

---

### Phase E — Dynamic events and custom errors (#2082)

One ABI encoder, two consumers (log data and revert data). Do not let events and errors grow separate offset arithmetics.

```lean
structure Log where
  emitter : Address
  topics  : Array Bytes32    -- size ≤ 4
  data    : ByteArray

structure RevertObs where
  selector : Bytes4          -- Panic / Error(string) / custom
  data     : ByteArray
```

Encoder specification (the thing `__evt_data_tail` must implement):

- Non-indexed arguments are ABI-encoded as a tuple: head at `[0:32*n)`, tails concatenated, offsets relative to the start of the encoding, not relative to free memory.
- Indexed static value: `pad32(value)` in the topic.
- Indexed `bytes`/`string`/array: topic is `keccak256(encodedContents)`, **not** the raw pointer.
- `anonymous` omits the signature topic.
- Signature topic is `keccak256(canonicalSig)` with the existing keccak axiom only if you need injectivity of selectors; equality of a concrete topic is computation, not an axiom.

Theorem, consumer of Phase A:

```lean
theorem event_obs_eq (st : Stmt) (h : st.feature.effects.events) :
    (Denote.execStmt st σ).logs = (Yul.exec (compileStmt st) σ).logs

theorem error_obs_eq ... :
    (Denote.execStmt st σ).returndata = (Yul.exec (compileStmt st) σ).returndata
```

`VerifiedECMShims.dynamicAndStructEvent` should be **the** lowering used by `Codegen`, not a side shim. Until `Codegen.lean` calls it, the shim’s proof does not apply to emitted Yul. Same rule as the patch packs in Phase F.

Panic codes stay a separate selector (`0x4e487b71`) so a bounds-check revert is not unified with a custom error in `Obs`.

---

### Phase F — Wire the standalone Layer 3 proofs into the pipeline

Today `CertifiedPatchPack`, `SlotCoalescingShim`, and `SelectorDispatchTree` are not on the path that `EndToEnd.lean` talks about, and `buildSwitch` is still linear. The 12-rule expression `foundation` pack is on the path; `StmtRule` / `BlockRule` / `ObjectRule` foundation bundles are empty. Empty bundles are the right default. Do not fill them with unproven rewrites.

**F1. Make the current compiler a config, by `rfl`, before changing behavior.**

```lean
structure PipelineConfig (fork : EvmYul.Fork) where
  expr   : CertifiedPatchPack ExprPatchRule
  stmt   : CertifiedPatchPack StmtPatchRule
  block  : CertifiedPatchPack BlockPatchRule
  object : CertifiedPatchPack ObjectPatchRule
  dispatch : DispatchMode          -- | linear | tree
  coalesce : Bool
  tempReuse : TempReuseConfig

def PipelineConfig.legacy (fork) : PipelineConfig fork where
  expr      := foundationExpr12          -- or/and/add identities already in Codegen
  stmt      := .nil
  block     := .nil
  object    := .nil
  dispatch  := .linear                   -- buildSwitch
  coalesce  := false
  tempReuse := TempReuseConfig.current   -- spill above 0x1000
```

Refactor, don’t rewrite: `Compiler/Codegen.lean` becomes `lowerIR cfg` and `Compiler/CompilationModel/Compile.lean` passes `cfg`. First PR proves

```lean
theorem legacy_eq_old_codegen (c) :
    lowerIR .legacy c = Codegen.old c := rfl
```

Parity packs stay pinned to `.legacy`. No proof is broken because the function is definitionally the same.

**F2. Patch monoid.**

```lean
structure CertifiedPatchRule (α) where
  apply        : α → α
  preserves    : ∀ x σ, Yul.ObsEquiv (eval x σ) (eval (apply x) σ)
  improves     : ∀ fork σ, GasInterpreter.used fork (apply x) σ
                           ≤ GasInterpreter.used fork x σ

def CertifiedPatchPack.fold (p : CertifiedPatchPack α) : CertifiedPatchRule α
```

Composition is a `List.foldl` congruence: `ObsEquiv` is transitive, `≤` on gas is transitive. `.nil` is the identity rule (`improves` is `≤` via `Nat.le_refl`). That is why empty stmt/block/object bundles can be wired immediately.

Apply order, fixed and part of the certificate, not confluent and not searched at compile time:

```text
lower IR → object pack → dispatch (linear|tree) → block pack
        → slot coalesce (if cfg.coalesce) → stmt pack → expr pack → tempReuse
```

Each stage’s output is the next stage’s input. The certificate is the chain of `preserves` proofs for **this** `cfg`, stored beside the Yul object. Equality saturation is a search procedure in Phase 4 of Part 2; it is not the semantics.

**F3. `SelectorDispatchTree`.**

`Compiler/Selector.lean` is already the algorithm: a balanced BST on the `uint32` selector. The missing lemma is equivalence to linear `buildSwitch`, under a compile-time side condition you can decide:

```lean
theorem dispatchTree_eq_linear
    (fs : List (Selector × Yul.Block))
    (huniq : fs.pairwise (·.fst ≠ ·.fst))
    (hsorted : Sorted (·.fst < ·.fst) fs) :
    Yul.ObsEquiv (eval (buildSwitch fs)) (eval (buildTree fs))
```

Proof: induction on `fs`. At each node the pivot comparison (`LT`/`EQ`/`GT` on clean 32-bit values) partitions the list the same way a linear chain of `EQ`/`JUMPI` does. Dirty high bits must be masked once at the dispatcher entry (`and sel 0xffffffff`); both strategies share that prefix so the mask is not a behavioral difference.

`Codegen` selects `.tree` only when `huniq` is proved by the function-table construction (duplicate selectors are already a compile error). Default remains `.linear` until this lemma is in the `legacy_eq` successor config `PipelineConfig.dispatchTree`.

**F4. `SlotCoalescingShim` — alias rules, or it is unsound.**

Intra-block `SLOAD` CSE and packed `SSTORE` fusion are valid only under a local alias analysis. Encode the side conditions in the certificate, not in comments.

CSE of `SLOAD k` may reuse a previous value only if, between the two sites, none of the following occur:

- `SSTORE` to a key with `keyAddr` equal to `k` (Phase A injectivity);
- `CALL` / `DELEGATECALL` / `CALLCODE` whose `AdversaryModel` has `k ∈ victimWrites` or `extHavoc` (a `STATICCALL` does not invalidate);
- another Yul block that is a join from a path that stored `k` (so **intra-block, no join** unless both paths have the same abstract value);
- `MSTORE` is irrelevant to storage CSE. Do not let the storage lattice share state with the memory lattice.

Packed subfield fusion, one slot, disjoint bit ranges:

```text
mask_i  = ((1 << width_i) - 1) << shift_i
ranges pairwise disjoint and ⊆ 0..255
fused store =
  (old & ~fold(or, mask_i)) | fold(or, (val_i << shift_i) & mask_i)
```

Lemma: for each field `i`, `extract(fused, shift_i, width_i) = val_i` and for bits outside all masks, `fused` equals `old`. That is `BitVec` algebra on `EvmYul.UInt256`, plus the frame lemma that no other key changes.

**Across `if`:** coalesce a slot at the join only if the abstract value on both branches is the same `BitVec` expression (both wrote the same fused word, or neither wrote). Otherwise reload. Path-sensitive lattice, finite because the block is finite: forward analysis, meet at join is intersection of known equalities.

Wire as `cfg.coalesce := true` only in a new pipeline id. `PipelineConfig.legacy` keeps `false`, so parity is untouched.

**F5. Temp reuse stays where it is, but its gas proof must use the interpreter.**

`TempReuse.lean` / `TempReuseSoundness.lean` already argue dead-temporary reuse and spills above `0x1000`. Semantic preservation can stay. Gas dominance cannot be an opcode count: a spill into a higher memory word pays quadratic memory expansion in `EvmYul/EVM/Gas.lean`. Phase G makes that obligation real. Until then, do not claim `improves_cost` for spilling.

---

### Phase G — One gas semantics

`Verity.Autoresearch.GasCostModel` must become a theorem about `EvmYul/Yul/GasInterpreter.lean`, not a parallel table. The interpreter is already parameterized by `Fork` (`Shanghai`, `Cancun`, `Prague`, `Osaka`) and the schedule you listed (2929, 1153, 6780, 7702, 2537, 2935, 7623, 7951, plus 3855 `PUSH0` and 5656 `MCOPY`).

```lean
def cost (fork : Fork) (y : Yul.Stmt) (σ : State) : Nat :=
  GasInterpreter.used fork y σ

theorem autoresearch_cost_eq (fork) (y) (σ)
    (h : y ∈ VerityYulSubset) :
    GasCostModel.cost y σ = cost fork y σ
```

If the arena needs a fast abstract model, it may **over-approximate** cost (`abs ≥ cost`) and a patch is accepted only when `abs(fork, y') ≤ cost(fork, y)` implies the concrete inequality. An abstract model that under-approximates is unsound for `improves_cost`.

Fork-index every certificate. A `MCOPY` or `TSTORE` patch is `improves_cost Cancun` (and later), and is **rejected** on `Shanghai`, not “gas improved” in the abstract. EIP-2929 warmth is part of `State`: deleting a cold `SLOAD` changes the access set seen by a later `SSTORE`. The interpreter already threads that; a peephole that ignores the access list will lie by about 2000 gas. Refunds: the quantity to minimize is the gas charged to the caller at the end of `MessageCallCombinator` (used minus refund, clamped by the refund cap), not the sum of opcode base costs.

`GasTermination` is the well-founded measure for Phase B recursion and for “the optimizer did not introduce a loop.” A patch that adds a backward jump is outside the pack language unless it comes with a decreasing variant.

---

### Phase H — `BridgedSafeStmts` for whole programs

`EndToEnd.lean` connects `BridgedSafeStmts` to `EvmYul.Yul.callDispatcher`. Extend the bridge object, do not add a second end-to-end theorem.

```lean
structure LinkWitness where
  table   : List (InternalId × Yul.Function)
  ecms    : List (ECMId × ECMSummary)
  resolve : ∀ id ∈ mask.helperIds,
              lookup table id = some (compileHelper id)
  ecmOk   : ∀ e ∈ mask.ecmIds,
              ∃ s ∈ ecms, s.id = e ∧ s.preservesObs
  bridge  : BridgedSafeStmts (link table ecms program)
```

`resolve` is the Phase B catalog, read at the Yul level: the dispatcher’s leaf for `id` is definitionally the body `agree` already related to `HelperSummary`.

`Stmt.ecm` stops being opaque by requiring each ECM to be one of the eight families in `Compiler/Proofs/VerifiedECMShims.lean` (`eip712AndEcrecover`, `create2AndSstore2`, `dynamicAndStructEvent`, `yulOutlinedHelper`, `Math512`, `ScratchHashing`, `SafeTokenCalls`, `TransientLocks`), each with a summary in `Obs` form. An unrecognized assembly block is an uncertified import (Part 2), not a hole in `LinkWitness`.

`callDispatcher` then satisfies:

```lean
theorem link_obs (w : LinkWitness) (σ) :
    ObsEquiv (Denote.obs program σ)
             (EvmYul.Yul.obs (callDispatcher w.bridge) σ)
```

by composing `compile_preserves_semantics`, `compiledStmtStep`, and `ecmOk`.

---

### Phase I — `solc --strict-assembly` leaves the TCB

`DialectCommutation` (`step .Yul ↔ step .EVM`) is an interpreter theorem. It does **not** say solc’s assembler is correct. Treating it as that is the remaining TCB bug.

Build a verified assembler for the Yul **subset Verity emits**, not for all of Yul.

Proposed `EvmYul/Assemble.lean`:

```lean
def assemble : Yul.Object → Bytecode    -- JUMPDEST layout, PUSHn immediates, data section

theorem assemble_sim (fork) (y : Yul.Object) (h : y ∈ VerityYulSubset) (σ) :
    ObsEquiv (EvmYul.Yul.obs fork y σ)
             (EvmYul.EVM.obs fork (assemble y) σ)
```

`assemble_sim` is proved by induction on the subset, appealing to `DialectCommutation` per opcode and to a jump-table lemma: every `JUMP`/`JUMPI` immediate produced by `assemble` is a `JUMPDEST` in the image, and the destination’s Yul label is the one `buildSwitch` / `buildTree` named. Subobjects (`datasize` / `dataoffset` / `datacopy`, used by `create2AndSstore2`) are a later increment: until they are in the subset, those ECMs stay interpreted at Yul, not claimed at bytecode.

Practical sequence:

1. Straight-line arithmetic, `MLOAD`/`MSTORE`, `SLOAD`/`SSTORE`, `TLOAD`/`TSTORE`, `LOG0`–`LOG4`, `REVERT`/`RETURN`.
2. Internal jumps for the dispatcher and for outlined helpers (`yulOutlinedHelper`).
3. `CALL` family, matching `MessageCallCombinator`.
4. Object linking and auxdata. Verity bytecode should **not** append solc CBOR metadata; it is not part of semantics. Diffs against solc strip metadata before compare (Part 2).

After `assemble_sim`, the master theorem instantiates `compile_pipeline_correct` with `Assemble.assemble`. `solc --strict-assembly` remains a differential oracle only. A bytecode blob that solc produced is certified only if it is **equal** to `assemble y` (translation validation by syntactic equality of the subset) or if you re-prove `assemble_sim` for that blob, which you will not do per contract.

---

### Phase J — `Import.lean` leaves the TCB by witnesses, not by shrinking the 15.7k file

`Compiler/SolidityImport/Import.lean` can stay large. It becomes an untrusted parser whose output is accepted only with a `CertifiedContractTranslationWitness` (`TranslationValidation.lean`, `SolcoreBridge`).

The witness is per entrypoint, not one global proof of 15.7k lines:

```lean
structure CertifiedContractTranslationWitness where
  solcVersion : SolcPin                         -- 0.8.10 | 0.8.26 | 0.8.34
  layout      : storageLayoutJSON = model.layout
  selectors   : ∀ f, model.selector f = keccak4 (canonicalSig f)
  body        : ∀ f, Solcore.denote f = Denote.obs (model.fn f)
  roundtrip   : parse (EmitVerity.emit model) = model   -- modulo name hygiene
```

`body` is the only hard conjunct. Generate it, don’t write it:

1. `EmitVerity.lean` / `EmitVerityBridge.lean` already print a `verity_contract`. Parsing that text back must be definitionally the model (`roundtrip`). That removes pretty-printing from the TCB.
2. For each Solidity function, the importer emits a Lean file `Cert/<metadataHash>/<fn>.lean` containing the witness goal and a proof script that is `rfl` / structural recursion where the translation is a fold, plus calls to the Phase B–E lemmas where it is not.
3. `lake build` of that file is the certificate. Failure **demotes** the contract to “imported, uncertified.” It does not block the corpus, and it does not enter `compile_pipeline_correct`.
4. `Differential.lean` (`Denote.execStmtList` vs `CompilationModel.compile`) stays a test, not a witness. Tests do not remove TCB.

What “automate on every import” means operationally: `verity import Foo.sol --certify` writes those goals; CI builds only the certificates for entrypoints you claim. `Import.lean` is no longer a trusted premise of any theorem that carries a witness. Contracts without a witness are absent from the master statement.

`InlineAssemblyShims.lean` is the pressure valve: each idiom either becomes a named ECM in Phase H with a proof, or it blocks certification of that function. 100% (38/38) `PoolManager` coverage is a coverage number, not a witness. Re-certify those functions under Phase J before advertising them as verified.

---

### Phase order (one line)

A (Obs + real array slots) → B (helper catalog, drop `helperSurfaceClosed`) → C (adversary, 6 PRs) → D (nonreentrant inside the spec) → E (events/errors on the shared encoder) → F1 (legacy pipeline by `rfl`) → G (gas = `GasInterpreter`) → F2–F5 (tree, coalesce, packs) → H (link witness) → I (assembler) → J (import witnesses).

Part 2 starts at F1+G for measurement, and may ingest the corpus in parallel with A–E, but **no** gas patch is promoted, and **no** solc discrepancy is called a solc bug, before A, G, and J are in place for that contract.

---

## PART 2 — Corpus, differential oracle, certified gas, solc bugs

### 1. Ingestion

Pin everything by solc metadata hash (`ipfs` / `bzzr1` content id inside the CBOR auxdata). The address is not the identity; the metadata hash plus the compiler settings are.

**Sources, in the order that keeps the TCB honest:**

| Tier | What | Gate |
|---|---|---|
| 0 | In-repo Verity contracts and the existing Uniswap v4 `PoolManager` import | must already build |
| 1 | Sourcify `full_match` for a fixed chain list | runtime bytecode equals replay of `solc --standard-json` after metadata strip |
| 2 | Protocol repos at a pinned commit: Uniswap v2/v3/v4, Aave v3, Morpho Blue, Maker/Sky, Curve, Balancer, Lido, EigenLayer, Pendle, OZ, Solady, Solmate, Seaport, ERC-4337 `EntryPoint` | `forge build` with the repo’s own `foundry.toml` (`solc`, `via_ir`, optimizer runs, `evm_version`) reproduces the artifact the project commits |
| 3 | Sourcify `partial_match` and Etherscan verified sources | never certified; differential only if compilation reproduces on-chain code |

Use the published APIs (Sourcify, Etherscan verified-source). Do not treat a decompiled bytecode as Solidity.

**Settings that must be part of the cache key:** solc version, `optimizer.enabled`, `optimizer.runs`, `viaIR`, `evmVersion`, libraries (address link), metadata bytecode hash. A “Uniswap build” without `runs=200` vs `runs=
