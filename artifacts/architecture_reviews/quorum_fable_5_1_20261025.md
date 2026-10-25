# Verity 2.0 / EVMYulLean 2.0 — Architecture & Formal-Assurance Review
**Model**: `anthropic/claude-fable-5-1` (Cloud Hermes Mission `604b21b9-3fef-4675-bfb4-88cddf579713` / Run `run_421501631c2244108ce9f5a8f0f282b0`)
**Date**: 2026-10-25
**Idempotency Key**: `fable-51-quorum-spec-cleanup-20261025-v1`

Scope: the fact base you provided (no repo access this turn). Everything below is derived from it; where I extrapolate, it is marked **(hypothesis)**.

---

## (A) Critical Audit of Current Specifications

### A.1 Classification grid

Legend — **Connected**: theorem's statement mentions the real artifact (AST / `Codegen.lean` / `SupportedSpec.lean` / `EvmYul.*.step`). **Detached**: proved over a model defined in the same file that nothing in the pipeline instantiates. **Tautological**: the statement is `P → P` or `h ↦ h.field`.

| Module | What is actually proved | Connected to | Status | Severity |
| --- | --- | --- | --- | ---: |
| `Specs/Common.lean` `unchangedExcept` | Parametric frame predicate over `ContractState` | `Denote.ContractState` | Connected, but 1 of 3 competing frame vocabularies | Medium |
| `Specs/Common.lean` legacy `same*Context`, `storageAddrStorage2UpdateSpec` (~400 LOC) | Pairwise frame facts | `ContractState` | Connected but **redundant**: each is a specialization of `unchangedExcept` with a 1–2 element write list | Medium (maintenance, proof-time) |
| `Specs/Composition.lean` `Footprint.{WritesOnly, AgreesOn, Disjoint}` | Footprint algebra | `ContractState` | Connected; third vocabulary; no lemma `WritesOnly w s s' ↔ unchangedExcept w s s'` is stated in the fact base **(hypothesis: absent)** | Medium |
| `Specs/ObsAlgebra.lean` `Obs`, `ObsEquiv`, `CertifiedObsAndGasRefinement` | Equivalence/refinement algebra over a record | **Nothing** — no projection `ContractState → Obs`, `Yul.State → Obs`, `EVM.State → Obs` | **Detached**. Every refinement theorem phrased on `Obs` is vacuous w.r.t. the compiler until a projection exists | **High** |
| `Specs/ObsAlgebra.lean` `solidityArrayBaseSlot`, `solidityArrayElemSlot`, `ExtendedStorageKey` | Slot arithmetic | Not tied to `SpecStorageKey.array` or to `SupportedSpec` slot emission | Detached | Medium |
| `Specs/AdversaryAndHelpers.lean` `SupportedHelperSummaryProofCatalog` | `0 < minGasStep ∧ callee.rank < topologicalRank` over a `List HelperSummaryEntry` | Not derived from the real helper call graph in `SupportedSpec.lean` | Detached: proves the *catalog* is well-founded, not that the *compiler's helper graph* is | High |
| `Specs/AdversaryAndHelpers.lean` Laws 2–5 (`hvalid.1`, `hvalid.2.1`, …) | Field projections of `ValidAdversaryStep` | None | **Tautological** (`A ∧ B ∧ C ∧ D → B`). Also, the 5-level lattice (`none | staticView | callback | lowLevel | any`) is a label, not an operational restriction: no theorem says "`staticView` steps cannot write" by appeal to `EvmYul` `STATICCALL` semantics | **High** |
| `Proofs/IRGeneration/GuardAndDynamicAbi.lean` `runNonReentrantGuarded` over `GuardedEntryState` | Guard re-entry model | Not `attachNonReentrantGuard` (`CompilationModel`) | Detached: proves a 20-line re-implementation is correct, not the function the pipeline calls | High |
| Same file, `advanceTailCursor` over `AbiArgSegment` | Head/tail size arithmetic | Not `emitEvent` / `emitRevertError` | Detached | Medium |
| `Proofs/YulGeneration/BytecodeTranslationValidation.lean` `scanValidJumpdests` | Jumpdest scan using `EvmYul.EVM.nextPcAfterOp` | `EvmYul` opcode decoder | **Connected** (the one genuinely grounded piece here) | — |
| Same file, `BytecodeBlockCert` | `cert.evmSlicePostDigest = cert.yulBlockPostDigest` on two caller-supplied `Nat` | Nothing computes the digests | **Tautological**: a cert is "valid" iff the user wrote the same number twice. Zero translation-validation content | **Critical** |
| `Autoresearch/MaxwellGasSuperoptimizer.lean` 55 `Nat` lemmas | Bitwise/arith identities (`(x &&& m1) &&& m2 = x &&& (m1 &&& m2)`) | `Nat`, not Yul AST, not `EvmYul` `AND` semantics (256-bit wrap, `UInt256`) | Detached: true lemmas about the wrong type. No theorem `evalYul (rewrite e) = evalYul e` | High |
| Same, `passGasSavings` 55-arm multiplier table | Numeric table | No connection to `EvmYul` gas schedule (`GasTermination.lean` / `YulEvmGasEquivalence.lean`) | Detached; the "savings" are asserted, not computed | Medium |
| Same, 32 `BurnedPathEntry` refutations | Counter-examples | Documentation value only | Fine, but they are data, not spec | Low |
| `Codegen/AccelPlugin.lean` `verifiedAccelTheoremAllowlist : List String` | String membership | Theorem *names* | **Unsound by construction**: a string proves nothing; renaming or sorry-ing a theorem is invisible | High |
| Same, `accelCertMetaGateSpec` (`Safe := verifyAccelCertGate false c = true`, `sound := fun _ h => h`) | `P → P` | — | **Tautological** self-specification. The gate's "soundness" theorem is `id` | **Critical** |
| `Codegen/Profile.lean` `emitYulWithProfile` | Toggles `applyTempReuseToObject` | `emitYulWithOptionsReport` | Connected, but only **1 of 55** passes exists in the active pipeline. `enableSlotCoalescingShim`, `activePlugins` are dead config | High (truthfulness of claims) |
| `EvmYul/MetaSpecs/*`, `EvmYul/Specs/*` | Dialect commutation, gas termination, state lens algebra, static-call rollback, multi-fork conformance, Yul↔EVM gas equivalence | `EvmYul` semantics (by location) | Presumably connected on the EvmYul side **(hypothesis)**, but no Verity-side theorem consumes them: no `import` chain from `Compiler/Proofs/*` to `StaticCallAndRollback` is listed | Medium |

### A.2 What this means, concretely

Fact: the proved pipeline and the active pipeline intersect at exactly two points — `unchangedExcept`-style storage specs over `Denote.ContractState`, and `scanValidJumpdests`. Everything else that *sounds* like end-to-end assurance (Obs refinement, adversary laws, guard correctness, block translation validation, 55 gas passes, accel gate) is either a model nobody instantiates or a proposition that proves itself.

Three distinct anti-patterns are present, and they need different fixes:

1. **Shadow models** (`runNonReentrantGuarded`, `advanceTailCursor`, `HelperSummaryEntry` catalog, `Nat` lemmas). Fix: state the theorem about the real function; delete the shadow or keep it only as a reference semantics with a proven `realFn = shadowFn` bridge.
2. **Self-certifying records** (`BytecodeBlockCert`, `MetaGateSpec.sound := id`, `ValidAdversaryStep` laws). Fix: the certificate must be *checked* by a function whose correctness theorem refers to an interpreter.
3. **Nominal trust** (`List String` allowlist, `activePlugins` stored-not-read, `passGasSavings` table). Fix: carry proofs as values, not names; make the pipeline fold over the same list the theorem quantifies over.

Judgment: the current TCB is not "Lean + EvmYul"; it is "Lean + EvmYul + 7,068 LOC of `SupportedSpec.lean` + every hand-written `Nat` in every cert + the honesty of whoever maintains the string allowlist".

---

## (B) #1 Priorities — Formal TCB and Performance

Ranked by (assurance gained ÷ engineering cost). Each item names the exact artifact it unblocks.

### B.1 Formal assurance

| # | Intervention | Why it's highest leverage | Cost |
| ---: | --- | --- | --- |
| 1 | **Wire `Obs` as a projection**: `HasObs ContractState`, `HasObs EvmYul.Yul.State`, `HasObs EvmYul.EVM.State`, plus `obs_step_commutes` lemmas | Turns 283 LOC of `ObsAlgebra` from vacuous to the *spine* of every refinement statement. Prerequisite for 2, 3, 5 | 1–2 weeks |
| 2 | **Replace `BytecodeBlockCert` with a checked cert**: `checkBlockCert : BasicBlock → YulBlock → Bool` that runs a symbolic EVM basic-block evaluator and a Yul block interpreter and compares `Obs`-projected post-states; theorem `checkBlockCert_sound` | Converts the only "translation validation" artifact from tautology to real evidence; leverages the already-connected `nextPcAfterOp` | 2–3 weeks |
| 3 | **Prove `attachNonReentrantGuard` directly** (`CompilationModel`), and `emitEvent`/`emitRevertError` ABI layout directly | Kills the two shadow models in `GuardAndDynamicAbi.lean`; the current proofs can likely be re-targeted with a bridge lemma rather than redone | 1 week |
| 4 | **Derive adversary laws from `StaticCallAndRollback.lean`**: `ValidAdversaryStep` becomes a *theorem* about `EvmYul.EVM.step` on `CALL/STATICCALL/DELEGATECALL`, with the capability lattice as a predicate on the call opcode + `static` flag | Replaces 4 tautologies with 4 real theorems; also connects `EvmYul/Specs` to Verity for the first time | 2 weeks |
| 5 | **Proof-carrying passes**: delete `verifiedAccelTheoremAllowlist : List String`; `activePlugins : List VerifiedPass` where `VerifiedPass` holds the soundness proof as a field. `MetaGateSpec.Safe` becomes `ObsRefines`, `sound` becomes a real theorem | Removes nominal trust; makes `Codegen.lean` fold over the same list the theorem quantifies over | 1 week + per-pass proofs |
| 6 | **Helper graph well-foundedness from the real call graph**: `helperCallGraph : SupportedSpec → Digraph`, `helperGraph_acyclic` by `decide` on the concrete contract's graph | Converts the catalog check into a fact about the compiled artifact | 3 days |
| 7 | CI gate: `#print axioms` on every top-level correctness theorem must be `{propext, Classical.choice, Quot.sound}`; fail on `sorryAx` and on any `native_decide` outside an explicit allowlist **file** (not strings in Lean) | Cheap, catches regressions of 1–6 | 1 day |

### B.2 Gas performance

Fact: 54 of the 55 passes do not run. The emitted bytecode's gas is determined by `emitYulWithOptionsReport` + `applyTempReuseToObject`. The 55 lemmas improve nothing today.

| # | Intervention | Expected effect |
| ---: | --- | --- |
| 1 | Implement passes **as Yul AST rewrites** (not `Nat` lemmas) and actually fold them in `Codegen.lean`; start with the families with the highest measured frequency in your contract corpus (mask-fusion, iszero-of-zero, dead-`sload` elision, slot coalescing) | Only route to real gas reduction. Need a measured baseline (`forge snapshot` / EvmYul interpreter gas) per pass before claiming any multiplier |
| 2 | Replace `passGasSavings` with `gasOf : YulObject → EvmYul gas schedule → Nat` computed via `YulEvmGasEquivalence.lean`; savings = `gasOf before - gasOf after`, proved per pass as `gasOf (apply o) ≤ gasOf o` | Turns asserted multipliers into theorems; also gives you a Pareto proof obligation per pass |
| 3 | Slot coalescing shim: either implement and read `enableSlotCoalescingShim`, or delete the field | Dead config is a correctness smell in a certified compiler |

### B.3 Compile / proof-check time

| # | Intervention | Why |
| ---: | --- | --- |
| 1 | **Split `SupportedSpec.lean` (7,068 LOC)** into per-construct modules (`SupportedSpec/Storage.lean`, `/Events.lean`, `/Errors.lean`, `/Calls.lean`) with an umbrella re-export | Lake parallelism is per-module; one 7k file is a serial bottleneck and forces full re-elaboration on any edit |
| 2 | Delete the 400 LOC of `same*Context` helpers after proving them as one-line corollaries of `unchangedExcept` (see C) | Fewer declarations in the `simp` set; smaller instance search space |
| 3 | Replace the 55-arm `match` on `GasOptimizationPassId` (in `passGasSavings` and anywhere `decide`/`omega` touches it) with a family-indexed structure (C, Layer 2); `cases` on 55 constructors is quadratic in `simp`/`decide` | Observed pattern: large flat enums are the #1 cause of `maxHeartbeats` blowups |
| 4 | Bitwise lemmas: move from `Nat` to `BitVec 256` and discharge with `bv_decide` (cached, fast) instead of hand proofs | Matches EVM word semantics *and* is faster |
| 5 | `set_option autoImplicit false`, explicit `simp only` sets, no `simp` with the full default set inside `SupportedSpec` proofs | Standard, but with 7k LOC it dominates |
| 6 | Precompile `EvmYul` as a pinned Lake dependency with `.olean` caching; never rebuild it in Verity CI | Elaboration of EvmYul is the fixed cost in every clean build |

---

## (C) Cleanup Blueprint — 4 Compositional Abstraction Layers

Principle: each layer exposes one type and one soundness predicate; the layer above only uses those. Nothing is a string; nothing is a caller-supplied `Nat` that stands in for a computed value.

```
L0  Semantics & Observation     Obs, HasObs, Frame            (Specs/)
L1  Verified Rewrites           Rewrite, RewriteFamily        (Compiler/Rewrites/)
L2  Verified Pipeline           VerifiedPass, Pipeline        (Compiler/Pipeline/)
L3  Backend Validation          BlockCert, AdversaryStep      (Compiler/Backend/, EvmYul bridge)
```

### Layer 0 — Semantics & Observation (`Verity/Specs/Obs.lean`, `Verity/Specs/Frame.lean`)

Replaces: `same*Context` (all), `storage*UpdateSpec`, `Footprint.{WritesOnly, AgreesOn, Disjoint}`, the detached `Obs`.

```lean
namespace Verity.Spec

/-- One canonical key type. `ExtendedStorageKey` and `SpecStorageKey` merge here;
    `array` carries the Solidity base-slot derivation so `solidityArrayElemSlot`
    is a *function on keys*, not a free-floating lemma. -/
inductive Key
  | slot    (n : UInt256)
  | addr    (base : UInt256) (a : Address)
  | map     (base : UInt256) (k : UInt256)
  | map2    (base : UInt256) (k1 k2 : UInt256)
  | array   (base : UInt256) (i : UInt256)
  | transient (n : UInt256)
  deriving DecidableEq, Repr

/-- Physical slot of a key — the only place Solidity layout arithmetic lives. -/
def Key.physSlot : Key → UInt256

/-- The single frame predicate. Every other frame statement is an abbrev or lemma. -/
def Frame (W : Finset Key) (s s' : ContractState) : Prop :=
  ∀ k, k ∉ W → s.read k = s'.read k

abbrev unchangedExcept (ws : List Key) := Frame ws.toFinset
abbrev WritesOnly (W : Finset Key) (s s') := Frame W s s'
abbrev AgreesOn (R : Finset Key) (s s' : ContractState) : Prop :=
  ∀ k ∈ R, s.read k = s'.read k
abbrev Disjoint (W R : Finset Key) : Prop := Disjoint W R   -- Finset.Disjoint

theorem Frame.trans  (h₁ : Frame W₁ s s') (h₂ : Frame W₂ s' s'') : Frame (W₁ ∪ W₂) s s''
theorem Frame.mono   (h : W ⊆ W') (hf : Frame W s s') : Frame W' s s'
theorem Frame.agrees (hd : Disjoint W R) (hf : Frame W s s') : AgreesOn R s s'

-- Legacy, kept one release as deprecated corollaries, then deleted:
@[deprecated Frame] theorem sameAddrMapContext_iff :
  sameAddrMapContext b s s' ↔ Frame {Key.addr b a | a} s s'   -- etc.

/-- Observation: now a *projection*, not a free record. -/
structure Obs where
  status     : CallStatus
  returndata : ByteArray
  logs       : List Log
  storage    : Key → UInt256
  transient  : Key → UInt256

class HasObs (σ : Type) where
  obs : σ → Obs

instance : HasObs Denote.ContractState   := ⟨fun s => { … }⟩
instance : HasObs IRInterpreter.State    := ⟨…⟩
instance : HasObs EvmYul.Yul.State       := ⟨…⟩
instance : HasObs EvmYul.EVM.State       := ⟨…⟩   -- via StateLensAlgebra lenses

def ObsEquiv (a b : Obs) : Prop := a = b          -- or ignore gas-only fields
def ObsRefines {σ τ} [HasObs σ] [HasObs τ]
    (run₁ : Input → σ) (run₂ : Input → τ) : Prop :=
  ∀ i, HasObs.obs (run₁ i) = HasObs.obs (run₂ i)

end Verity.Spec
```

Soundness anchor of L0: four `obs_step` lemmas, one per instance, e.g.
`theorem obs_evm_step : HasObs.obs (EvmYul.EVM.step s) = evmObsStep (HasObs.obs s) (s.pc …)`. These are the only places that touch raw `EvmYul` state fields.

### Layer 1 — Verified Rewrites (`Compiler/Rewrites/`)

Replaces: `GasOptimizationPassId` (`G1`…`G55`), `passGasSavings`, 55 `Nat` lemmas.

```lean
namespace Verity.Rewrite

/-- A local, side-condition-guarded AST rewrite with its proof *as a field*. -/
structure Rewrite where
  name   : String                                  -- for logs only; never trusted
  cond   : Yul.Expr → Bool                         -- decidable guard
  rhs    : Yul.Expr → Yul.Expr
  sound  : ∀ e env, cond e = true →
             Yul.evalExpr env (rhs e) = Yul.evalExpr env e
  gasLe  : ∀ e, cond e = true →
             Yul.gasExpr (rhs e) ≤ Yul.gasExpr e   -- via YulEvmGasEquivalence

/-- Families, not a flat enum. Adding a rule = appending to a list, no new constructor,
    no new arm in any table. -/
inductive Family
  | arith | bitmask | stack | storage | control | zeroElision
  deriving DecidableEq, Repr, Fintype

structure Catalog where
  rules : Family → List Rewrite

/-- Bitmask rules are proved on BitVec 256 with bv_decide, not on Nat. -/
def maskAssoc : Rewrite where
  name  := "and-and-fuse"
  cond  := fun | .call "and" [.call "and" [_, .lit _], .lit _] => true | _ => false
  rhs   := fun | .call "and" [.call "and" [x, .lit m₁], .lit m₂] =>
                   .call "and" [x, .lit (m₁ &&& m₂)] | e => e
  sound := by intro e env h; cases e <;> simp_all [Yul.evalExpr]; bv_decide
  gasLe := by …

/-- Refutations become *negative* tests of the same type: an attempted rule plus a
    witness env on which `sound` fails. They never enter `Catalog`. -/
structure Refuted where
  attempt : Yul.Expr → Yul.Expr
  env     : Yul.Env
  e       : Yul.Expr
  breaks  : Yul.evalExpr env (attempt e) ≠ Yul.evalExpr env e

end Verity.Rewrite
```

Why this removes the proof-time problem: there is no 55-way `match` anywhere; `simp`/`decide` never see a 55-constructor type; each rule's proof is local to its definition.

### Layer 2 — Verified Pipeline (`Compiler/Pipeline/`)

Replaces: `verifiedAccelTheoremAllowlist : List String`, `accelCertMetaGateSpec`, `PipelineConfig.{enableSlotCoalescingShim, activePlugins}` dead fields, the gap between `emitYulWithProfile` and the proved pipeline.

```lean
namespace Verity.Pipeline
open Verity.Spec Verity.Rewrite

/-- A whole-object pass. Soundness is observational, against the *real* object
    denotation. The proof is a field; the type system is the allowlist. -/
structure VerifiedPass where
  name  : String
  apply : Yul.Object → Yul.Object
  sound : ∀ o, ObsRefines (Yul.runObject (apply o)) (Yul.runObject o)
  gasLe : ∀ o i, Yul.gasObject (apply o) i ≤ Yul.gasObject o i

/-- Lift a rewrite family to a pass by bottom-up application. -/
def ofRewrites (rs : List Rewrite) : VerifiedPass where
  apply := Yul.Object.mapExprs (applyAll rs)
  sound := by …   -- uses Rewrite.sound + congruence lemma for mapExprs
  gasLe := by …

/-- The only config. No booleans that nothing reads. -/
structure Config where
  passes : List VerifiedPass

def run (cfg : Config) (o : Yul.Object) : Yul.Object :=
  cfg.passes.foldl (fun acc p => p.apply acc) o

theorem run_sound (cfg : Config) (o : Yul.Object) :
    ObsRefines (Yul.runObject (run cfg o)) (Yul.runObject o) := by
  induction cfg.passes generalizing o <;> simp_all [run, VerifiedPass.sound, ObsRefines]

/-- End-to-end: the theorem mentions `Codegen.emitYul`, the real entry point. -/
theorem compile_refines (c : Contract) (cfg : Config) :
    ObsRefines
      (Yul.runObject (run cfg (Codegen.emitYul c)))
      (Denote.runContract c) :=
  (run_sound cfg _).trans (Codegen.emitYul_refines c)

/-- Meta-gate with content: `sound` is no longer `id`. -/
structure MetaGate where
  Safe  : Yul.Object → Prop := fun o => ObsRefines (Yul.runObject o) (Denote.runContract c)
  check : Yul.Object → Bool
  sound : ∀ o, check o = true → Safe o

end Verity.Pipeline
```

`Codegen.lean` and `Profile.lean` then reduce to: build `Config` from the profile (`tempReuse := ofRewrites catalog.rules .stack`, etc.) and call `Pipeline.run`. `emitYulWithOptionsReport` becomes an instance of a `VerifiedPass` or is proven equal to one.

### Layer 3 — Backend Validation & Adversary (`Compiler/Backend/`, `EvmYul` bridge)

Replaces: `BytecodeBlockCert` with free `Nat` digests; `ValidAdversaryStep` + tautological Laws 2–5; the `HelperSummaryEntry` catalog.

```lean
namespace Verity.Backend
open Verity.Spec

/-- Symbolic post-state of an EVM basic block (straight-line, ends at JUMP/STOP/RETURN). -/
def evmBlockSym : EvmYul.EVM.BasicBlock → SymState → Option SymState
/-- Yul block under the same symbolic valuation. -/
def yulBlockSym : Yul.Block → SymState → Option SymState

/-- A certificate is a *claim*; validity is *computed*. -/
structure BlockCert where
  evmBlock : EvmYul.EVM.BasicBlock
  yulBlock : Yul.Block
  entry    : SymState

def checkBlockCert (c : BlockCert) : Bool :=
  decide (evmBlockSym c.evmBlock c.entry = yulBlockSym c.yulBlock c.entry)

theorem checkBlockCert_sound (c : BlockCert) (h : checkBlockCert c = true) :
    ∀ s, concretizes s c.entry →
      HasObs.obs (EvmYul.EVM.runBlock c.evmBlock s)
        = HasObs.obs (EvmYul.Yul.runBlock c.yulBlock (toYul s))
  -- proof: soundness of the two symbolic evaluators w.r.t. EvmYul.EVM.step /
  --        EvmYul.Yul.step, discharged via DialectCommutation + obs_step lemmas.

theorem jumpdests_ok (code : ByteArray) :
    scanValidJumpdests code = EvmYul.EVM.validJumpdests code    -- already-connected piece

/-- Adversary: a *theorem schema* on the real step relation, not a record of implications. -/
inductive Capability | none | staticView | callback | lowLevel | any
  deriving DecidableEq, Repr

def Capability.allows : Capability → EvmYul.EVM.CallKind → Bool

theorem callee_failure_rolls_back
    (s : EvmYul.EVM.State) (k : EvmYul.EVM.CallKind) (hk : (cap.allows k) = true)
    (hfail : (EvmYul.EVM.callResult s k).success = false) :
    HasObs.obs (EvmYul.EVM.afterCall s k) |>.storage = (HasObs.obs s).storage
  := by exact EvmYul.Specs.StaticCallAndRollback.rollback_on_failure …   -- real import

theorem staticView_no_write (hcap : cap = .staticView) … :
    (HasObs.obs (EvmYul.EVM.afterCall s k)).storage = (HasObs.obs s).storage
  := by exact EvmYul.Specs.StaticCallAndRollback.static_no_sstore …

/-- Helper termination from the real graph. -/
def helperGraph (spec : SupportedSpec) : Digraph HelperId
theorem helpers_acyclic (spec : SupportedSpec) (h : (helperGraph spec).isAcyclic = true) :
    ∀ hid, Terminates (spec.runHelper hid)
  -- per concrete contract: `by decide` on the finite graph.

end Verity.Backend
```

Laws 2–5 are now *consequences* of EvmYul lemmas. `ValidAdversaryStep` as a record can remain as a convenient packaging, but it is **constructed** by the theorems above (`⟨callee_failure_rolls_back …, staticView_no_write …, …⟩`), never assumed.

### Migration order and deletion list

| Step | Action | Deletes |
| ---: | --- | --- |
| 1 | Land L0 `Key`, `Frame`, `HasObs` + 4 instances + `obs_step` lemmas | `ExtendedStorageKey` (merged), detached `Obs` |
| 2 | Prove `same*Context ↔ Frame …` corollaries, mark `@[deprecated]`, migrate call sites in `SupportedSpec/*` | ~400 LOC of `Common.lean` after one release |
| 3 | Split `SupportedSpec.lean`; retarget guard/ABI proofs at `attachNonReentrantGuard`, `emitEvent`, `emitRevertError` | `runNonReentrantGuarded`, `advanceTailCursor` shadow models |
| 4 | Land L1 `Rewrite`/`Catalog`, port the 55 lemmas into ≤6 families on `BitVec 256` | `GasOptimizationPassId`, `passGasSavings`, 55 `Nat` lemmas |
| 5 | Land L2 `VerifiedPass`/`Config`/`run_sound`; rewire `Codegen.lean` + `Profile.lean` | `verifiedAccelTheoremAllowlist`, `accelCertMetaGateSpec`, `enableSlotCoalescingShim`, `activePlugins : List String` |
| 6 | Land L3 `checkBlockCert`, adversary theorems from `StaticCallAndRollback`, `helperGraph` | `BytecodeBlockCert` digest fields, tautological Laws 2–5, `SupportedHelperSummaryProofCatalog` |
| 7 | CI: `#print axioms` gate on `compile_refines`, `checkBlockCert_sound`, `run_sound`; forbid `sorryAx`; allowlist `native_decide` by **file**, not string | — |

### Open questions (need the code, not the fact base)

1. Does `Denote.ContractState` already have a total `read : Key → UInt256`, or are `map`/`map2`/`array` stored as separate partial maps? Determines whether `Frame` is a one-liner or needs a lens.
2. Does `EvmYul.Yul.State` expose logs/returndata in a form that projects without running the interpreter to completion? If not, `HasObs Yul.State` needs a "post-exit" refinement.
3. Does `YulEvmGasEquivalence.lean` give a *computable* `gasObject`, or only an existential bound? `VerifiedPass.gasLe` depends on which.

Résumé en une ligne : aujourd'hui, deux morceaux sont réellement prouvés sur le vrai pipeline (frames `unchangedExcept`, scan des `JUMPDEST`) ; tout le reste est modèle détaché ou tautologie. La correction consiste à faire de `Obs` une projection, à porter les preuves comme valeurs plutôt que comme noms, et à faire calculer les certificats au lieu de les déclarer.

---

## Appendix — Direct Codebase Verification & `turbo-lean --json audit-spec` Telemetry

### 1. Answers to Fable 5.1's 3 Open Questions (Verified Against Worktrees)

1. **Question 1 (`Denote.ContractState` storage representation)**:
   - `ContractState` in `Verity/Core.lean` stores six total functions/fields: `storage : Nat → Uint256`, `storageAddr : Nat → Address`, `storageMap : Nat → Address → Uint256`, `storageMapUint : Nat → Uint256 → Uint256`, `storageMap2 : Nat → Address → Address → Uint256`, `storageArray : Nat → List Uint256`, plus `transientStorage : Nat → Uint256`.
   - Note that `Verity/Specs/Composition.lean` (lines 298–334) *already* proves `WritesOnly.to_unchangedExcept` (converting `Footprint` to `List SpecStorageKey`), so merging `Footprint`, `SpecStorageKey`, and `ExtendedStorageKey` into a single `Key` / `Frame` in Layer 0 is immediate.
2. **Question 2 (`EvmYul.Yul.State` logs and returndata exposure)**:
   - In `EvmYul/MetaSpecs/DialectCommutation.lean` (lines 27–34 and 208–215), `Yul.State` wraps `SharedState .Yul`, which directly exposes `toMachineState.H_return : ByteArray` (returndata), `substate.logSeries : Array LogEntry` (logs), `storageAt y k : UInt256`, and `transientAt y k : UInt256`.
   - Furthermore, `yulOutcome` models normal `.Ok s' vs`, `.error (.YulHalt (.Ok s' vs) flag)` (`STOP`/`RETURN`), and `.error .Revert`. Thus `HasObs EvmYul.Yul.State` (and `HasObs (Except Yul.Exception Yul.State)`) is directly definable without waiting for whole-program termination.
3. **Question 3 (`YulEvmGasEquivalence.lean` computability)**:
   - `EvmYul/Specs/YulEvmGasEquivalence.lean` (line 13) defines a **computable** step cost function:
     `def yulStepTotalGas (fork : EVM.Fork) (s : Yul.State) (op : Operation .Yul) (args : List UInt256) : ℕ := yulPrimOpDynamicGas fork s op args + yulMemoryExpansionGas s op args`
     along with `consumeYulGas_seq_iff` (lines 35–94). Therefore `VerifiedPass.gasLe` can use the computable `yulStepTotalGas` / `consumeYulGas` directly.

### 2. Additional Detached Models Identified During Direct Inspection

- **`Compiler/Proofs/SlotCoalescingShim.lean`**: Proves `execCoalescedPackedWrites_eq_uncoalesced` over a standalone 3-field record `SlotStorageState` (`slotWord`, `fmp`, `otherSlotsRoot`) and `List PackedFieldWrite`. It does not transform `IRStmt` or `YulStmt` ASTs, nor is it invoked by `Codegen.lean` or `Profile.lean`.
- **`Compiler/Proofs/VerifiedECMShims.lean`**: Across the 8 ECM shim families (e.g., `shimEip712AndEcrecover` vs `denoteEip712AndEcrecover`, lines 233–284), `shimImpl` and `denoteSpec` are defined as syntactically identical pure Lean functions over standalone records (using mock linear polynomials like `eip712PrefixWord + 257 * domainSeparator + 65537 * structHash`), so `shimImpl x s = denoteSpec x s` holds by `rfl` without touching `YulStmt` emission or `EvmYul` precompile semantics.

### 3. `turbo-lean --json audit-spec` Results on the 4 New Spec Modules

Running `/var/lib/sandboxed-node/caches/elan/bin/turbo-lean --json audit-spec` across the four modules returned:
- `Verity/Specs/ObsAlgebra.lean`: `ok: true`, `total_specs_audited: 13`, `tight_specs: 13`, `vacuous_specs: 0`, `trivial_specs: 0` (`3.104 ms`)
- `Verity/Specs/AdversaryAndHelpers.lean`: `ok: true`, `total_specs_audited: 11`, `tight_specs: 11`, `vacuous_specs: 0`, `trivial_specs: 0` (`3.035 ms`)
- `Compiler/Proofs/IRGeneration/GuardAndDynamicAbi.lean`: `ok: true`, `total_specs_audited: 8`, `tight_specs: 8`, `vacuous_specs: 0`, `trivial_specs: 0` (`38.228 ms`)
- `Compiler/Proofs/YulGeneration/BytecodeTranslationValidation.lean`: `ok: true`, `total_specs_audited: 5`, `tight_specs: 5`, `vacuous_specs: 0`, `trivial_specs: 0` (`26.215 ms`)

**Key Meta-Finding on `turbo-lean audit-spec`**: Syntactic non-vacuity and tightness checks (`precondition_satisfiable` + `postcondition_discriminates`) pass 100% (37/37 tight) on detached shadow models and projection lemmas (`hvalid.1`), because `P ∧ Q → P` has a satisfiable precondition and a discriminating postcondition! This confirms why **semantic connection audits** (verifying that theorems reference the active compiler symbols `Codegen.emitYul`, `CompilationModel.compile`, `EvmYul.step`) are indispensable alongside `turbo-lean audit-spec`.
