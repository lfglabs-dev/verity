import Compiler.Proofs.Storage.SolidityStorage
import Compiler.Proofs.IRGeneration.SourceSemantics
import Verity.Core.Uint256

namespace Compiler.Proofs.LoopSimulation

open Compiler.Proofs.Storage

/-! # Loop simulation

This file supplies a small, semantics-independent library for reducing bounded
source loops to ordinary `List.foldl` proofs.  The loop model deliberately uses
the same `(index, remaining)` recursion as `SourceSemantics.execForEachLoop`.
Consequently clients only have to prove that one environment step is represented
by their Lean accumulator step; all iteration bookkeeping is handled here.
-/

section FoldCorrespondence

variable {State : Type} (step : State → Nat → State)

/-- Pure successful execution of a bounded `forEach`, starting at `index`. -/
def forEachFrom : State → Nat → Nat → State
  | state, _, 0 => state
  | state, index, remaining + 1 =>
      forEachFrom (step state index) (index + 1) remaining

/-- Pure successful execution of `forEach i < bound`, starting at index zero. -/
def forEach (state : State) (bound : Nat) : State :=
  forEachFrom step state 0 bound

/-- The indices visited by a bounded loop, in execution order. -/
def loopIndices (index remaining : Nat) : List Nat :=
  (List.range remaining).map (index + ·)

@[simp] theorem loopIndices_zero (index : Nat) : loopIndices index 0 = [] := rfl

theorem loopIndices_succ (index remaining : Nat) :
    loopIndices index (remaining + 1) =
      index :: loopIndices (index + 1) remaining := by
  simp [loopIndices, List.range_succ_eq_map]
  omega

/-- `forEach` execution is exactly a left fold over its increasing indices. -/
theorem forEachFrom_eq_foldl (state : State) (index remaining : Nat) :
    forEachFrom step state index remaining =
      (loopIndices index remaining).foldl step state := by
  induction remaining generalizing state index with
  | zero => rfl
  | succ remaining ih =>
      rw [forEachFrom, loopIndices_succ, List.foldl_cons]
      exact ih (step state index) (index + 1)

theorem forEach_eq_foldl (state : State) (bound : Nat) :
    forEach step state bound = (List.range bound).foldl step state := by
  rw [forEach, forEachFrom_eq_foldl]
  simp [loopIndices]

/-- The fold presentation can also be consumed in the reverse direction. -/
theorem foldl_eq_forEach (state : State) (bound : Nat) :
    (List.range bound).foldl step state = forEach step state bound :=
  (forEach_eq_foldl step state bound).symm

end FoldCorrespondence

/-! ## Index invariants -/

/-- An invariant indexed by the next loop index. -/
def IndexInvariant {State : Type} (Inv : Nat → State → Prop)
    (step : State → Nat → State) : Prop :=
  ∀ index state, Inv index state → Inv (index + 1) (step state index)

theorem forEachFrom_preserves_indexInvariant
    {State : Type} {Inv : Nat → State → Prop} {step : State → Nat → State}
    (hstep : IndexInvariant Inv step) (state : State) (index remaining : Nat)
    (hinit : Inv index state) :
    Inv (index + remaining) (forEachFrom step state index remaining) := by
  induction remaining generalizing state index with
  | zero =>
      rw [forEachFrom]
      simpa using hinit
  | succ remaining ih =>
      rw [forEachFrom]
      have hnext := hstep index state hinit
      have hfinal := ih (step state index) (index + 1) hnext
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal

theorem forEach_preserves_indexInvariant
    {State : Type} {Inv : Nat → State → Prop} {step : State → Nat → State}
    (hstep : IndexInvariant Inv step) (state : State) (bound : Nat)
    (hinit : Inv 0 state) :
    Inv bound (forEach step state bound) := by
  simpa [forEach] using
    forEachFrom_preserves_indexInvariant hstep state 0 bound hinit

/-! ## Order conservation -/

/-- Instrument a step with the exact index trace it observes. -/
def traceStep {State : Type} (step : State → Nat → State) :
    (State × List Nat) → Nat → State × List Nat :=
  fun stateAndTrace index =>
    (step stateAndTrace.1 index, stateAndTrace.2 ++ [index])

theorem forEachFrom_trace_order
    {State : Type} (step : State → Nat → State)
    (state : State) (trace : List Nat) (index remaining : Nat) :
    (forEachFrom (traceStep step) (state, trace) index remaining).2 =
      trace ++ loopIndices index remaining := by
  induction remaining generalizing state trace index with
  | zero => simp [forEachFrom, loopIndices]
  | succ remaining ih =>
      rw [forEachFrom, loopIndices_succ]
      simpa [traceStep, List.append_assoc] using
        ih (step state index) (trace ++ [index]) (index + 1)

theorem forEach_trace_order
    {State : Type} (step : State → Nat → State)
    (state : State) (bound : Nat) :
    (forEach (traceStep step) (state, []) bound).2 = List.range bound := by
  simpa [forEach, loopIndices] using
    forEachFrom_trace_order step state [] 0 bound

/-! ## Environment/accumulator simulation -/

/-- A relation connecting an executable environment with a Lean accumulator. -/
abbrev EnvAccRel (Env Acc : Type) := Env → Acc → Prop

theorem foldl_rel
    {Env Acc Index : Type}
    (Rel : EnvAccRel Env Acc)
    (envStep : Env → Index → Env) (accStep : Acc → Index → Acc)
    (hstep : ∀ env acc index, Rel env acc →
      Rel (envStep env index) (accStep acc index))
    (indices : List Index) (env : Env) (acc : Acc) (hinit : Rel env acc) :
    Rel (indices.foldl envStep env) (indices.foldl accStep acc) := by
  induction indices generalizing env acc with
  | nil => exact hinit
  | cons index rest ih =>
      exact ih (envStep env index) (accStep acc index)
        (hstep env acc index hinit)

theorem forEach_rel
    {Env Acc : Type}
    (Rel : EnvAccRel Env Acc)
    (envStep : Env → Nat → Env) (accStep : Acc → Nat → Acc)
    (hstep : ∀ env acc index, Rel env acc →
      Rel (envStep env index) (accStep acc index))
    (bound : Nat) (env : Env) (acc : Acc) (hinit : Rel env acc) :
    Rel (forEach envStep env bound) (forEach accStep acc bound) := by
  rw [forEach_eq_foldl, forEach_eq_foldl]
  exact foldl_rel Rel envStep accStep hstep (List.range bound) env acc hinit

private theorem execForEachLoop_continue_eq_forEachFrom
    (varName : String)
    (runBody : Compiler.Proofs.IRGeneration.SourceSemantics.RuntimeState →
      Compiler.Proofs.IRGeneration.SourceSemantics.StmtResult)
    (envStep : Compiler.Proofs.IRGeneration.SourceSemantics.RuntimeState → Nat →
      Compiler.Proofs.IRGeneration.SourceSemantics.RuntimeState)
    (hbody : ∀ env index,
      runBody
          { env with bindings :=
              (Compiler.Proofs.IRGeneration.SourceSemantics.bindValue env.bindings varName
                (Compiler.Proofs.IRGeneration.SourceSemantics.wordNormalize index)) } =
        .continue (envStep env index))
    (env : Compiler.Proofs.IRGeneration.SourceSemantics.RuntimeState)
    (index remaining : Nat) :
    Compiler.Proofs.IRGeneration.SourceSemantics.execForEachLoop
        varName runBody env index remaining =
      .continue (forEachFrom envStep env index remaining) := by
  induction remaining generalizing env index with
  | zero => rfl
  | succ remaining ih =>
      rw [Compiler.Proofs.IRGeneration.SourceSemantics.execForEachLoop,
        hbody, forEachFrom]
      exact ih (envStep env index) (index + 1)

/-- Bridge the pure loop simulation to `SourceSemantics.execForEachLoop` when
every body execution successfully continues.  The `hbody` premise includes the
concrete semantics' normalized loop-index binding.  Early `.stop`, `.return`,
and `.revert` results are intentionally outside this successful-continuation
lemma: `execForEachLoop` propagates each immediately, so they require a
result-aware relation rather than the total-state `forEach_rel` contract. -/
theorem forEach_rel_execForEachLoop_sound
    {Acc : Type}
    (Rel : EnvAccRel
      Compiler.Proofs.IRGeneration.SourceSemantics.RuntimeState Acc)
    (varName : String)
    (runBody : Compiler.Proofs.IRGeneration.SourceSemantics.RuntimeState →
      Compiler.Proofs.IRGeneration.SourceSemantics.StmtResult)
    (envStep : Compiler.Proofs.IRGeneration.SourceSemantics.RuntimeState → Nat →
      Compiler.Proofs.IRGeneration.SourceSemantics.RuntimeState)
    (accStep : Acc → Nat → Acc)
    (hbody : ∀ env index,
      runBody
          { env with bindings :=
              (Compiler.Proofs.IRGeneration.SourceSemantics.bindValue env.bindings varName
                (Compiler.Proofs.IRGeneration.SourceSemantics.wordNormalize index)) } =
        .continue (envStep env index))
    (hstep : ∀ env acc index, Rel env acc →
      Rel (envStep env index) (accStep acc index))
    (bound : Nat)
    (env : Compiler.Proofs.IRGeneration.SourceSemantics.RuntimeState)
    (acc : Acc) (hinit : Rel env acc) :
    Compiler.Proofs.IRGeneration.SourceSemantics.execForEachLoop
        varName runBody env 0 bound =
      .continue (forEach envStep env bound) ∧
    Rel (forEach envStep env bound) (forEach accStep acc bound) := by
  constructor
  · simpa [forEach] using
      execForEachLoop_continue_eq_forEachFrom varName runBody envStep hbody env 0 bound
  · exact forEach_rel Rel envStep accStep hstep bound env acc hinit

/-! ## UInt256 normalization -/

abbrev UInt256 := Verity.Core.Uint256

def normalizeUInt256 (n : Nat) : Nat := n % Verity.Core.Uint256.modulus

@[simp] theorem normalizeUInt256_eq_val (n : Nat) :
    normalizeUInt256 n = (Verity.Core.Uint256.ofNat n).val := rfl

@[simp] theorem normalizeUInt256_lt (n : Nat) :
    normalizeUInt256 n < Verity.Core.Uint256.modulus :=
  Nat.mod_lt n Verity.Core.Uint256.modulus_pos

@[simp] theorem normalizeUInt256_idem (n : Nat) :
    normalizeUInt256 (normalizeUInt256 n) = normalizeUInt256 n := by
  exact Nat.mod_eq_of_lt (normalizeUInt256_lt n)

theorem normalizeUInt256_eq_self {n : Nat}
    (h : n < Verity.Core.Uint256.modulus) :
    normalizeUInt256 n = n := Nat.mod_eq_of_lt h

theorem normalizeUInt256_add (a b : Nat) :
    normalizeUInt256 (a + b) =
      normalizeUInt256 (normalizeUInt256 a + normalizeUInt256 b) := by
  simp [normalizeUInt256, Nat.add_mod]

theorem normalizeUInt256_succ (n : Nat) :
    normalizeUInt256 (n + 1) =
      normalizeUInt256 (normalizeUInt256 n + 1) := by
  simpa using normalizeUInt256_add n 1

/-! ## Canonical storage-mapping iteration

These lemmas do not unfold Solidity slot computation or compiled storage
interpretation.  They consume the Phase 1D theorems as the storage boundary.
-/

def mappingWrite (contract : ContractId) (baseSlot : Nat)
    (value : Nat → Word) (key : Nat) : StorageWrite :=
  { contract := contract
    slot := mappingSlotPointer baseSlot key
    value := value key }

def iterateMappingWrites (contract : ContractId) (baseSlot : Nat)
    (value : Nat → Word) (keys : List Nat) (storage : SolidityStorage) :
    SolidityStorage :=
  keys.foldl (fun current key =>
    applyStorageWrite (mappingWrite contract baseSlot value key) current) storage

theorem iterateMappingWrites_eq_stateRewrite
    (contract : ContractId) (baseSlot : Nat) (value : Nat → Word)
    (keys : List Nat) (storage : SolidityStorage) :
    iterateMappingWrites contract baseSlot value keys storage =
      applyStateRewrite (keys.map (mappingWrite contract baseSlot value)) storage := by
  induction keys generalizing storage with
  | nil => rfl
  | cons key keys ih =>
      simp only [iterateMappingWrites, List.foldl_cons, List.map_cons,
        applyStateRewrite_cons]
      exact ih (applyStorageWrite (mappingWrite contract baseSlot value key) storage)

/-- Every iterated mapping read uses the canonical pointer certified by Phase 1D. -/
theorem mappingReadAt_of_key
    (storage : SolidityStorage) (contract scratchBase baseSlot key : Nat)
    (hkey : key < Compiler.Constants.evmModulus) :
    Option.map (storage contract)
        (compiledMappingSlotPointer
          (Compiler.CodegenCommon.mappingSlotFuncAt scratchBase)
          scratchBase baseSlot key) =
      some (storage contract (mappingSlotPointer baseSlot key)) :=
  (mappingSlot_of_key storage contract scratchBase baseSlot key hkey).1

/-- One loop iteration of the emitted mapping store is the canonical update. -/
theorem mappingIteration_compiled_eq_canonical
    (scratchBase contract baseSlot key : Nat) (value : Word)
    (storage : SolidityStorage) :
    interpretCompiledMappingSstore
        (Compiler.CodegenCommon.mappingSlotFuncAt scratchBase)
        scratchBase contract
        (.exprStmt (.call "sstore"
          [.call "mappingSlot" [.lit baseSlot, .lit key], .lit value.toNat])) storage =
      applyStorageWrite (mappingWrite contract baseSlot (fun _ => value) key) storage := by
  simpa [mappingWrite] using
    (compiledMappingSstore_eq_canonicalSstore
      scratchBase contract baseSlot key value storage).2

/-! ## Worked example: sum over an array -/

def sumStep (values : List Nat) (sum : Nat) (index : Nat) : Nat :=
  sum + values.getD index 0

theorem forEach_sum_eq_foldl_getD (values : List Nat) (initial : Nat) :
    forEach (sumStep values) initial values.length =
      (List.range values.length).foldl (sumStep values) initial :=
  forEach_eq_foldl (sumStep values) initial values.length

theorem foldl_range_getD_eq_foldl (values : List Nat) (initial : Nat) :
    (List.range values.length).foldl (sumStep values) initial =
      values.foldl (· + ·) initial := by
  have hmap :
      (List.range values.length).map (fun index => values.getD index 0) = values := by
    apply List.ext_getElem
    · simp
    · intro index hRange hValues
      simp [List.getElem?_eq_getElem hValues]
  calc
    (List.range values.length).foldl (sumStep values) initial =
        ((List.range values.length).map (fun index => values.getD index 0)).foldl
          (· + ·) initial := by
      rw [List.foldl_map]
      rfl
    _ = values.foldl (· + ·) initial := by rw [hmap]

/-- A concrete end-to-end loop proof: bounded array summation is `List.foldl`. -/
theorem forEach_sum_over_array (values : List Nat) (initial : Nat) :
    forEach (sumStep values) initial values.length =
      values.foldl (· + ·) initial := by
  rw [forEach_sum_eq_foldl_getD, foldl_range_getD_eq_foldl]

end Compiler.Proofs.LoopSimulation
