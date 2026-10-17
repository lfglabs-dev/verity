import Verity.Core.Model.Denote
import Compiler.SolidityImport.AbiEncoding
import Compiler.SolidityImport.Proofs
import Compiler.SolidityImport.LoopInvariants

namespace Compiler.CompilationModel.Denote
open Compiler.CompilationModel.PhysicalMemory
open Compiler.CompilationModel.DenoteMemory

/-- Complete actual store poststate, without assuming a coherent entry world. -/
theorem execStmt_mstore_physical (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (offset value : Expr) (address word : Nat)
    (resolvedOffset : evalExpr oracle fields state offset = some address)
    (resolvedValue : evalExpr oracle fields state value = some word) :
    execStmt oracle fields state (.mstore offset value) =
      .continue { state with world := state.world.writePhysicalMemoryValue address word } := by
  simp only [execStmt, resolvedOffset, resolvedValue]

/-- Store expansion and every non-memory observation are retained by this frame. -/
theorem execStmt_mstore_physical_frame (oracle : DenoteOracle) (fields : List Field)
    (before after : DenoteState) (offset value : Expr) (address word : Nat)
    (resolvedOffset : evalExpr oracle fields before offset = some address)
    (resolvedValue : evalExpr oracle fields before value = some word)
    (executed : execStmt oracle fields before (.mstore offset value) = .continue after) :
    { after with world := after.world.installPhysicalMemory Memory.empty } =
      { before with world := before.world.installPhysicalMemory Memory.empty } := by
  rw [execStmt_mstore_physical oracle fields before offset value address word
    resolvedOffset resolvedValue] at executed
  cases executed
  rfl

/-- The byte frame does not discard writes to overlapping word windows. -/
theorem execStmt_mstore_physical_byte_frame (oracle : DenoteOracle) (fields : List Field)
    (before after : DenoteState) (offset value : Expr) (address word query : Nat)
    (resolvedOffset : evalExpr oracle fields before offset = some address)
    (resolvedValue : evalExpr oracle fields before value = some word)
    (executed : execStmt oracle fields before (.mstore offset value) = .continue after)
    (outside : query < address ∨ address + 32 ≤ query) :
    after.world.physicalByte query = before.world.physicalByte query := by
  rw [execStmt_mstore_physical oracle fields before offset value address word
    resolvedOffset resolvedValue] at executed
  cases executed
  exact writePhysicalMemoryValue_byte_outside before.world address _ query outside

/-- Actual clearing poststate, including bytes, all overlapping word windows,
expansion and the entire non-memory world. No aligned-entry assumption. -/
def abiClearPhysicalWorld (world : Verity.ContractState) (base : Nat) :
    Nat → Verity.ContractState
  | 0 => world
  | count + 1 => (abiClearPhysicalWorld world base count).writePhysicalMemoryValue
      (base + 32 * count) (Verity.Core.Uint256.ofNat 0)

@[simp] theorem abiClearPhysicalWorld_zero (world : Verity.ContractState) (base : Nat) :
    abiClearPhysicalWorld world base 0 = world := rfl

theorem abiClearPhysicalWorld_prefix (world : Verity.ContractState) (base count : Nat) :
    PhysicalZeroPrefix world (abiClearPhysicalWorld world base count) base count := by
  induction count with
  | zero =>
      intro query
      have empty : ¬ (base ≤ query ∧ query < base + 32 * 0) := by omega
      simp only [abiClearPhysicalWorld, if_neg empty]
  | succ count ih => exact physicalZeroPrefix_step world _ base count ih

theorem abiClearPhysicalWorld_byte (world : Verity.ContractState) (base count query : Nat) :
    (abiClearPhysicalWorld world base count).physicalByte query =
      if base ≤ query ∧ query < base + 32 * count then zeroByte else world.physicalByte query :=
  abiClearPhysicalWorld_prefix world base count query

theorem abiClearPhysicalWorld_frame (world : Verity.ContractState) (base count : Nat) :
    (abiClearPhysicalWorld world base count).installPhysicalMemory Memory.empty =
      world.installPhysicalMemory Memory.empty := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (abiClearPhysicalWorld world base count).installPhysicalMemory Memory.empty = _
      exact ih

theorem execStmt_zeroWord_physical (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (initial : Verity.ContractState) (address : Expr) (base count : Nat)
    (evaluated : evalExpr oracle fields state address = some (base + 32 * count))
    (cleared : state.world = abiClearPhysicalWorld initial base count) :
    execStmt oracle fields state (.mstore address (.literal 0)) =
      .continue { state with world := abiClearPhysicalWorld initial base (count + 1) } := by
  rw [execStmt_mstore_physical oracle fields state address (.literal 0)
    (base + 32 * count) 0 evaluated (by rfl)]
  simp only [cleared, abiClearPhysicalWorld]

end Compiler.CompilationModel.Denote

namespace Compiler.CompilationModel.Denote
private theorem evalPhysicalAddBounded (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (left right : Expr) (a b : Nat)
    (leftEval : evalExpr oracle fields state left = some a)
    (rightEval : evalExpr oracle fields state right = some b)
    (bounded : a + b < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.add left right) = some (a + b) := by
  have aBound : a < Verity.Core.Uint256.modulus := by omega
  have bBound : b < Verity.Core.Uint256.modulus := by omega
  rw [evalExpr, leftEval, rightEval]
  change some (((a % Verity.Core.Uint256.modulus) +
    (b % Verity.Core.Uint256.modulus)) % Verity.Core.Uint256.modulus) = _
  rw [Nat.mod_eq_of_lt aBound, Nat.mod_eq_of_lt bBound, Nat.mod_eq_of_lt bounded]

private theorem evalPhysicalWordStride (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (indexExpr : Expr) (index : Nat)
    (evaluated : evalExpr oracle fields state indexExpr = some index)
    (bounded : 32 * index < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.mul indexExpr (.literal 32)) = some (32 * index) := by
  have indexBound : index < Verity.Core.Uint256.modulus := by omega
  simp only [evalExpr, evaluated]
  change some (((index % Verity.Core.Uint256.modulus) * 32) % Verity.Core.Uint256.modulus) = _
  rw [Nat.mod_eq_of_lt indexBound, Nat.mul_comm index 32, Nat.mod_eq_of_lt bounded]

/-- The emitted zero-word body installs the full physical clearing state. -/
theorem execStmt_zeroWordBody_physical (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (initial : Verity.ContractState)
    (baseName indexName : String) (base index : Nat)
    (baseEval : lookupValue state.bindings baseName = base)
    (indexEval : lookupValue state.bindings indexName = index)
    (bounded : base + 32 * index < Verity.Core.Uint256.modulus)
    (cleared : state.world = abiClearPhysicalWorld initial base index) :
    execStmt oracle fields state (.mstore
      (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)) =
      .continue { state with world := abiClearPhysicalWorld initial base (index + 1) } := by
  apply execStmt_zeroWord_physical oracle fields state initial _ base index _ cleared
  apply evalPhysicalAddBounded oracle fields state (.localVar baseName)
    (.mul (.localVar indexName) (.literal 32)) base (32 * index) (congrArg some baseEval)
  · exact evalPhysicalWordStride oracle fields state (.localVar indexName) index
      (congrArg some indexEval) (by omega)
  · exact bounded

/-- Loop invariant records the entire physical world, not a word-map projection. -/
def AbiPhysicalClearInvariant (initial : Verity.ContractState) (baseName : String)
    (base count : Nat) (state : DenoteState) : Prop :=
  lookupValue state.bindings baseName = base ∧
    state.world = abiClearPhysicalWorld initial base count

/-- Actual emitted bounded clearing loop. No alignment/coherence assumptions,
no accepted early exits; every non-memory world component is preserved. -/
theorem execForEachLoop_clear_physical (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName indexName : String) (base count : Nat)
    (held : lookupValue state.bindings baseName = base) (fresh : indexName ≠ baseName)
    (bounded : base + 32 * count < Verity.Core.Uint256.modulus) :
    ∃ after, execForEachLoop indexName (fun s => execStmtList oracle fields s
        [.mstore (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)])
      state 0 count = .continue after ∧
      AbiPhysicalClearInvariant state.world baseName base count after := by
  have step : ∀ index before, index < count →
      AbiPhysicalClearInvariant state.world baseName base index before →
      LoopOutcomePost (AbiPhysicalClearInvariant state.world baseName base (index + 1)) (fun _ => False)
        (execStmtList oracle fields
          { before with bindings := bindValue before.bindings indexName (wordNormalize index) }
          [.mstore (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)]) := by
    intro index before inside invariant
    have indexBound : index < Verity.Core.Uint256.modulus := by omega
    have baseEval : lookupValue (bindValue before.bindings indexName (wordNormalize index)) baseName = base := by
      rw [SolidityImport.lookup_bind_other _ _ _ _ fresh]
      exact invariant.1
    have indexEval : lookupValue (bindValue before.bindings indexName (wordNormalize index)) indexName = index := by
      rw [SolidityImport.lookup_bind_same]
      change index % Verity.Core.Uint256.modulus = index
      exact Nat.mod_eq_of_lt indexBound
    have store := execStmt_zeroWordBody_physical oracle fields
      { before with bindings := bindValue before.bindings indexName (wordNormalize index) }
      state.world baseName indexName base index baseEval indexEval (by omega) invariant.2
    simp only [execStmtList, store]
    exact ⟨baseEval, rfl⟩
  have result := execForEachLoop_bounded_invariant indexName
    (fun s => execStmtList oracle fields s
      [.mstore (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)])
    count (AbiPhysicalClearInvariant state.world baseName base) (fun _ => False)
    step count 0 state (by omega) ⟨held, rfl⟩
  simp only [Nat.zero_add] at result
  cases actual : execForEachLoop indexName (fun s => execStmtList oracle fields s
      [.mstore (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)])
      state 0 count with
  | «continue» after => exact ⟨after, rfl, by simpa only [actual, LoopOutcomePost] using result⟩
  | stop after => simp only [actual, LoopOutcomePost] at result
  | «return» value after => simp only [actual, LoopOutcomePost] at result
  | revert => simp only [actual, LoopOutcomePost] at result
  | revertWithData bytes => simp only [actual, LoopOutcomePost] at result
  | interpretationError message => simp only [actual, LoopOutcomePost] at result
  | exceptional after => simp only [actual, LoopOutcomePost] at result

/-- Complete actual forEach clearing statement, including its initial index
binding. Count evaluation and all range checks remain explicit obligations. -/
theorem execStmt_clearWords_physical (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName indexName : String) (countExpr : Expr)
    (base count : Nat)
    (evaluated : evalExpr oracle fields state countExpr = some count)
    (held : lookupValue state.bindings baseName = base) (fresh : indexName ≠ baseName)
    (bounded : base + 32 * count < Verity.Core.Uint256.modulus) :
    ∃ after, execStmt oracle fields state (.forEach indexName countExpr
        [.mstore (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)]) =
      .continue after ∧ AbiPhysicalClearInvariant state.world baseName base count after := by
  have initialBase : lookupValue (bindValue state.bindings indexName (wordNormalize 0)) baseName = base := by
    rw [SolidityImport.lookup_bind_other _ _ _ _ fresh]
    exact held
  obtain ⟨after, actual, invariant⟩ := execForEachLoop_clear_physical oracle fields
    { state with bindings := bindValue state.bindings indexName (wordNormalize 0) }
    baseName indexName base count initialBase fresh bounded
  refine ⟨after, ?_, invariant⟩
  simp only [execStmt, evaluated]
  exact actual


end Compiler.CompilationModel.Denote

namespace Compiler.CompilationModel.Denote

theorem abiPhysicalRoundedSize_bounds (size : Nat) :
    size ≤ 32 * ((size + 31) / 32) ∧ 32 * ((size + 31) / 32) < size + 32 := by
  omega

/-- Actual generated word count, with the rounding addition checked not to wrap. -/
private theorem evalPhysicalRoundedCount (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (sizeExpr : Expr) (size : Nat)
    (evaluated : evalExpr oracle fields state sizeExpr = some size)
    (bounded : size + 31 < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.div (.add sizeExpr (.literal 31)) (.literal 32)) =
      some ((size + 31) / 32) := by
  have added := evalPhysicalAddBounded oracle fields state sizeExpr (.literal 31) size 31
    evaluated (by rfl) bounded
  rw [evalExpr, added]
  change some (((size + 31) % Verity.Core.Uint256.modulus / 32) % Verity.Core.Uint256.modulus) = _
  have quotient : (size + 31) / 32 < Verity.Core.Uint256.modulus :=
    lt_of_le_of_lt (Nat.div_le_self _ _) bounded
  rw [Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt quotient]

/-- Actual generated rounded byte allocation, with every coercion accounted for. -/
private theorem evalPhysicalRoundedSize (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (sizeExpr : Expr) (size : Nat)
    (evaluated : evalExpr oracle fields state sizeExpr = some size)
    (bounded : size + 31 < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state
      (.mul (.div (.add sizeExpr (.literal 31)) (.literal 32)) (.literal 32)) =
        some (32 * ((size + 31) / 32)) := by
  apply evalPhysicalWordStride oracle fields state _ _
    (evalPhysicalRoundedCount oracle fields state sizeExpr size evaluated bounded)
  have := (abiPhysicalRoundedSize_bounds size).2
  omega


/-- Exact reserve prefix, including the actual physical free-pointer write and
all overlapping word windows, bytes, expansion, and non-memory state. -/
theorem execStmtList_reserve_physical (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName endName : String) (sizeExpr : Expr) (base size : Nat)
    (pointer : (state.world.memory 64).val = base) (distinct : endName ≠ baseName)
    (sizeEval : evalExpr oracle fields
      { state with bindings := bindValue state.bindings baseName base } sizeExpr = some size)
    (bounded : base + size ≤ 2^64 - 1) :
    execStmtList oracle fields state (SolidityImport.AbiEncoding.reserve baseName endName sizeExpr) =
      .continue { state with
        bindings := bindValue (bindValue state.bindings baseName base) endName (base + size)
        world := state.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat (base + size)) } := by
  have read : evalExpr oracle fields state (.mload (.literal 64)) = some base := by
    change some (state.world.memory 64).val = some base
    rw [pointer]
  have wordBound : base + size < Verity.Core.Uint256.modulus := by
    have : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
    omega
  have sum := evalPhysicalAddBounded oracle fields
    { state with bindings := bindValue state.bindings baseName base }
    (.localVar baseName) sizeExpr base size
    (by simp [evalExpr, SolidityImport.lookup_bind_same]) sizeEval wordBound
  unfold SolidityImport.AbiEncoding.reserve
  rw [SolidityImport.exec_let_cons, read]
  simp only
  rw [SolidityImport.exec_let_cons, sum]
  simp only
  simp [execStmtList, execStmt, evalExpr, SolidityImport.lookup_bind_same,
    SolidityImport.lookup_bind_other, distinct, boolWord, wordNormalize,
    Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    bounded]


/-- Exact complete packed allocation world, without an alignment assumption.
Pointer writes overlapping the allocated slice are retained in their real order. -/
theorem execStmtList_packedBuffer_physical (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName endName indexName sizeName : String) (base size : Nat)
    (pointer : (state.world.memory 64).val = base)
    (sizeValue : lookupValue state.bindings sizeName = size)
    (distinct : endName ≠ baseName) (baseFresh : baseName ≠ sizeName)
    (endFresh : endName ≠ sizeName) (indexFresh : indexName ≠ baseName)
    (bounded : base + 32 * ((size + 31) / 32) ≤ 2^64 - 1) :
    ∃ after, execStmtList oracle fields state
      (SolidityImport.AbiEncoding.packedBuffer baseName endName indexName (.localVar sizeName)) =
        .continue after ∧ lookupValue after.bindings baseName = base ∧
      after.world = abiClearPhysicalWorld
        (state.world.writePhysicalMemoryValue 64
          (Verity.Core.Uint256.ofNat (base + 32 * ((size + 31) / 32))))
        base ((size + 31) / 32) := by
  let count := (size + 31) / 32
  let reserved : DenoteState := { state with
    bindings := bindValue (bindValue state.bindings baseName base) endName (base + 32 * count)
    world := state.world.writePhysicalMemoryValue 64
      (Verity.Core.Uint256.ofNat (base + 32 * count)) }
  have sizeBound : size + 31 < Verity.Core.Uint256.modulus := by
    have := (abiPhysicalRoundedSize_bounds size).1
    have : 2^64 + 31 < Verity.Core.Uint256.modulus := by decide
    omega
  have sizeAfterBase : evalExpr oracle fields
      { state with bindings := bindValue state.bindings baseName base } (.localVar sizeName) = some size := by
    simp [evalExpr, SolidityImport.lookup_bind_other, baseFresh, sizeValue]
  have allocation := execStmtList_reserve_physical oracle fields state baseName endName
    (.mul (.div (.add (.localVar sizeName) (.literal 31)) (.literal 32)) (.literal 32)) base
    (32 * count) pointer distinct
    (evalPhysicalRoundedSize oracle fields _ _ size sizeAfterBase sizeBound) bounded
  have sizeAfter : evalExpr oracle fields reserved (.localVar sizeName) = some size := by
    simp [reserved, evalExpr, SolidityImport.lookup_bind_other, endFresh, baseFresh, sizeValue]
  have baseAfter : lookupValue reserved.bindings baseName = base := by
    simp [reserved, SolidityImport.lookup_bind_other, SolidityImport.lookup_bind_same, distinct]
  have wordBound : base + 32 * count < Verity.Core.Uint256.modulus := by
    have : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
    omega
  obtain ⟨after, cleared, result⟩ := execStmt_clearWords_physical oracle fields reserved baseName indexName
    _ base count (evalPhysicalRoundedCount oracle fields reserved _ size sizeAfter sizeBound)
    baseAfter indexFresh wordBound
  refine ⟨after, ?_, result.1, result.2⟩
  unfold SolidityImport.AbiEncoding.packedBuffer
  rw [SolidityImport.exec_append, allocation]
  exact (SolidityImport.exec_singleton oracle fields reserved _).trans cleared


end Compiler.CompilationModel.Denote

namespace Compiler.CompilationModel.Denote
open Compiler.CompilationModel.PhysicalMemory
open Compiler.CompilationModel.DenoteMemory

theorem execStmtList_reserve_oversized_physical (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName endName : String) (sizeExpr : Expr) (base size : Nat)
    (pointer : (state.world.memory 64).val = base)
    (sizeEval : evalExpr oracle fields
      { state with bindings := bindValue state.bindings baseName base } sizeExpr = some size)
    (wordBound : base + size < Verity.Core.Uint256.modulus)
    (oversized : 2^64 - 1 < base + size) :
    execStmtList oracle fields state (SolidityImport.AbiEncoding.reserve baseName endName sizeExpr) =
      .revertWithData (panicBytes 0x41) := by
  have read : evalExpr oracle fields state (.mload (.literal 64)) = some base := by
    change some (state.world.memory 64).val = some base
    rw [pointer]
  have sum := evalPhysicalAddBounded oracle fields
    { state with bindings := bindValue state.bindings baseName base }
    (.localVar baseName) sizeExpr base size
    (by simp [evalExpr, SolidityImport.lookup_bind_same]) sizeEval wordBound
  unfold SolidityImport.AbiEncoding.reserve
  rw [SolidityImport.exec_let_cons, read]
  simp only
  rw [SolidityImport.exec_let_cons, sum]
  simp only
  have rejected : ¬ base + size ≤ 2^64 - 1 := by omega
  simp [execStmtList, execStmt, evalExpr, SolidityImport.lookup_bind_same,
    boolWord, wordNormalize, Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS, rejected]

theorem abiPhysicalReserve_wrapBelow (base size : Nat)
    (baseBound : base < Verity.Core.Uint256.modulus)
    (sizeBound : size < Verity.Core.Uint256.modulus)
    (wrapped : Verity.Core.Uint256.modulus ≤ base + size) :
    (base + size) % Verity.Core.Uint256.modulus < base := by
  rw [Nat.mod_eq_sub_mod wrapped]
  have remainder : base + size - Verity.Core.Uint256.modulus < Verity.Core.Uint256.modulus := by omega
  rw [Nat.mod_eq_of_lt remainder]
  omega

/-- The wrapped-addition allocation case is rejected with exact panic bytes. -/
theorem execStmtList_reserve_wrapped_physical (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName endName : String) (sizeExpr : Expr) (base size : Nat)
    (pointer : (state.world.memory 64).val = base) (distinct : endName ≠ baseName)
    (sizeEval : evalExpr oracle fields
      { state with bindings := bindValue state.bindings baseName base } sizeExpr = some size)
    (sizeBound : size < Verity.Core.Uint256.modulus)
    (wrapped : Verity.Core.Uint256.modulus ≤ base + size) :
    execStmtList oracle fields state (SolidityImport.AbiEncoding.reserve baseName endName sizeExpr) =
      .revertWithData (panicBytes 0x41) := by
  have baseBound : base < Verity.Core.Uint256.modulus := pointer ▸ (state.world.memory 64).isLt
  have below := abiPhysicalReserve_wrapBelow base size baseBound sizeBound wrapped
  have rejected : ¬ base ≤ (base + size) % Verity.Core.Uint256.modulus := by omega
  have read : evalExpr oracle fields state (.mload (.literal 64)) = some base := by
    change some (state.world.memory 64).val = some base
    rw [pointer]
  have sum : evalExpr oracle fields
      { state with bindings := bindValue state.bindings baseName base } (.add (.localVar baseName) sizeExpr) =
        some ((base + size) % Verity.Core.Uint256.modulus) := by
    simp only [evalExpr, SolidityImport.lookup_bind_same, sizeEval]
    change some (((base % Verity.Core.Uint256.modulus) + (size % Verity.Core.Uint256.modulus)) %
      Verity.Core.Uint256.modulus) = _
    rw [Nat.mod_eq_of_lt baseBound, Nat.mod_eq_of_lt sizeBound]
  unfold SolidityImport.AbiEncoding.reserve
  rw [SolidityImport.exec_let_cons, read]
  simp only
  rw [SolidityImport.exec_let_cons, sum]
  simp only
  by_cases limit : (base + size) % Verity.Core.Uint256.modulus ≤ 2^64 - 1 <;>
    simp only [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] at limit rejected <;>
    simp [execStmtList, execStmt, evalExpr, SolidityImport.lookup_bind_same,
      SolidityImport.lookup_bind_other, distinct, boolWord, wordNormalize,
      Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
      limit, rejected]

/-- Physical payload and padding are cleared, the complete world is retained,
and all bytes outside the rounded allocation keep their initial values. -/
theorem execStmt_clearPackedBytes_physical (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName indexName : String) (sizeExpr : Expr) (base size : Nat)
    (sizeEval : evalExpr oracle fields state sizeExpr = some size)
    (held : lookupValue state.bindings baseName = base) (fresh : indexName ≠ baseName)
    (sizeBound : size + 31 < Verity.Core.Uint256.modulus)
    (allocationBound : base + 32 * ((size + 31) / 32) < Verity.Core.Uint256.modulus) :
    ∃ after, execStmt oracle fields state
      (.forEach indexName (.div (.add sizeExpr (.literal 31)) (.literal 32))
        [.mstore (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)]) =
        .continue after ∧
      after.world = abiClearPhysicalWorld state.world base ((size + 31) / 32) ∧
      lookupValue after.bindings baseName = base ∧
      (∀ index, index < size → (after.world.physicalByte (base + index)).val = 0) ∧
      (∀ address, address < base ∨ base + 32 * ((size + 31) / 32) ≤ address →
        after.world.physicalByte address = state.world.physicalByte address) := by
  obtain ⟨after, executed, result⟩ := execStmt_clearWords_physical oracle fields state
    baseName indexName _ base ((size + 31) / 32)
    (evalPhysicalRoundedCount oracle fields state sizeExpr size sizeEval sizeBound)
    held fresh allocationBound
  refine ⟨after, executed, result.2, result.1, ?_, ?_⟩
  · intro index inside
    have rounded := (abiPhysicalRoundedSize_bounds size).1
    rw [result.2, abiClearPhysicalWorld_byte, if_pos (by omega)]
    rfl
  · intro address outside
    rw [result.2, abiClearPhysicalWorld_byte, if_neg (by omega)]

end Compiler.CompilationModel.Denote

namespace Compiler.CompilationModel.Denote
open Compiler.CompilationModel.PhysicalMemory

/-- Clearing retains an existing coherent projection, including the empty case. -/
theorem abiClearPhysicalWorld_coherent (world : Verity.ContractState)
    (coherent : Coherent world) (base count : Nat) :
    Coherent (abiClearPhysicalWorld world base count) := by
  cases count with
  | zero => exact coherent
  | succ count => exact writePhysicalMemoryValue_coherent _ _ _

/-- The actual allocator establishes the representation invariant consumed
by byte copying, without imposing it on the caller's initial world. The exact
physical poststate and base binding remain part of the conclusion. -/
theorem execStmtList_packedBuffer_coherent (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName endName indexName sizeName : String) (base size : Nat)
    (pointer : (state.world.memory 64).val = base)
    (sizeValue : lookupValue state.bindings sizeName = size)
    (distinct : endName ≠ baseName) (baseFresh : baseName ≠ sizeName)
    (endFresh : endName ≠ sizeName) (indexFresh : indexName ≠ baseName)
    (bounded : base + 32 * ((size + 31) / 32) ≤ 2^64 - 1) :
    ∃ after, execStmtList oracle fields state
      (SolidityImport.AbiEncoding.packedBuffer baseName endName indexName (.localVar sizeName)) =
        .continue after ∧ lookupValue after.bindings baseName = base ∧
      after.world = abiClearPhysicalWorld
        (state.world.writePhysicalMemoryValue 64
          (Verity.Core.Uint256.ofNat (base + 32 * ((size + 31) / 32))))
        base ((size + 31) / 32) ∧ Coherent after.world := by
  obtain ⟨after, executed, held, post⟩ := execStmtList_packedBuffer_physical oracle fields
    state baseName endName indexName sizeName base size pointer sizeValue
    distinct baseFresh endFresh indexFresh bounded
  refine ⟨after, executed, held, post, ?_⟩
  rw [post]
  exact abiClearPhysicalWorld_coherent _ (writePhysicalMemoryValue_coherent _ _ _) _ _

end Compiler.CompilationModel.Denote
