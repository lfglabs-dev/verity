import Contracts.SolidityImportSmoke.ImportedCreationDecoderElementPrelude

namespace Contracts.SolidityImportSmoke.ImportedCreationDecoderArrayLoop
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration
open ImportedCreationDecoderElementPrelude

def indexed (state : DenoteState) (index : Nat) : DenoteState :=
  { state with bindings := bindValue state.bindings "_verity_slice_tmp_0_array3_element_index" (wordNormalize index) }
def runElements (state : DenoteState) (data array free : Nat) : Nat → DenoteState
  | 0 => indexed state 0
  | count + 1 => iteration (indexed (runElements state data array free count) count)
      (data + count * 128) (free + count * 128) array count

theorem binding_frame (state : DenoteState) (data array free count : Nat) (key : String)
    (notIndex : "_verity_slice_tmp_0_array3_element_index" ≠ key)
    (notSource : "_verity_slice_tmp_0_array3_element_source" ≠ key)
    (notElement : "_verity_slice_tmp_0_array3_element_element" ≠ key)
    (notNext : "_verity_slice_tmp_0_array3_element_next" ≠ key) :
    lookupValue (runElements state data array free count).bindings key = lookupValue state.bindings key := by
  induction count with
  | zero => exact SolidityImport.lookup_bind_other _ _ _ _ notIndex
  | succ count ih =>
      rw [runElements, iteration_binding _ _ _ _ _ _ notSource notElement notNext]
      exact (SolidityImport.lookup_bind_other _ _ _ _ notIndex).trans ih

theorem input_word (state : DenoteState) (data array free count query : Nat) :
    ImportedCalldataWord.word (runElements state data array free count) query = ImportedCalldataWord.word state query := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [runElements, iteration_input_word]
      exact ih

theorem input_size (state : DenoteState) (data array free count : Nat) :
    (runElements state data array free count).world.calldataSize = state.world.calldataSize := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [runElements, iteration_size]
      exact ih

/-- The real allocator grows by128 each time, including exact count-zero behavior. -/
theorem free_pointer (state : DenoteState) (data array free count : Nat)
    (initial : (state.world.memory 64).val = free) (pastArray : 64 ≤ array) (pastFree : 96 ≤ free)
    (budget : free + count * 128 ≤ 2^64 - 1) :
    ((runElements state data array free count).world.memory 64).val = free + count * 128 := by
  cases count with
  | zero => simpa only [runElements, indexed, Nat.zero_mul, Nat.add_zero] using initial
  | succ count =>
      have actual := iteration_pointer (indexed (runElements state data array free count) count)
        (data + count * 128) (free + count * 128) array count (by omega) (by omega)
      change ((iteration _ _ _ _ _).world.memory 64).val = _
      rw [actual]
      have small : free + count * 128 + 128 < Verity.Core.Uint256.modulus := by
        have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
        omega
      rw [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt small]
      omega

/-- A live iteration derives its pointer, descriptors and canonical words from
original loop-entry state; no successful-body outcome is assumed. -/
theorem body_step (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (data array free total index : Nat)
    (dataHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_data" = data)
    (arrayHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_memory" = array)
    (initial : (state.world.memory 64).val = free)
    (pastArray : 64 ≤ array) (pastFree : 96 ≤ free)
    (available : data + total * 128 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit)
    (budget : free + total * 128 ≤ 2^64 - 1)
    (cells : array + 32 + total * 32 < Verity.Core.Uint256.modulus)
    (canonical : ∀ i < total, ImportedCalldataWord.word state (data + i * 128) < 2^160 ∧
      ImportedCalldataWord.word state (data + i * 128 + 96) < 2^160)
    (live : index < total) :
    execStmtList oracle fields (indexed (runElements state data array free index) index) body =
      .continue (runElements state data array free (index + 1)) := by
  have small : index < Verity.Core.Uint256.modulus := by
    have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
    omega
  have heldData := binding_frame state data array free index "_verity_slice_tmp_0_array3_data"
    (by decide) (by decide) (by decide) (by decide)
  have heldArray := binding_frame state data array free index "_verity_slice_tmp_0_array3_memory"
    (by decide) (by decide) (by decide) (by decide)
  have pointer := free_pointer state data array free index initial pastArray pastFree (by omega)
  have execution := execute_body oracle fields (indexed (runElements state data array free index) index)
    data array index (free + index * 128)
    (by simpa only [indexed, SolidityImport.lookup_bind_other _ "_verity_slice_tmp_0_array3_element_index" "_verity_slice_tmp_0_array3_data" _ (by decide), heldData] using dataHeld)
    (by simpa only [indexed, SolidityImport.lookup_bind_other _ "_verity_slice_tmp_0_array3_element_index" "_verity_slice_tmp_0_array3_memory" _ (by decide), heldArray] using arrayHeld)
    (by simp only [indexed, SolidityImport.lookup_bind_same, wordNormalize, Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt small])
    pointer (by simpa only [indexed, input_size] using (show data + index * 128 + 128 ≤ state.world.calldataSize.val by omega))
    (by simpa only [indexed, input_size] using sizeBound) (by omega) (by omega)
    (by change ImportedCalldataWord.word (runElements state data array free index) _ < _; rw [input_word]; exact (canonical index live).1)
    (by change ImportedCalldataWord.word (runElements state data array free index) _ < _; rw [input_word]; exact (canonical index live).2)
  exact execution

/-- Execute every remaining real iteration by induction over the interpreter loop. -/
theorem run_loop (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (data array free total : Nat)
    (dataHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_data" = data)
    (arrayHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_memory" = array)
    (initial : (state.world.memory 64).val = free) (pastArray : 64 ≤ array) (pastFree : 96 ≤ free)
    (available : data + total * 128 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit)
    (budget : free + total * 128 ≤ 2^64 - 1)
    (cells : array + 32 + total * 32 < Verity.Core.Uint256.modulus)
    (canonical : ∀ i < total, ImportedCalldataWord.word state (data + i * 128) < 2^160 ∧
      ImportedCalldataWord.word state (data + i * 128 + 96) < 2^160)
    (remaining index : Nat) (bounded : index + remaining ≤ total) :
    execForEachLoop "_verity_slice_tmp_0_array3_element_index"
      (fun current => execStmtList oracle fields current body)
      (runElements state data array free index) index remaining =
      .continue (runElements state data array free (index + remaining)) := by
  induction remaining generalizing index with
  | zero => rfl
  | succ remaining ih =>
      rw [execForEachLoop]
      have step := body_step oracle fields state data array free total index dataHeld arrayHeld initial
        pastArray pastFree available sizeBound budget cells canonical (by omega)
      unfold indexed at step
      rw [step]
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (index + 1) (by omega)

def statement : Stmt := .forEach "_verity_slice_tmp_0_array3_element_index"
  (.localVar "_verity_slice_tmp_0_array3_length") body

theorem actual_statement :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body[28]?) = some (some statement) := by rfl

/-- Execute actual complete decoder loop28, including zero elements. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (data array free total : Nat)
    (dataHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_data" = data)
    (arrayHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_memory" = array)
    (countHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_length" = total)
    (initial : (state.world.memory 64).val = free) (pastArray : 64 ≤ array) (pastFree : 96 ≤ free)
    (available : data + total * 128 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit)
    (budget : free + total * 128 ≤ 2^64 - 1)
    (cells : array + 32 + total * 32 < Verity.Core.Uint256.modulus)
    (canonical : ∀ i < total, ImportedCalldataWord.word state (data + i * 128) < 2^160 ∧
      ImportedCalldataWord.word state (data + i * 128 + 96) < 2^160) :
    execStmt oracle fields state statement = .continue (runElements state data array free total) := by
  have executed := run_loop oracle fields state data array free total dataHeld arrayHeld initial
    pastArray pastFree available sizeBound budget cells canonical total 0 (by omega)
  simp only [statement, execStmt, evalExpr, countHeld]
  change execForEachLoop "_verity_slice_tmp_0_array3_element_index"
    (fun current => execStmtList oracle fields current body) (runElements state data array free 0) 0 total = _
  simpa only [Nat.zero_add] using executed

/-- Coherence is preserved for any number of real element allocations/stores. -/
theorem coherent (state : DenoteState) (data array free count : Nat) (initial : Coherent state.world) :
    Coherent (runElements state data array free count).world := by
  cases count with
  | zero => exact initial
  | succ count => exact iteration_coherent _ _ _ _ _

/-- Every byte outside allocator, complete pointer array and element region is preserved. -/
theorem byte_frame (state : DenoteState) (data array free count query : Nat)
    (outsidePointer : query < 64 ∨ 96 ≤ query)
    (outsideCells : query < array + 32 ∨ array + 32 + count * 32 ≤ query)
    (outsideElements : query < free ∨ free + count * 128 ≤ query) :
    (runElements state data array free count).world.physicalByte query = state.world.physicalByte query := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [runElements, iteration_frame _ _ _ _ _ _ outsidePointer (by omega) (by omega)]
      exact ih (by omega) (by omega)

/-- Every cell retains its actual allocated struct pointer across later iterations. -/
theorem pointer_cell_byte (state : DenoteState) (data array free count index : Nat) (lane : Fin 32)
    (pastArray : 64 ≤ array) (separated : array + 32 + count * 32 ≤ free) (live : index < count) :
    (runElements state data array free count).world.physicalByte (array + 32 + index * 32 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (free + index * 128)) lane := by
  induction count with
  | zero => omega
  | succ count ih =>
      by_cases last : index = count
      · subst index
        exact iteration_cell_byte _ _ _ _ _ lane (by omega)
      · have old : index < count := by omega
        have small := lane.isLt
        rw [runElements, iteration_frame _ _ _ _ _ _ (Or.inr (by omega))
          (Or.inl (by omega)) (Or.inl (by omega))]
        exact ih (by omega) old

/-- Pointer-word observations follow from all32 real bytes and coherent memory. -/
theorem pointer_cell_word (state : DenoteState) (data array free count index : Nat)
    (initial : Coherent state.world) (pastArray : 64 ≤ array)
    (separated : array + 32 + count * 32 ≤ free) (live : index < count) :
    (runElements state data array free count).world.memory (array + 32 + index * 32) =
      Verity.Core.Uint256.ofNat (free + index * 128) := by
  let cell := array + 32 + index * 32
  let value := Verity.Core.Uint256.ofNat (free + index * 128)
  have equality := ImportedAbiArray.word_of_bytes
    (state.world.writePhysicalMemoryValue cell value) (runElements state data array free count).world cell
    (writePhysicalMemoryValue_coherent _ _ _) (coherent state data array free count initial) (by
      intro lane
      rw [writePhysicalMemoryValue_byte_at]
      exact pointer_cell_byte state data array free count index lane pastArray separated live)
  exact equality.trans (writePhysicalMemoryValue_at _ _ _)

/-- All four actual element fields derive their bytes from iteration-entry calldata. -/
theorem iteration_byte (state : DenoteState) (source element array index offset : Nat) (lane : Fin 32)
    (valid : offset = 0 ∨ offset = 32 ∨ offset = 64 ∨ offset = 96) :
    (iteration state source element array index).world.physicalByte (element + offset + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (source + offset))) lane := by
  rcases valid with rfl | rfl | rfl | rfl
  · rw [iteration, ImportedCreationDecoderElementFields.bytes0, ImportedCreationDecoderElementPrelude.input_word]
  · rw [iteration, ImportedCreationDecoderElementFields.bytes32, ImportedCreationDecoderElementPrelude.input_word]
  · rw [iteration, ImportedCreationDecoderElementFields.bytes64, ImportedCreationDecoderElementPrelude.input_word]
  · rw [iteration, ImportedCreationDecoderElementFields.bytes96, ImportedCreationDecoderElementPrelude.input_word]

/-- EVERY original calldata field byte survives all subsequent actual loop writes. -/
theorem element_byte (state : DenoteState) (data array free count index offset : Nat) (lane : Fin 32)
    (pastFree : 96 ≤ free) (separated : array + 32 + count * 32 ≤ free) (live : index < count)
    (valid : offset = 0 ∨ offset = 32 ∨ offset = 64 ∨ offset = 96) :
    (runElements state data array free count).world.physicalByte (free + index * 128 + offset + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (data + index * 128 + offset))) lane := by
  induction count with
  | zero => omega
  | succ count ih =>
      by_cases last : index = count
      · subst index
        rw [runElements, iteration_byte _ _ _ _ _ _ lane valid]
        change valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word
          (runElements state data array free count) (data + count * 128 + offset))) lane = _
        rw [input_word]
      · have old : index < count := by omega
        have small := lane.isLt
        have offsetBound : offset ≤ 96 := by omega
        rw [runElements, iteration_frame _ _ _ _ _ _ (Or.inr (by omega))
          (Or.inr (by omega)) (Or.inl (by omega))]
        exact ih (by omega) old

end Contracts.SolidityImportSmoke.ImportedCreationDecoderArrayLoop
