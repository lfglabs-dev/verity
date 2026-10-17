import Contracts.SolidityImportSmoke.ImportedCreationDecoderElementFields

namespace Contracts.SolidityImportSmoke.ImportedCreationDecoderElementPrelude
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration

abbrev indexExpr : Expr := .localVar "_verity_slice_tmp_0_array3_element_index"
abbrev sourceExpr : Expr := .add (.localVar "_verity_slice_tmp_0_array3_data") (.mul indexExpr (.literal 128))
abbrev cellExpr : Expr := .add (.add (.localVar "_verity_slice_tmp_0_array3_memory") (.literal 32)) (.mul indexExpr (.literal 32))
def sourced (state : DenoteState) (source : Nat) : DenoteState :=
  { state with bindings := bindValue state.bindings "_verity_slice_tmp_0_array3_element_source" source }
def allocated (state : DenoteState) (source element : Nat) : DenoteState :=
  { (sourced state source) with
    bindings := bindValue (bindValue (sourced state source).bindings
      "_verity_slice_tmp_0_array3_element_element" element) "_verity_slice_tmp_0_array3_element_next" (element + 128)
    world := state.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat (element + 128)) }
def completed (state : DenoteState) (source element array index : Nat) : DenoteState :=
  { (allocated state source element) with
    world := (allocated state source element).world.writePhysicalMemoryValue
      (array + 32 + index * 32) (Verity.Core.Uint256.ofNat element) }

def sourceSegment : List Stmt :=
  [.letVar "_verity_slice_tmp_0_array3_element_source" sourceExpr,
   SolidityImport.AbiLowering.guard (.logicalNot (.slt
     (.sub .calldatasize (.localVar "_verity_slice_tmp_0_array3_element_source")) (.literal 128)))]
def reservation : List Stmt := SolidityImport.AbiEncoding.reserve
  "_verity_slice_tmp_0_array3_element_element" "_verity_slice_tmp_0_array3_element_next" (.literal 128)
def pointerStore : Stmt := .mstore cellExpr (.localVar "_verity_slice_tmp_0_array3_element_element")
def segment : List Stmt := sourceSegment ++ reservation ++ [pointerStore]

theorem actual_segment : ImportedCreationDecoderElementFields.actualLoopBody.take 8 = segment := by rfl

/-- The actual live index determines the calldata element address. -/
theorem source_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (data index : Nat)
    (dataHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_data" = data)
    (indexHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_element_index" = index)
    (bound : data + index * 128 < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state sourceExpr = some (data + index * 128) := by
  have multiplied := ImportedAbiBounds.mul_evaluated oracle fields state indexExpr (.literal 128) index 128
    (by simp only [evalExpr, indexHeld]) (by rfl) (by omega) (by decide) (by omega)
  exact ImportedAbiWordBinding.add_evaluated oracle fields state _ _ data (index * 128)
    (by simp only [evalExpr, dataHeld]) multiplied bound

/-- Execute the real source binding and 128-byte remaining-input guard. -/
theorem execute_source (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (data index : Nat)
    (dataHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_data" = data)
    (indexHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_element_index" = index)
    (available : data + index * 128 + 128 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit) :
    execStmtList oracle fields state sourceSegment = .continue (sourced state (data + index * 128)) := by
  have ceiling : Verity.Core.Int256.signBit < Verity.Core.Uint256.modulus := Verity.Core.Int256.signBit_lt_modulus
  have source := source_evaluated oracle fields state data index dataHeld indexHeld (by omega)
  have guarded := ImportedAbiTupleHead.remaining_evaluated oracle fields (sourced state (data + index * 128))
    (.localVar "_verity_slice_tmp_0_array3_element_source") (data + index * 128) 128
    (by simp [evalExpr, sourced]) available sizeBound
  rw [sourceSegment, SolidityImport.exec_let_cons, source]
  change execStmtList oracle fields (sourced state (data + index * 128)) [_] = _
  rw [ImportedAbiTupleHead.guard_cons oracle fields _ _ [] guarded]
  rfl

/-- The actual five-instruction allocator advances free memory by128. -/
theorem execute_reservation (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source element : Nat) (pointer : (state.world.memory 64).val = element)
    (budget : element + 128 ≤ 2^64 - 1) :
    execStmtList oracle fields (sourced state source) reservation = .continue (allocated state source element) := by
  exact execStmtList_reserve_physical oracle fields (sourced state source)
    "_verity_slice_tmp_0_array3_element_element" "_verity_slice_tmp_0_array3_element_next"
    (.literal 128) element 128 pointer (by decide) (by rfl) budget

/-- Resolve the actual pointer-array destination without wrap at either add. -/
theorem cell_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (array index : Nat)
    (arrayHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_memory" = array)
    (indexHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_element_index" = index)
    (bound : array + 32 + index * 32 < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state cellExpr = some (array + 32 + index * 32) := by
  have base := ImportedAbiWordBinding.add_evaluated oracle fields state
    (.localVar "_verity_slice_tmp_0_array3_memory") (.literal 32) array 32
    (by simp only [evalExpr, arrayHeld]) (by rfl) (by omega)
  have offset := ImportedAbiBounds.mul_evaluated oracle fields state indexExpr (.literal 32) index 32
    (by simp only [evalExpr, indexHeld]) (by rfl) (by omega) (by decide) (by omega)
  exact ImportedAbiWordBinding.add_evaluated oracle fields state _ _ (array + 32) (index * 32) base offset bound

/-- Real allocator bindings cannot overwrite the array or live-index descriptor. -/
theorem allocated_binding (state : DenoteState) (source element : Nat) (key : String)
    (notSource : "_verity_slice_tmp_0_array3_element_source" ≠ key)
    (notElement : "_verity_slice_tmp_0_array3_element_element" ≠ key)
    (notNext : "_verity_slice_tmp_0_array3_element_next" ≠ key) :
    lookupValue (allocated state source element).bindings key = lookupValue state.bindings key := by
  change lookupValue (bindValue (bindValue (bindValue state.bindings
    "_verity_slice_tmp_0_array3_element_source" source) "_verity_slice_tmp_0_array3_element_element" element)
    "_verity_slice_tmp_0_array3_element_next" (element + 128)) key = _
  rw [SolidityImport.lookup_bind_other _ _ _ _ notNext,
    SolidityImport.lookup_bind_other _ _ _ _ notElement,
    SolidityImport.lookup_bind_other _ _ _ _ notSource]

/-- Entire actual eight-instruction prefix, including the pointer-cell write. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (data array index element : Nat)
    (dataHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_data" = data)
    (arrayHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_memory" = array)
    (indexHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_element_index" = index)
    (pointer : (state.world.memory 64).val = element)
    (available : data + index * 128 + 128 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit)
    (budget : element + 128 ≤ 2^64 - 1)
    (cellBound : array + 32 + index * 32 < Verity.Core.Uint256.modulus) :
    execStmtList oracle fields state segment = .continue (completed state (data + index * 128) element array index) := by
  have first := execute_source oracle fields state data index dataHeld indexHeld available sizeBound
  have second := execute_reservation oracle fields state (data + index * 128) element pointer budget
  have arrayNow := (allocated_binding state (data + index * 128) element
    "_verity_slice_tmp_0_array3_memory" (by decide) (by decide) (by decide)).trans arrayHeld
  have indexNow := (allocated_binding state (data + index * 128) element
    "_verity_slice_tmp_0_array3_element_index" (by decide) (by decide) (by decide)).trans indexHeld
  have third := execStmt_mstore_physical oracle fields (allocated state (data + index * 128) element)
    cellExpr (.localVar "_verity_slice_tmp_0_array3_element_element") (array + 32 + index * 32) element
    (cell_evaluated oracle fields _ array index arrayNow indexNow cellBound)
    (by simp [evalExpr, allocated, SolidityImport.lookup_bind_other])
  rw [segment, SolidityImport.exec_append, SolidityImport.exec_append, first]
  change (match execStmtList oracle fields (sourced state (data + index * 128)) reservation with
    | .continue next => execStmtList oracle fields next [pointerStore]
    | outcome => outcome) = _
  rw [second]
  exact (SolidityImport.exec_singleton oracle fields _ _).trans third

theorem input_word (state : DenoteState) (source element array index query : Nat) :
    ImportedCalldataWord.word (completed state source element array index) query =
      ImportedCalldataWord.word state query := by rfl

theorem descriptors (state : DenoteState) (source element array index : Nat) :
    lookupValue (completed state source element array index).bindings "_verity_slice_tmp_0_array3_element_source" = source ∧
    lookupValue (completed state source element array index).bindings "_verity_slice_tmp_0_array3_element_element" = element := by
  simp [completed, allocated, sourced, SolidityImport.lookup_bind_other]

theorem coherent (state : DenoteState) (source element array index : Nat) :
    Coherent (completed state source element array index).world := writePhysicalMemoryValue_coherent _ _ _

/-- Both writes preserve every byte outside allocator and pointer-cell words. -/
theorem byte_frame (state : DenoteState) (source element array index query : Nat)
    (outsidePointer : query < 64 ∨ 96 ≤ query)
    (outsideCell : query < array + 32 + index * 32 ∨ array + 64 + index * 32 ≤ query) :
    (completed state source element array index).world.physicalByte query = state.world.physicalByte query := by
  rw [completed, writePhysicalMemoryValue_byte_outside _ _ _ _ (by omega)]
  exact writePhysicalMemoryValue_byte_outside _ _ _ _ outsidePointer

/-- The pointer-cell write cannot clobber the allocator below a real array. -/
theorem free_pointer (state : DenoteState) (source element array index : Nat)
    (pastPointer : 96 ≤ array + 32 + index * 32) :
    (completed state source element array index).world.memory 64 = Verity.Core.Uint256.ofNat (element + 128) := by
  change ((state.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat (element + 128))).writePhysicalMemoryWord
    (array + 32 + index * 32) (valueWord (Verity.Core.Uint256.ofNat element))).memory 64 = _
  rw [writePhysicalMemoryWord_outside _ _ _ _ (writePhysicalMemoryValue_coherent _ _ _) (Or.inl pastPointer)]
  exact writePhysicalMemoryValue_at _ _ _

def body : List Stmt := segment ++ ImportedCreationDecoderElementFields.segment
def iteration (state : DenoteState) (source element array index : Nat) : DenoteState :=
  ImportedCreationDecoderElementFields.completed (completed state source element array index) source element

theorem actual_body : ImportedCreationDecoderElementFields.actualLoopBody = body := by rfl

/-- Execute the ENTIRE actual fourteen-instruction decoder loop body. -/
theorem execute_body (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (data array index element : Nat)
    (dataHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_data" = data)
    (arrayHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_memory" = array)
    (indexHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_element_index" = index)
    (pointer : (state.world.memory 64).val = element)
    (available : data + index * 128 + 128 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit)
    (budget : element + 128 ≤ 2^64 - 1)
    (cellBound : array + 32 + index * 32 < Verity.Core.Uint256.modulus)
    (canonical0 : ImportedCalldataWord.word state (data + index * 128) < 2^160)
    (canonical96 : ImportedCalldataWord.word state (data + index * 128 + 96) < 2^160) :
    execStmtList oracle fields state body = .continue (iteration state (data + index * 128) element array index) := by
  have first := execute oracle fields state data array index element dataHeld arrayHeld indexHeld pointer
    available sizeBound budget cellBound
  have held := descriptors state (data + index * 128) element array index
  have sourceBound : data + index * 128 + 96 < Verity.Core.Uint256.modulus := by
    have ceiling : Verity.Core.Int256.signBit < Verity.Core.Uint256.modulus := Verity.Core.Int256.signBit_lt_modulus
    omega
  have destinationBound : element + 96 < Verity.Core.Uint256.modulus := by
    have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
    omega
  have copied := ImportedCreationDecoderElementFields.execute oracle fields
    (completed state (data + index * 128) element array index) (data + index * 128) element
    held.1 held.2 sourceBound destinationBound
    (by rw [input_word]; exact canonical0) (by rw [input_word]; exact canonical96)
  rw [body, SolidityImport.exec_append, first]
  exact copied

/-- Bounded word-frame bridge, proved before instantiating deep allocator states. -/
theorem fields_pointer (state : DenoteState) (source element : Nat)
    (pastElement : 96 ≤ element) (initial : Coherent state.world) :
    (ImportedCreationDecoderElementFields.completed state source element).world.memory 64 = state.world.memory 64 := by
  apply ImportedAbiArray.word_of_bytes state.world
    (ImportedCreationDecoderElementFields.completed state source element).world 64 initial
    (ImportedCreationDecoderElementFields.coherent state source element initial)
  intro lane
  exact ImportedCreationDecoderElementFields.byte_frame state source element (64 + lane.val)
    (Or.inl (by have := lane.isLt; omega))

/-- All later field copies preserve the true allocator value. -/
theorem iteration_pointer (state : DenoteState) (source element array index : Nat)
    (pastCell : 96 ≤ array + 32 + index * 32) (pastElement : 96 ≤ element) :
    (iteration state source element array index).world.memory 64 = Verity.Core.Uint256.ofNat (element + 128) := by
  rw [iteration, fields_pointer _ _ _ pastElement (coherent state source element array index),
    free_pointer _ _ _ _ _ pastCell]

/-- Every actual pointer-cell byte survives all four struct field copies. -/
theorem iteration_cell_byte (state : DenoteState) (source element array index : Nat) (lane : Fin 32)
    (beforeElement : array + 64 + index * 32 ≤ element) :
    (iteration state source element array index).world.physicalByte (array + 32 + index * 32 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat element) lane := by
  rw [iteration, ImportedCreationDecoderElementFields.byte_frame _ _ _ _ (Or.inl (by have := lane.isLt; omega))]
  exact writePhysicalMemoryValue_byte_at _ _ _ _

theorem iteration_binding (state : DenoteState) (source element array index : Nat) (key : String)
    (notSource : "_verity_slice_tmp_0_array3_element_source" ≠ key)
    (notElement : "_verity_slice_tmp_0_array3_element_element" ≠ key)
    (notNext : "_verity_slice_tmp_0_array3_element_next" ≠ key) :
    lookupValue (iteration state source element array index).bindings key = lookupValue state.bindings key := by
  unfold iteration
  rw [ImportedCreationDecoderElementFields.binding_frame (completed state source element array index) source element]
  exact allocated_binding state source element key notSource notElement notNext

theorem iteration_input_word (state : DenoteState) (source element array index query : Nat) :
    ImportedCalldataWord.word (iteration state source element array index) query = ImportedCalldataWord.word state query := by
  rw [iteration, ImportedCreationDecoderElementFields.input_word, input_word]

theorem iteration_coherent (state : DenoteState) (source element array index : Nat) :
    Coherent (iteration state source element array index).world := by
  unfold iteration
  exact ImportedCreationDecoderElementFields.coherent (completed state source element array index) source element
    (coherent state source element array index)

theorem iteration_frame (state : DenoteState) (source element array index query : Nat)
    (outsidePointer : query < 64 ∨ 96 ≤ query)
    (outsideCell : query < array + 32 + index * 32 ∨ array + 64 + index * 32 ≤ query)
    (outsideElement : query < element ∨ element + 128 ≤ query) :
    (iteration state source element array index).world.physicalByte query = state.world.physicalByte query := by
  rw [iteration, ImportedCreationDecoderElementFields.byte_frame _ _ _ _ outsideElement]
  exact byte_frame _ _ _ _ _ _ outsidePointer outsideCell

theorem fields_size (state : DenoteState) (source destination : Nat) (entries : List ImportedCalldataFields.Entry) :
    (ImportedCalldataFields.run state source destination entries).world.calldataSize = state.world.calldataSize := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih => exact (ih _).trans (ImportedCreationDecoderArrayHead.copied_size _ _ _)

/-- A size projection is framed in bounded pieces before loop induction. -/
theorem iteration_size (state : DenoteState) (source element array index : Nat) :
    (iteration state source element array index).world.calldataSize = state.world.calldataSize := by
  unfold iteration ImportedCreationDecoderElementFields.completed
  rw [fields_size]
  rfl

end Contracts.SolidityImportSmoke.ImportedCreationDecoderElementPrelude
