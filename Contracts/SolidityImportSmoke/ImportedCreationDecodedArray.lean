import Contracts.SolidityImportSmoke.ImportedCreationDecoderArrayLoop

namespace Contracts.SolidityImportSmoke.ImportedCreationDecodedArray
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration

abbrev rootPointer := ImportedCreationDecoderArrayBounds.rootPointer
abbrev count := ImportedCreationDecoderArrayBounds.originalCount
abbrev header := ImportedCreationDecoderArrayBounds.originalHeader
def data (state : DenoteState) : Nat := header state + 32
def free (state : DenoteState) : Nat := 384 + 32 * (count state + 1)
abbrev prepared := ImportedCreationDecoderArrayBounds.allocationCompleted

theorem allocated_input_word (state : DenoteState) (base count query : Nat) :
    ImportedCalldataWord.word (ImportedCreationDecoderArrayBounds.allocated state base count) query =
      ImportedCalldataWord.word state query := by rfl

theorem bounds_input_word (state : DenoteState) (base count header query : Nat) :
    ImportedCalldataWord.word (ImportedCreationDecoderArrayBounds.completed state base count header) query =
      ImportedCalldataWord.word state query := by rfl

theorem original_word (state : DenoteState) (query : Nat) :
    ImportedCalldataWord.word (prepared state) query = ImportedCalldataWord.word state query := by
  unfold prepared
  rw [ImportedCreationDecoderArrayBounds.allocationCompleted, allocated_input_word,
    ImportedCreationDecoderArrayBounds.prefixCompleted, bounds_input_word,
    ImportedCreationDecoderArrayHead.prefixCompleted]
  change ImportedCalldataWord.word (ImportedCreationDecoderFields.prefixCompleted state) query = _
  exact ImportedCreationDecoderArrayHead.original_word state query

theorem allocated_size (state : DenoteState) (base count : Nat) :
    (ImportedCreationDecoderArrayBounds.allocated state base count).world.calldataSize = state.world.calldataSize := by rfl

theorem original_size (state : DenoteState) :
    (prepared state).world.calldataSize = state.world.calldataSize := by
  unfold prepared
  rw [ImportedCreationDecoderArrayBounds.allocationCompleted, allocated_size,
    ImportedCreationDecoderArrayBounds.prefixCompleted, ImportedCreationDecoderArrayBounds.world_eq,
    ImportedCreationDecoderArrayBounds.original_size]

theorem allocated_bindings (state : DenoteState) (base count : Nat) :
    (ImportedCreationDecoderArrayBounds.allocated state base count).bindings = state.bindings := by rfl

/-- All actual loop descriptors are derived from original calldata and real stores. -/
theorem descriptors (state : DenoteState) :
    lookupValue (prepared state).bindings "_verity_slice_tmp_0_array3_data" = data state ∧
    lookupValue (prepared state).bindings "_verity_slice_tmp_0_array3_memory" = 384 ∧
    lookupValue (prepared state).bindings "_verity_slice_tmp_0_array3_length" = count state := by
  unfold prepared
  rw [ImportedCreationDecoderArrayBounds.allocationCompleted, allocated_bindings]
  exact ⟨(ImportedCreationDecoderArrayBounds.prefix_descriptors state).2,
    ImportedCreationDecoderArrayBounds.prefix_inputs state⟩

theorem initial_pointer (state : DenoteState) (budget : free state ≤ 2^64 - 1) :
    ((prepared state).world.memory 64).val = free state := by
  unfold prepared
  rw [ImportedCreationDecoderArrayBounds.allocationCompleted, ImportedCreationDecoderArrayBounds.allocated_pointer]
  change (Verity.Core.Uint256.ofNat (free state)).val = free state
  have bound : free state < Verity.Core.Uint256.modulus := by
    have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
    omega
  exact Nat.mod_eq_of_lt bound

theorem prepared_coherent (state : DenoteState) : Coherent (prepared state).world := by
  unfold prepared ImportedCreationDecoderArrayBounds.allocationCompleted
  exact ImportedCreationDecoderArrayBounds.allocated_coherent _ _ _

def segment : List Stmt := ImportedCreationDecoderArrayBounds.allocationPrefix ++
  [ImportedCreationDecoderArrayLoop.statement]
def completed (state : DenoteState) : DenoteState :=
  ImportedCreationDecoderArrayLoop.runElements (prepared state) (data state) 384 (free state) (count state)

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body.take 29) = some segment := by rfl

/-- Actual original-transaction instructions0..28, including the full decoder
loop for arbitrary count. All intermediate loop-entry observations are derived. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (headAvailable : 100 ≤ state.world.calldataSize.val)
    (rootOffsetBound : ImportedAbiTupleHead.rawOffset state 0 ≤ 2^64 - 1)
    (tupleAvailable : rootPointer state + 256 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit)
    (canonical32 : ImportedCalldataWord.word state (rootPointer state + 32) < 2^160)
    (canonical64 : ImportedCalldataWord.word state (rootPointer state + 64) < 2^160)
    (offsetBound : ImportedCreationDecoderArrayHead.relative state (rootPointer state) ≤ 2^64 - 1)
    (arrayAvailable : header state + 32 ≤ state.world.calldataSize.val)
    (budget : free state + count state * 128 ≤ 2^64 - 1)
    (payloadAvailable : data state + count state * 128 ≤ state.world.calldataSize.val)
    (canonical : ∀ i < count state, ImportedCalldataWord.word state (data state + i * 128) < 2^160 ∧
      ImportedCalldataWord.word state (data state + i * 128 + 96) < 2^160) :
    execStmtList oracle fields state segment = .continue (completed state) := by
  have reserveBudget : free state ≤ 2^64 - 1 := by omega
  have first := ImportedCreationDecoderArrayBounds.execute_allocation_prefix oracle fields state
    headAvailable rootOffsetBound tupleAvailable sizeBound canonical32 canonical64 offsetBound arrayAvailable
    reserveBudget (by simpa only [data, Nat.mul_comm] using payloadAvailable)
  have held := descriptors state
  have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
  have cells : 384 + 32 + count state * 32 < Verity.Core.Uint256.modulus := by
    unfold free at reserveBudget
    omega
  have copied := ImportedCreationDecoderArrayLoop.execute oracle fields (prepared state)
    (data state) 384 (free state) (count state) held.1 held.2.1 held.2.2 (initial_pointer state reserveBudget)
    (by decide) (by unfold free; omega)
    (by simpa only [original_size] using payloadAvailable)
    (by simpa only [original_size] using sizeBound) budget cells (by
      intro i live
      simpa only [original_word] using canonical i live)
  rw [segment, SolidityImport.exec_append, first]
  exact (SolidityImport.exec_singleton oracle fields _ _).trans copied

theorem coherent (state : DenoteState) : Coherent (completed state).world :=
  ImportedCreationDecoderArrayLoop.coherent _ _ _ _ _ (prepared_coherent state)

theorem free_pointer (state : DenoteState) (budget : free state + count state * 128 ≤ 2^64 - 1) :
    ((completed state).world.memory 64).val = free state + count state * 128 := by
  exact ImportedCreationDecoderArrayLoop.free_pointer (prepared state) (data state) 384 (free state) (count state)
    (initial_pointer state (by omega)) (by decide) (by unfold free; omega) budget

/-- Every original-input pointed-to struct address is derived from actual allocator execution. -/
theorem pointer_cell (state : DenoteState) (index : Nat) (live : index < count state) :
    (completed state).world.memory (416 + index * 32) = Verity.Core.Uint256.ofNat (free state + index * 128) := by
  exact ImportedCreationDecoderArrayLoop.pointer_cell_word (prepared state) (data state) 384 (free state)
    (count state) index (prepared_coherent state) (by decide) (by unfold free; omega) live

/-- Every field byte is an ORIGINAL transaction calldata observation. -/
theorem element_byte (state : DenoteState) (index offset : Nat) (lane : Fin 32)
    (live : index < count state) (valid : offset = 0 ∨ offset = 32 ∨ offset = 64 ∨ offset = 96) :
    (completed state).world.physicalByte (free state + index * 128 + offset + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (data state + index * 128 + offset))) lane := by
  have bytes := ImportedCreationDecoderArrayLoop.element_byte (prepared state) (data state) 384 (free state)
    (count state) index offset lane (by unfold free; omega) (by unfold free; omega) live valid
  rw [original_word] at bytes
  exact bytes

theorem prepared_binding (state : DenoteState) (key : String)
    (notNext : "_verity_slice_tmp_0_array3_next" ≠ key) (notData : "_verity_slice_tmp_0_array3_data" ≠ key)
    (notArray : "_verity_slice_tmp_0_array3_memory" ≠ key) (notHeader : "_verity_slice_tmp_0_array3_header" ≠ key)
    (notLength : "_verity_slice_tmp_0_array3_length" ≠ key) :
    lookupValue (prepared state).bindings key = lookupValue (ImportedCreationDecoderFields.prefixCompleted state).bindings key := by
  unfold prepared
  rw [ImportedCreationDecoderArrayBounds.allocationCompleted, allocated_bindings,
    ImportedCreationDecoderArrayBounds.prefixCompleted,
    ImportedCreationDecoderArrayBounds.binding_frame _ _ _ _ _ notNext notData,
    ImportedCreationDecoderArrayHead.prefixCompleted,
    ImportedCreationDecoderArrayHead.binding_frame _ _ _ _ notArray notHeader notLength]

theorem market_bindings (state : DenoteState) :
    lookupValue (completed state).bindings "_verity_slice_tmp_0_calldata" = rootPointer state ∧
    lookupValue (completed state).bindings "_verity_slice_tmp_0_memory" = 128 := by
  have first := ImportedCreationDecoderArrayLoop.binding_frame (prepared state) (data state) 384 (free state)
    (count state) "_verity_slice_tmp_0_calldata" (by decide) (by decide) (by decide) (by decide)
  have second := ImportedCreationDecoderArrayLoop.binding_frame (prepared state) (data state) 384 (free state)
    (count state) "_verity_slice_tmp_0_memory" (by decide) (by decide) (by decide) (by decide)
  rw [prepared_binding _ _ (by decide) (by decide) (by decide) (by decide) (by decide)] at first second
  exact ⟨first.trans (ImportedCreationDecoderFields.prefix_bindings state).1,
    second.trans (ImportedCreationDecoderFields.prefix_bindings state).2⟩

/-- Real array allocator writes preserve the previously decoded Market object. -/
theorem prepared_market_byte (state : DenoteState) (query : Nat) (lower : 96 ≤ query) (upper : query < 384) :
    (prepared state).world.physicalByte query =
      (ImportedCreationDecoderFields.prefixCompleted state).world.physicalByte query := by
  unfold prepared
  rw [ImportedCreationDecoderArrayBounds.allocationCompleted,
    ImportedCreationDecoderArrayBounds.allocated_frame _ _ _ _ (Or.inr lower) (Or.inl upper),
    ImportedCreationDecoderArrayBounds.prefixCompleted, ImportedCreationDecoderArrayBounds.world_eq,
    ImportedCreationDecoderArrayHead.prefixCompleted, ImportedCreationDecoderArrayHead.world_eq]

theorem market_byte (state : DenoteState) (query : Nat) (lower : 96 ≤ query) (upper : query < 384) :
    (completed state).world.physicalByte query =
      (ImportedCreationDecoderFields.prefixCompleted state).world.physicalByte query := by
  have frame := ImportedCreationDecoderArrayLoop.byte_frame (prepared state) (data state) 384 (free state)
    (count state) query (Or.inr lower) (Or.inl (by omega)) (Or.inl (by unfold free; omega))
  exact frame.trans (prepared_market_byte state query lower upper)

/-- Actual stored array count remains intact after every element iteration. -/
theorem count_word (state : DenoteState) :
    (completed state).world.memory 384 = Verity.Core.Uint256.ofNat (count state) := by
  have framed := ImportedAbiArray.word_of_bytes (prepared state).world (completed state).world 384
    (prepared_coherent state) (coherent state) (by
      intro lane
      exact ImportedCreationDecoderArrayLoop.byte_frame (prepared state) (data state) 384 (free state)
        (count state) (384 + lane.val) (Or.inr (by omega)) (Or.inl (by have := lane.isLt; omega))
        (Or.inl (by have := lane.isLt; unfold free; omega)))
  rw [framed]
  exact ImportedCreationDecoderArrayBounds.allocated_count _ _ _ (by decide)

end Contracts.SolidityImportSmoke.ImportedCreationDecodedArray
