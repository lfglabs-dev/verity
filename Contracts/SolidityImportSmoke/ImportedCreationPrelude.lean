import Contracts.SolidityImportSmoke.ImportedCreationFieldFrames
import Contracts.SolidityImportSmoke.ImportedCreationArrayDescriptors
import Contracts.SolidityImportSmoke.ImportedCreationArrayHeader

namespace Contracts.SolidityImportSmoke.ImportedCreationPrelude
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration
open ImportedCreationHeadFields

def copied (state : DenoteState) (source head : Nat) :=
  runFields (ImportedCreationHeadAllocation.allocated state head) source head firstEntries

def prepared (state : DenoteState) (source head : Nat) :=
  ImportedCreationArrayDescriptors.extracted (copied state source head) source

def segment := ImportedCreationHeadAllocation.segment ++ first ++ ImportedCreationArrayDescriptors.segment

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 39).take 15) = some segment := by rfl

theorem copied_coherent (state : DenoteState) (source head : Nat) : Coherent (copied state source head).world := by
  exact ImportedCreationFieldFrames.coherent _ _ _ _ (writePhysicalMemoryValue_coherent _ _ _)

/-- Every original input byte between96andtheABIhead survives actual allocation
and all three actual field copies. -/
theorem input_byte (state : DenoteState) (source head query : Nat)
    (pastPointer : 96 ≤ query) (before : query < head) :
    (copied state source head).world.physicalByte query = state.world.physicalByte query := by
  have fields := run_frame (ImportedCreationHeadAllocation.allocated state head) source head query firstEntries
    (by intro entry belongs; exact Or.inl (by omega))
  exact fields.trans (ImportedCreationHeadAllocation.input_byte state head query pastPointer before)

theorem input_word (state : DenoteState) (source head query : Nat) (coherent : Coherent state.world)
    (pastPointer : 96 ≤ query) (before : query + 32 ≤ head) :
    (copied state source head).world.memory query = state.world.memory query := by
  apply ImportedAbiArray.word_of_bytes state.world _ query coherent (copied_coherent state source head)
  intro offset
  exact input_byte state source head (query + offset.val) (by omega) (by have := offset.isLt; omega)

/-- Actual copied-head bindings: original Market pointer and allocated ABIhead. -/
theorem copied_bindings (state : DenoteState) (source head : Nat) :
    lookupValue (copied state source head).bindings "_verity_slice_tmp_0_memory" =
      lookupValue state.bindings "_verity_slice_tmp_0_memory" ∧
    lookupValue (copied state source head).bindings "_verity_slice_tmp_3" = head := by
  constructor
  · rw [copied, ImportedCreationFieldFrames.binding _ _ _ _ _ (by simp [firstEntries])]
    simp only [ImportedCreationHeadAllocation.allocated,
      SolidityImport.lookup_bind_other _ "_verity_slice_tmp_4" "_verity_slice_tmp_0_memory" _ (by decide),
      SolidityImport.lookup_bind_other _ "_verity_slice_tmp_3" "_verity_slice_tmp_0_memory" _ (by decide)]
  · rw [copied, ImportedCreationFieldFrames.binding _ _ _ _ _ (by simp [firstEntries])]
    simp only [ImportedCreationHeadAllocation.allocated,
      SolidityImport.lookup_bind_other _ "_verity_slice_tmp_4" "_verity_slice_tmp_3" _ (by decide), SolidityImport.lookup_bind_same]

/-- Derive the original array pointer from actual input-word preservation. -/
theorem array_pointer (state : DenoteState) (source head : Nat) (coherent : Coherent state.world)
    (pastPointer : 96 ≤ source) (before : source + 128 ≤ head) :
    ImportedCreationArrayDescriptors.pointer (copied state source head) source =
      ImportedCreationArrayDescriptors.pointer state source := by
  unfold ImportedCreationArrayDescriptors.pointer
  rw [input_word state source head (source + 96) coherent (by omega) (by omega)]

/-- Derive the original count too; a post-copy count local is not an input. -/
theorem array_count (state : DenoteState) (source head : Nat) (coherent : Coherent state.world)
    (pastPointer : 96 ≤ source) (before : source + 128 ≤ head)
    (arrayPast : 96 ≤ ImportedCreationArrayDescriptors.pointer state source)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 ≤ head) :
    ImportedCreationArrayDescriptors.count (copied state source head) source =
      ImportedCreationArrayDescriptors.count state source := by
  unfold ImportedCreationArrayDescriptors.count
  rw [array_pointer state source head coherent pastPointer before,
    input_word state source head _ coherent arrayPast arrayBefore]

/-- Execute ALL fifteen actualinstructions39..53: reservation/rootstore, first
threefields, then realarraydescriptorloads. No intermediateworld is assumed. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source head : Nat) (coherent : Coherent state.world)
    (pointer : (state.world.memory 64).val = head)
    (held : lookupValue state.bindings "_verity_slice_tmp_0_memory" = source)
    (pastPointer : 96 ≤ source) (sourceBefore : source + 256 ≤ head)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 ≤ head)
    (budget : head + 288 ≤ 2^64 - 1) :
    execStmtList oracle fields state segment = .continue (prepared state source head) := by
  have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
  have allocated := ImportedCreationHeadAllocation.execute oracle fields state head pointer budget
  have sourceHeld : lookupValue (ImportedCreationHeadAllocation.allocated state head).bindings "_verity_slice_tmp_0_memory" = source := by
    simp only [ImportedCreationHeadAllocation.allocated,
      SolidityImport.lookup_bind_other _ "_verity_slice_tmp_4" "_verity_slice_tmp_0_memory" _ (by decide),
      SolidityImport.lookup_bind_other _ "_verity_slice_tmp_3" "_verity_slice_tmp_0_memory" _ (by decide), held]
  have headHeld : lookupValue (ImportedCreationHeadAllocation.allocated state head).bindings "_verity_slice_tmp_3" = head := by
    simp only [ImportedCreationHeadAllocation.allocated,
      SolidityImport.lookup_bind_other _ "_verity_slice_tmp_4" "_verity_slice_tmp_3" _ (by decide), SolidityImport.lookup_bind_same]
  have fieldsRun := execute_first oracle fields (ImportedCreationHeadAllocation.allocated state head) source head
    (writePhysicalMemoryValue_coherent _ _ _) sourceHeld headHeld (by omega) (by omega)
  have descriptorsRun := ImportedCreationArrayDescriptors.execute oracle fields (copied state source head) source
    ((copied_bindings state source head).1.trans held) (by omega)
    (by rw [array_pointer state source head coherent pastPointer (by omega)]; omega)
  rw [segment, SolidityImport.exec_append, SolidityImport.exec_append, allocated]
  change (match execStmtList oracle fields (ImportedCreationHeadAllocation.allocated state head) first with
    | .continue after => execStmtList oracle fields after ImportedCreationArrayDescriptors.segment
    | other => other) = _
  rw [fieldsRun]
  exact descriptorsRun

/-- The actual free-pointer word is preserved by every field copy. -/
theorem free_pointer (state : DenoteState) (source head : Nat) (pastPointer : 96 ≤ head) :
    (prepared state source head).world.memory 64 = Verity.Core.Uint256.ofNat (head + 288) := by
  change (runFields (ImportedCreationHeadAllocation.allocated state head) source head firstEntries).world.memory 64 = _
  rw [ImportedCreationFieldFrames.word _ _ _ _ _ (writePhysicalMemoryValue_coherent _ _ _)
    (by intro entry belongs; exact Or.inl (by omega))]
  exact ImportedCreationHeadAllocation.free_pointer state head pastPointer

/-- Actual prepared bindings refer to ORIGINAL pointer/count and allocatedhead. -/
theorem descriptors (state : DenoteState) (source head : Nat) (coherent : Coherent state.world)
    (pastPointer : 96 ≤ source) (before : source + 128 ≤ head)
    (arrayPast : 96 ≤ ImportedCreationArrayDescriptors.pointer state source)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 ≤ head) :
    lookupValue (prepared state source head).bindings "_verity_slice_tmp_3" = head ∧
    lookupValue (prepared state source head).bindings "_verity_slice_tmp_9" = ImportedCreationArrayDescriptors.count state source ∧
    lookupValue (prepared state source head).bindings "_verity_slice_tmp_10" = ImportedCreationArrayDescriptors.pointer state source + 32 := by
  have actual := ImportedCreationArrayDescriptors.descriptors (copied state source head) source
  rw [array_pointer state source head coherent pastPointer before,
    array_count state source head coherent pastPointer before arrayPast arrayBefore] at actual
  refine ⟨?_, actual.2.1, actual.2.2⟩
  exact (ImportedCreationArrayDescriptors.binding_frame (copied state source head) source "_verity_slice_tmp_3"
    (by decide) (by decide) (by decide)).trans (copied_bindings state source head).2

def allocationSegment := segment ++ ImportedCreationArrayAllocation.segment

def tailAllocated (state : DenoteState) (source head : Nat) : DenoteState :=
  let ready := prepared state source head
  let finish := head + 288 + (32 + 128 * ImportedCreationArrayDescriptors.count state source)
  { ready with
    bindings := bindValue (bindValue ready.bindings "_verity_slice_tmp_11" (head + 288)) "_verity_slice_tmp_12" finish
    world := ready.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat finish) }

theorem actual_allocation_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 39).take 20) = some allocationSegment := by rfl

/-- Execute the entire REAL20-instruction allocationprefix, deriving the dynamic
size from the ORIGINAL loaded array count and updated static-head free pointer. -/
theorem execute_allocated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source head : Nat) (coherent : Coherent state.world)
    (pointer : (state.world.memory 64).val = head)
    (held : lookupValue state.bindings "_verity_slice_tmp_0_memory" = source)
    (pastPointer : 96 ≤ source) (sourceBefore : source + 256 ≤ head)
    (arrayPast : 96 ≤ ImportedCreationArrayDescriptors.pointer state source)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 ≤ head)
    (budget : head + 320 + 128 * ImportedCreationArrayDescriptors.count state source ≤ 2^64 - 1) :
    execStmtList oracle fields state allocationSegment = .continue (tailAllocated state source head) := by
  have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
  have initial := execute oracle fields state source head coherent pointer held pastPointer sourceBefore arrayBefore (by omega)
  have facts := descriptors state source head coherent pastPointer (by omega) arrayPast arrayBefore
  have free : ((prepared state source head).world.memory 64).val = head + 288 := by
    rw [free_pointer state source head (by omega), Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt (by omega)]
  have dynamic := ImportedCreationArrayAllocation.execute oracle fields (prepared state source head)
    (head + 288) (ImportedCreationArrayDescriptors.count state source) free facts.2.1 (by omega)
  rw [allocationSegment, SolidityImport.exec_append, initial]
  exact dynamic

/-- The second real allocator write at64 preserves all ORIGINAL input bytes
at96orabovebeforetheoutputhead, across the entire20instructionprefix. -/
theorem allocated_input_byte (state : DenoteState) (source head query : Nat)
    (pastPointer : 96 ≤ query) (before : query < head) :
    (tailAllocated state source head).world.physicalByte query = state.world.physicalByte query := by
  change ((prepared state source head).world.writePhysicalMemoryValue 64 _).physicalByte query = _
  rw [writePhysicalMemoryValue_byte_outside _ _ _ _ (Or.inr pastPointer)]
  exact input_byte state source head query pastPointer before

theorem allocated_input_word (state : DenoteState) (source head query : Nat)
    (coherent : Coherent state.world) (pastPointer : 96 ≤ query) (before : query + 32 ≤ head) :
    (tailAllocated state source head).world.memory query = state.world.memory query := by
  apply ImportedAbiArray.word_of_bytes state.world _ query coherent (writePhysicalMemoryValue_coherent _ _ _)
  intro offset
  exact allocated_input_byte state source head (query + offset.val) (by omega) (by have := offset.isLt; omega)

/-- The ORIGINAL pointer-array words survive both allocators and all headwrites. -/
theorem allocated_source_at (state : DenoteState) (source head base index : Nat)
    (coherent : Coherent state.world) (pastPointer : 96 ≤ base) (before : base + 32 * index + 32 ≤ head) :
    ImportedAbiArray.sourceAt (tailAllocated state source head).world base index =
      ImportedAbiArray.sourceAt state.world base index := by
  unfold ImportedAbiArray.sourceAt
  rw [allocated_input_word state source head _ coherent (by omega) before]

theorem allocated_binding (state : DenoteState) (source head : Nat) (key : String)
    (n11 : "_verity_slice_tmp_11" ≠ key) (n12 : "_verity_slice_tmp_12" ≠ key) :
    lookupValue (tailAllocated state source head).bindings key = lookupValue (prepared state source head).bindings key := by
  change lookupValue (bindValue (bindValue _ "_verity_slice_tmp_11" _) "_verity_slice_tmp_12" _) key = _
  rw [SolidityImport.lookup_bind_other _ _ _ _ n12, SolidityImport.lookup_bind_other _ _ _ _ n11]

/-- Descriptors for the following actual metadata+arrayloop are derived from
ORIGINAL inputs and real allocations. No post-reservation bindings are assumed. -/
theorem allocated_descriptors (state : DenoteState) (source head : Nat) (coherent : Coherent state.world)
    (pastPointer : 96 ≤ source) (before : source + 128 ≤ head)
    (arrayPast : 96 ≤ ImportedCreationArrayDescriptors.pointer state source)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 ≤ head) :
    lookupValue (tailAllocated state source head).bindings "_verity_slice_tmp_3" = head ∧
    lookupValue (tailAllocated state source head).bindings "_verity_slice_tmp_9" = ImportedCreationArrayDescriptors.count state source ∧
    lookupValue (tailAllocated state source head).bindings "_verity_slice_tmp_10" = ImportedCreationArrayDescriptors.pointer state source + 32 ∧
    lookupValue (tailAllocated state source head).bindings "_verity_slice_tmp_11" = head + 288 := by
  have facts := descriptors state source head coherent pastPointer before arrayPast arrayBefore
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (allocated_binding state source head "_verity_slice_tmp_3" (by decide) (by decide)).trans facts.1
  · exact (allocated_binding state source head "_verity_slice_tmp_9" (by decide) (by decide)).trans facts.2.1
  · exact (allocated_binding state source head "_verity_slice_tmp_10" (by decide) (by decide)).trans facts.2.2
  · change lookupValue (bindValue (bindValue _ "_verity_slice_tmp_11" (head + 288)) "_verity_slice_tmp_12" _) "_verity_slice_tmp_11" = _
    rw [SolidityImport.lookup_bind_other _ "_verity_slice_tmp_12" "_verity_slice_tmp_11" _ (by decide), SolidityImport.lookup_bind_same]

def arraySegment := allocationSegment ++ ImportedCreationArrayHeader.fullSegment

def arrayCompleted (state : DenoteState) (source head : Nat) :=
  ImportedCreationArrayHeader.completed (tailAllocated state source head) head
    (ImportedCreationArrayDescriptors.pointer state source + 32) (ImportedCreationArrayDescriptors.count state source)

theorem actual_array_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 39).take 23) = some arraySegment := by rfl

/-- Execute ALL23actualinstructions through the complete variable-count loop.
Descriptors, original pointer values and allocation sizes are derived, not
assumed to hold at an intermediate boundary. -/
theorem execute_array (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source head : Nat) (coherent : Coherent state.world)
    (pointer : (state.world.memory 64).val = head)
    (held : lookupValue state.bindings "_verity_slice_tmp_0_memory" = source)
    (pastPointer : 96 ≤ source) (sourceBefore : source + 256 ≤ head)
    (arrayPast : 96 ≤ ImportedCreationArrayDescriptors.pointer state source)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 +
      32 * ImportedCreationArrayDescriptors.count state source ≤ head)
    (sources : ∀ i < ImportedCreationArrayDescriptors.count state source,
      ImportedAbiArray.sourceAt state.world (ImportedCreationArrayDescriptors.pointer state source + 32) i + 128 ≤ head)
    (budget : head + 320 + 128 * ImportedCreationArrayDescriptors.count state source ≤ 2^64 - 1) :
    execStmtList oracle fields state arraySegment = .continue (arrayCompleted state source head) := by
  have allocation := execute_allocated oracle fields state source head coherent pointer held pastPointer sourceBefore
    arrayPast (by omega) budget
  have facts := allocated_descriptors state source head coherent pastPointer (by omega) arrayPast (by omega)
  have run := ImportedCreationArrayHeader.execute_full oracle fields (tailAllocated state source head)
    head (ImportedCreationArrayDescriptors.pointer state source + 32) (ImportedCreationArrayDescriptors.count state source)
    (writePhysicalMemoryValue_coherent _ _ _) facts.1 facts.2.2.2 facts.2.1 facts.2.2.1 arrayBefore
    (by intro i live; rw [allocated_source_at state source head _ i coherent (by omega) (by omega)]; exact sources i live)
    budget
  rw [arraySegment, SolidityImport.exec_append, allocation]
  exact run

/-- Every array output byte now refers to the ORIGINAL encoder-entry Market
pointer-array and source structs, across both allocations, headcopies and stores. -/
theorem array_bytes (state : DenoteState) (source head : Nat) (coherent : Coherent state.world)
    (arrayPast : 96 ≤ ImportedCreationArrayDescriptors.pointer state source)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 +
      32 * ImportedCreationArrayDescriptors.count state source ≤ head)
    (sources : ∀ i < ImportedCreationArrayDescriptors.count state source,
      96 ≤ ImportedAbiArray.sourceAt state.world (ImportedCreationArrayDescriptors.pointer state source + 32) i ∧
      ImportedAbiArray.sourceAt state.world (ImportedCreationArrayDescriptors.pointer state source + 32) i + 128 ≤ head)
    (index : Fin (ImportedCreationArrayDescriptors.count state source)) (offset : Fin 128) :
    (arrayCompleted state source head).world.physicalByte (head + 320 + 128 * index.val + offset.val) =
      state.world.physicalByte (ImportedAbiArray.sourceAt state.world
        (ImportedCreationArrayDescriptors.pointer state source + 32) index.val + offset.val) := by
  have pointers : ∀ i < ImportedCreationArrayDescriptors.count state source,
      ImportedAbiArray.sourceAt (tailAllocated state source head).world (ImportedCreationArrayDescriptors.pointer state source + 32) i =
      ImportedAbiArray.sourceAt state.world (ImportedCreationArrayDescriptors.pointer state source + 32) i := by
    intro i live
    exact allocated_source_at state source head _ i coherent (by omega) (by omega)
  have bytes := ImportedCreationArrayHeader.output_bytes (tailAllocated state source head) head
    (ImportedCreationArrayDescriptors.pointer state source + 32) (ImportedCreationArrayDescriptors.count state source)
    (writePhysicalMemoryValue_coherent _ _ _) arrayBefore
    (by intro i live; rw [pointers i live]; exact (sources i live).2) index offset
  rw [pointers index.val index.isLt] at bytes
  exact bytes.trans (allocated_input_byte state source head _ (by have := (sources index.val index.isLt).1; omega)
    (by have := (sources index.val index.isLt).2; have := offset.isLt; omega))

theorem array_coherent (state : DenoteState) (source head : Nat) : Coherent (arrayCompleted state source head).world := by
  rw [arrayCompleted, ImportedCreationArrayHeader.completed, ImportedCreationArrayLoop.world_eq]
  exact ImportedAbiArray.coherent _ _ _ _ (writePhysicalMemoryValue_coherent _ _ _)

/-- The complete actual arrayloop retains both original Market and ABIhead
bindings, so the following last4fields use their actual descriptors. -/
theorem array_bindings (state : DenoteState) (source head : Nat) (coherent : Coherent state.world)
    (pastPointer : 96 ≤ source) (before : source + 128 ≤ head)
    (arrayPast : 96 ≤ ImportedCreationArrayDescriptors.pointer state source)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 ≤ head) :
    lookupValue (arrayCompleted state source head).bindings "_verity_slice_tmp_0_memory" =
      lookupValue state.bindings "_verity_slice_tmp_0_memory" ∧
    lookupValue (arrayCompleted state source head).bindings "_verity_slice_tmp_3" = head := by
  have headHeld := (allocated_descriptors state source head coherent pastPointer before arrayPast arrayBefore).1
  constructor
  · rw [arrayCompleted, ImportedCreationArrayHeader.completed, ImportedCreationArrayLoop.binding_frame _ _ _ _ _ (by decide) (by decide)]
    change lookupValue (tailAllocated state source head).bindings "_verity_slice_tmp_0_memory" = _
    rw [allocated_binding _ _ _ _ (by decide) (by decide)]
    exact (ImportedCreationArrayDescriptors.binding_frame (copied state source head) source "_verity_slice_tmp_0_memory"
      (by decide) (by decide) (by decide)).trans (copied_bindings state source head).1
  · rw [arrayCompleted, ImportedCreationArrayHeader.completed, ImportedCreationArrayLoop.binding_frame _ _ _ _ _ (by decide) (by decide)]
    exact headHeld

def fullSegment := arraySegment ++ last

def completed (state : DenoteState) (source head : Nat) := runFields (arrayCompleted state source head) source head lastEntries

theorem actual_full_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 39).take 31) = some fullSegment := by rfl

/-- Execute the ENTIREactual31instructionMarketencoder, including every real
allocation, both field groups, descriptor loads, metadata stores and arrayloop. -/
theorem execute_full (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source head : Nat) (coherent : Coherent state.world)
    (pointer : (state.world.memory 64).val = head)
    (held : lookupValue state.bindings "_verity_slice_tmp_0_memory" = source)
    (pastPointer : 96 ≤ source) (sourceBefore : source + 256 ≤ head)
    (arrayPast : 96 ≤ ImportedCreationArrayDescriptors.pointer state source)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 +
      32 * ImportedCreationArrayDescriptors.count state source ≤ head)
    (sources : ∀ i < ImportedCreationArrayDescriptors.count state source,
      ImportedAbiArray.sourceAt state.world (ImportedCreationArrayDescriptors.pointer state source + 32) i + 128 ≤ head)
    (budget : head + 320 + 128 * ImportedCreationArrayDescriptors.count state source ≤ 2^64 - 1) :
    execStmtList oracle fields state fullSegment = .continue (completed state source head) := by
  have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
  have arrayRun := execute_array oracle fields state source head coherent pointer held pastPointer sourceBefore
    arrayPast arrayBefore sources budget
  have facts := array_bindings state source head coherent pastPointer (by omega) arrayPast (by omega)
  have lastRun := execute_last oracle fields (arrayCompleted state source head) source head (array_coherent state source head)
    (facts.1.trans held) facts.2 (by omega) (by omega)
  rw [fullSegment, SolidityImport.exec_append, arrayRun]
  exact lastRun

/-- The actual fullencoder free-pointer word derives its exact total payload
size320+128*count. The loop/lastfields cannot clobber the actual allocator write. -/
theorem completed_pointer (state : DenoteState) (source head : Nat) (pastPointer : 96 ≤ head) :
    (completed state source head).world.memory 64 =
      Verity.Core.Uint256.ofNat (head + 320 + 128 * ImportedCreationArrayDescriptors.count state source) := by
  rw [completed, ImportedCreationFieldFrames.word _ _ _ _ _ (array_coherent state source head)
    (by intro entry belongs; exact Or.inl (by omega))]
  rw [arrayCompleted, ImportedCreationArrayHeader.metadata_word _ _ _ _ _ (by omega)]
  rw [ImportedCreationArrayHeader.words_before _ _ _ _ (writePhysicalMemoryValue_coherent _ _ _) (by omega)]
  change ((prepared state source head).world.writePhysicalMemoryValue 64 _).memory 64 = _
  rw [writePhysicalMemoryValue_at]
  congr 1
  omega

/-- The final four realfieldcopies preserve EVERY already-encoded array byte. -/
theorem completed_array_bytes (state : DenoteState) (source head : Nat) (coherent : Coherent state.world)
    (arrayPast : 96 ≤ ImportedCreationArrayDescriptors.pointer state source)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 +
      32 * ImportedCreationArrayDescriptors.count state source ≤ head)
    (sources : ∀ i < ImportedCreationArrayDescriptors.count state source,
      96 ≤ ImportedAbiArray.sourceAt state.world (ImportedCreationArrayDescriptors.pointer state source + 32) i ∧
      ImportedAbiArray.sourceAt state.world (ImportedCreationArrayDescriptors.pointer state source + 32) i + 128 ≤ head)
    (index : Fin (ImportedCreationArrayDescriptors.count state source)) (offset : Fin 128) :
    (completed state source head).world.physicalByte (head + 320 + 128 * index.val + offset.val) =
      state.world.physicalByte (ImportedAbiArray.sourceAt state.world
        (ImportedCreationArrayDescriptors.pointer state source + 32) index.val + offset.val) := by
  rw [completed, run_frame _ _ _ _ _ (by
    intro entry belongs
    simp only [lastEntries, List.mem_cons, List.not_mem_nil, or_false] at belongs
    rcases belongs with rfl | rfl | rfl | rfl <;> exact Or.inr (by omega))]
  exact array_bytes state source head coherent arrayPast arrayBefore sources index offset

end Contracts.SolidityImportSmoke.ImportedCreationPrelude
