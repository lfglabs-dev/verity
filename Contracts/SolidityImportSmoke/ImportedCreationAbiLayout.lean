import Contracts.SolidityImportSmoke.ImportedCreationPrelude

namespace Contracts.SolidityImportSmoke.ImportedCreationAbiLayout
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration
open ImportedCreationHeadFields ImportedCreationPrelude

/-- All original input bytes96..headsurvive the complete arrayencoder. -/
theorem array_input_byte (state : DenoteState) (source head query : Nat)
    (pastPointer : 96 ≤ query) (before : query < head) :
    (arrayCompleted state source head).world.physicalByte query = state.world.physicalByte query := by
  rw [arrayCompleted, ImportedCreationArrayHeader.completed,
    ImportedCreationArrayLoop.output_frame _ _ _ _ _ (Or.inl (by omega)),
    ImportedCreationArrayHeader.bytes_before _ _ _ _ (by omega)]
  exact allocated_input_byte state source head query pastPointer before

/-- Final staticfields retain every complete word before their destination. -/
theorem earlier_word (state : DenoteState) (source head query : Nat) (before : query + 32 ≤ head + 160) :
    (completed state source head).world.memory query = (arrayCompleted state source head).world.memory query := by
  rw [completed]
  apply ImportedCreationFieldFrames.word _ _ _ _ _ (array_coherent state source head)
  intro entry belongs
  simp only [lastEntries, List.mem_cons, List.not_mem_nil, or_false] at belongs
  rcases belongs with rfl | rfl | rfl | rfl <;> exact Or.inl (by omega)

/-- Final staticfields also retain the length word immediately after the head. -/
theorem length_word (state : DenoteState) (source head : Nat) :
    (completed state source head).world.memory (head + 288) =
      Verity.Core.Uint256.ofNat (ImportedCreationArrayDescriptors.count state source) := by
  rw [completed, ImportedCreationFieldFrames.word _ _ _ _ _ (array_coherent state source head) (by
    intro entry belongs
    simp only [lastEntries, List.mem_cons, List.not_mem_nil, or_false] at belongs
    rcases belongs with rfl | rfl | rfl | rfl <;> exact Or.inr (by omega))]
  exact ImportedCreationArrayHeader.completed_length _ _ _ _

theorem offset_word (state : DenoteState) (source head : Nat) :
    (completed state source head).world.memory (head + 128) = Verity.Core.Uint256.ofNat 256 := by
  rw [earlier_word _ _ _ _ (by omega)]
  exact ImportedCreationArrayHeader.completed_offset _ _ _ _

/-- The root32offset survives BOTHallocators, allfieldcopies and the arrayloop. -/
theorem root_word (state : DenoteState) (source head : Nat) (pastPointer : 96 ≤ head) :
    (completed state source head).world.memory head = Verity.Core.Uint256.ofNat 32 := by
  rw [earlier_word _ _ _ _ (by omega), arrayCompleted,
    ImportedCreationArrayHeader.metadata_word _ _ _ _ _ (by omega),
    ImportedCreationArrayHeader.words_before _ _ _ _ (writePhysicalMemoryValue_coherent _ _ _) (by omega)]
  change (((prepared state source head).world.writePhysicalMemoryValue 64 _).memory head) = _
  change (((prepared state source head).world.writePhysicalMemoryWord 64 _).memory head) = _
  rw [writePhysicalMemoryWord_outside _ _ _ _ (show Coherent (prepared state source head).world from copied_coherent state source head) (Or.inr pastPointer)]
  change (runFields (ImportedCreationHeadAllocation.allocated state head) source head firstEntries).world.memory head = _
  rw [ImportedCreationFieldFrames.word _ _ _ _ _ (writePhysicalMemoryValue_coherent _ _ _) (by intro entry belongs; exact Or.inl (by omega))]
  exact ImportedCreationHeadAllocation.root_word state head

/-- First3fieldoutputbytes retain the ORIGINALencoderinput, across all
subsequentallocations, metadata and finalfieldstores. -/
theorem first_bytes (state : DenoteState) (source head offset : Nat)
    (pastPointer : 96 ≤ source) (before : source + 256 ≤ head) (inside : offset < 96) :
    (completed state source head).world.physicalByte (head + 32 + offset) =
      state.world.physicalByte (source + offset) := by
  rw [completed, run_frame _ _ _ _ _ (by
    intro entry belongs
    simp only [lastEntries, List.mem_cons, List.not_mem_nil, or_false] at belongs
    rcases belongs with rfl | rfl | rfl | rfl <;> exact Or.inl (by omega))]
  rw [arrayCompleted, ImportedCreationArrayHeader.completed,
    ImportedCreationArrayLoop.output_frame _ _ _ _ _ (Or.inl (by omega)),
    ImportedCreationArrayHeader.bytes_before _ _ _ _ (by omega)]
  change (((prepared state source head).world.writePhysicalMemoryValue 64 _).physicalByte (head + 32 + offset)) = _
  rw [writePhysicalMemoryValue_byte_outside _ _ _ _ (Or.inr (by omega))]
  have bytes := written_byte (ImportedCreationHeadAllocation.allocated state head) source head offset firstEntries
    (by intro entry belongs; simp only [firstEntries, List.mem_cons, List.not_mem_nil, or_false] at belongs
        rcases belongs with rfl | rfl | rfl <;> omega) (by
      by_cases a : offset < 32
      · exact ⟨("_verity_slice_tmp_5", 0), by simp [firstEntries], by omega⟩
      by_cases b : offset < 64
      · exact ⟨("_verity_slice_tmp_6", 32), by simp [firstEntries], by omega⟩
      · exact ⟨("_verity_slice_tmp_7", 64), by simp [firstEntries], by omega⟩)
  exact bytes.trans (ImportedCreationHeadAllocation.input_byte state head (source + offset) (by omega) (by omega))

/-- Last4fieldoutputbytes also retain ORIGINALinput, rather than an assumed
post-arrayfieldvalue. -/
theorem last_bytes (state : DenoteState) (source head offset : Nat)
    (pastPointer : 96 ≤ source) (before : source + 256 ≤ head) (lo : 128 ≤ offset) (hi : offset < 256) :
    (completed state source head).world.physicalByte (head + 32 + offset) =
      state.world.physicalByte (source + offset) := by
  have bytes := written_byte (arrayCompleted state source head) source head offset lastEntries
    (by intro entry belongs; simp only [lastEntries, List.mem_cons, List.not_mem_nil, or_false] at belongs
        rcases belongs with rfl | rfl | rfl | rfl <;> omega) (by
      by_cases a : offset < 160
      · exact ⟨("_verity_slice_tmp_15", 128), by simp [lastEntries], by omega⟩
      by_cases b : offset < 192
      · exact ⟨("_verity_slice_tmp_16", 160), by simp [lastEntries], by omega⟩
      by_cases c : offset < 224
      · exact ⟨("_verity_slice_tmp_17", 192), by simp [lastEntries], by omega⟩
      · exact ⟨("_verity_slice_tmp_18", 224), by simp [lastEntries], by omega⟩)
  exact bytes.trans (array_input_byte state source head (source + offset) (by omega) (by omega))

def wordByte (value offset : Nat) : Byte :=
  valueWord (Verity.Core.Uint256.ofNat value) ⟨offset % 32, Nat.mod_lt _ (by decide)⟩

def abiByte (state : DenoteState) (source offset : Nat) : Byte :=
  if offset < 32 then wordByte 32 offset
  else if offset < 128 then state.world.physicalByte (source + (offset - 32))
  else if offset < 160 then wordByte 256 (offset - 128)
  else if offset < 288 then state.world.physicalByte (source + (offset - 32))
  else if offset < 320 then wordByte (ImportedCreationArrayDescriptors.count state source) (offset - 288)
  else state.world.physicalByte (ImportedAbiArray.sourceAt state.world
    (ImportedCreationArrayDescriptors.pointer state source + 32) ((offset - 320) / 128) + (offset - 320) % 128)

def payloadSize (state : DenoteState) (source : Nat) : Nat := 320 + 128 * ImportedCreationArrayDescriptors.count state source

def abiBytes (state : DenoteState) (source : Nat) : ByteArray :=
  ⟨((List.range (payloadSize state source)).map fun offset => UInt8.ofNat (abiByte state source offset).val).toArray⟩

/-- A coherent complete word observation determines ALL of its physical bytes. -/
theorem word_byte (world : Verity.ContractState) (query value offset : Nat)
    (coherent : Coherent world) (word : world.memory query = Verity.Core.Uint256.ofNat value)
    (inside : offset < 32) : world.physicalByte (query + offset) = wordByte value offset := by
  have physical := ImportedAbiWordCopy.load_word world coherent query
  rw [word] at physical
  have byte := (congrFun physical ⟨offset, inside⟩).symm
  simpa only [wordByte, Nat.mod_eq_of_lt inside, Memory.readWord, Verity.ContractState.physicalByte] using byte

theorem completed_coherent (state : DenoteState) (source head : Nat) : Coherent (completed state source head).world := by
  exact ImportedCreationFieldFrames.coherent _ _ _ _ (array_coherent state source head)

/-- Entire320byteABIhead, including bothoffsets, all7staticfields and the count. -/
theorem static_bytes (state : DenoteState) (source head offset : Nat)
    (pastPointer : 96 ≤ source) (before : source + 256 ≤ head) (inside : offset < 320) :
    (completed state source head).world.physicalByte (head + offset) = abiByte state source offset := by
  by_cases root : offset < 32
  · rw [abiByte, if_pos root]
    exact word_byte _ head 32 offset (completed_coherent state source head) (root_word state source head (by omega)) root
  rw [abiByte, if_neg root]
  by_cases first : offset < 128
  · rw [if_pos first]
    have address : head + offset = head + 32 + (offset - 32) := by omega
    rw [address]
    exact first_bytes state source head (offset - 32) pastPointer before (by omega)
  rw [if_neg first]
  by_cases middle : offset < 160
  · rw [if_pos middle]
    have address : head + offset = head + 128 + (offset - 128) := by omega
    rw [address]
    exact word_byte _ (head + 128) 256 (offset - 128) (completed_coherent state source head) (offset_word state source head) (by omega)
  rw [if_neg middle]
  by_cases last : offset < 288
  · rw [if_pos last]
    have address : head + offset = head + 32 + (offset - 32) := by omega
    rw [address]
    exact last_bytes state source head (offset - 32) pastPointer before (by omega) (by omega)
  rw [if_neg last, if_pos inside]
  have address : head + offset = head + 288 + (offset - 288) := by omega
  rw [address]
  exact word_byte _ (head + 288) (ImportedCreationArrayDescriptors.count state source) (offset - 288)
    (completed_coherent state source head) (length_word state source head) (by omega)

/-- EVERYbyte of the complete variable-size payload is derived from actual
execution. The RHS contains only ORIGINALencoder-entry memory/words. -/
theorem payload_bytes (state : DenoteState) (source head offset : Nat) (coherent : Coherent state.world)
    (pastPointer : 96 ≤ source) (before : source + 256 ≤ head)
    (arrayPast : 96 ≤ ImportedCreationArrayDescriptors.pointer state source)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 +
      32 * ImportedCreationArrayDescriptors.count state source ≤ head)
    (sources : ∀ i < ImportedCreationArrayDescriptors.count state source,
      96 ≤ ImportedAbiArray.sourceAt state.world (ImportedCreationArrayDescriptors.pointer state source + 32) i ∧
      ImportedAbiArray.sourceAt state.world (ImportedCreationArrayDescriptors.pointer state source + 32) i + 128 ≤ head)
    (inside : offset < payloadSize state source) :
    (completed state source head).world.physicalByte (head + offset) = abiByte state source offset := by
  by_cases static : offset < 320
  · exact static_bytes state source head offset pastPointer before static
  · have index : (offset - 320) / 128 < ImportedCreationArrayDescriptors.count state source := by
      unfold payloadSize at inside
      omega
    have address : head + offset = head + 320 + 128 * ((offset - 320) / 128) + (offset - 320) % 128 := by
      have := Nat.mod_add_div (offset - 320) 128
      omega
    have expected : abiByte state source offset = state.world.physicalByte (ImportedAbiArray.sourceAt state.world
        (ImportedCreationArrayDescriptors.pointer state source + 32) ((offset - 320) / 128) + (offset - 320) % 128) := by
      simp only [abiByte, if_neg (show ¬ offset < 32 from by omega), if_neg (show ¬ offset < 128 from by omega),
        if_neg (show ¬ offset < 160 from by omega), if_neg (show ¬ offset < 288 from by omega), if_neg static]
    rw [expected, address]
    exact completed_array_bytes state source head coherent arrayPast arrayBefore sources
      ⟨_, index⟩ ⟨_, Nat.mod_lt _ (by decide)⟩

/-- Exact fullByteArrayequality, with no supplied target buffer or trace. -/
theorem payload_code (state : DenoteState) (source head : Nat) (coherent : Coherent state.world)
    (pastPointer : 96 ≤ source) (before : source + 256 ≤ head)
    (arrayPast : 96 ≤ ImportedCreationArrayDescriptors.pointer state source)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 +
      32 * ImportedCreationArrayDescriptors.count state source ≤ head)
    (sources : ∀ i < ImportedCreationArrayDescriptors.count state source,
      96 ≤ ImportedAbiArray.sourceAt state.world (ImportedCreationArrayDescriptors.pointer state source + 32) i ∧
      ImportedAbiArray.sourceAt state.world (ImportedCreationArrayDescriptors.pointer state source + 32) i + 128 ≤ head) :
    Verity.Core.Model.Create2.physicalInitcodeBytes (completed state source head).world head (payloadSize state source) = abiBytes state source := by
  apply congrArg (fun bytes : List UInt8 => (⟨bytes.toArray⟩ : ByteArray))
  apply List.map_congr_left
  intro offset belongs
  exact congrArg (fun byte : Byte => UInt8.ofNat byte.val)
    (payload_bytes state source head offset coherent pastPointer before arrayPast arrayBefore sources (List.mem_range.mp belongs))

end Contracts.SolidityImportSmoke.ImportedCreationAbiLayout
