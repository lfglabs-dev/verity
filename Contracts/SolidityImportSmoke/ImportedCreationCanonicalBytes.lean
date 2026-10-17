import Contracts.SolidityImportSmoke.ImportedCreationOriginalBytes

namespace Contracts.SolidityImportSmoke.ImportedCreationCanonicalBytes
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration
open ImportedCreationDecodedPrefix ImportedCreationEncoderEntry ImportedCreationOriginalBytes

def calldataByte (state : DenoteState) (address lane : Nat) : Byte :=
  ImportedCreationAbiLayout.wordByte (ImportedCalldataWord.word state address) lane

theorem static_field (oracle : DenoteOracle) (state : DenoteState) (offset lane : Nat)
    (valid : offset = 0 ∨ offset = 32 ∨ offset = 64 ∨ offset = 128 ∨ offset = 160 ∨ offset = 192 ∨ offset = 224)
    (inside : lane < 32) :
    (completed oracle state).world.physicalByte (128 + offset + lane) =
      calldataByte state (rootPointer state + offset) lane := by
  have reduced : lane % 32 = lane := Nat.mod_eq_of_lt inside
  rcases valid with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [calldataByte, ImportedCreationAbiLayout.wordByte, reduced]
  · exact field0 oracle state ⟨lane, inside⟩
  · exact field32 oracle state ⟨lane, inside⟩
  · exact field64 oracle state ⟨lane, inside⟩
  · exact field128 oracle state ⟨lane, inside⟩
  · exact field160 oracle state ⟨lane, inside⟩
  · exact field192 oracle state ⟨lane, inside⟩
  · exact field224 oracle state ⟨lane, inside⟩

theorem dynamic_byte (oracle : DenoteOracle) (state : DenoteState) (index offset : Nat)
    (live : index < count state) (inside : offset < 128) :
    (completed oracle state).world.physicalByte (free state + index * 128 + offset) =
      calldataByte state (data state + index * 128 + 32 * (offset / 32)) (offset % 32) := by
  have lane : offset % 32 < 32 := Nat.mod_lt _ (by decide)
  have valid : 32 * (offset / 32) = 0 ∨ 32 * (offset / 32) = 32 ∨
      32 * (offset / 32) = 64 ∨ 32 * (offset / 32) = 96 := by omega
  have split : free state + index * 128 + offset =
      free state + index * 128 + 32 * (offset / 32) + offset % 32 := by omega
  rw [split]
  simpa only [calldataByte, ImportedCreationAbiLayout.wordByte, Nat.mod_eq_of_lt lane] using
    element oracle state index _ ⟨offset % 32, lane⟩ live valid

theorem static_byte (oracle : DenoteOracle) (state : DenoteState) (offset : Nat)
    (inside : offset < 96 ∨ (128 ≤ offset ∧ offset < 256)) :
    (completed oracle state).world.physicalByte (128 + offset) =
      calldataByte state (rootPointer state + 32 * (offset / 32)) (offset % 32) := by
  have valid : 32 * (offset / 32) = 0 ∨ 32 * (offset / 32) = 32 ∨
      32 * (offset / 32) = 64 ∨ 32 * (offset / 32) = 128 ∨
      32 * (offset / 32) = 160 ∨ 32 * (offset / 32) = 192 ∨ 32 * (offset / 32) = 224 := by omega
  have split : 128 + offset = 128 + 32 * (offset / 32) + offset % 32 := by omega
  rw [split]
  exact static_field oracle state _ _ valid (Nat.mod_lt _ (by decide))

def abiByte (state : DenoteState) (offset : Nat) : Byte :=
  if offset < 32 then ImportedCreationAbiLayout.wordByte 32 offset
  else if offset < 128 then calldataByte state
    (rootPointer state + 32 * ((offset - 32) / 32)) ((offset - 32) % 32)
  else if offset < 160 then ImportedCreationAbiLayout.wordByte 256 (offset - 128)
  else if offset < 288 then calldataByte state
    (rootPointer state + 32 * ((offset - 32) / 32)) ((offset - 32) % 32)
  else if offset < 320 then ImportedCreationAbiLayout.wordByte (count state) (offset - 288)
  else calldataByte state (data state + ((offset - 320) / 128) * 128 +
    32 * (((offset - 320) % 128) / 32)) (((offset - 320) % 128) % 32)

theorem abi_byte (oracle : DenoteOracle) (state : DenoteState) (offset : Nat)
    (budget : head state ≤ 2^64 - 1) (inside : offset < 320 + 128 * count state) :
    ImportedCreationAbiLayout.abiByte (completed oracle state) 128 offset = abiByte state offset := by
  unfold ImportedCreationAbiLayout.abiByte abiByte
  split_ifs with root first middle last length
  · rfl
  · exact static_byte oracle state (offset - 32) (Or.inl (by omega))
  · rfl
  · exact static_byte oracle state (offset - 32) (Or.inr ⟨by omega, by omega⟩)
  · rw [array_count oracle state budget]
  · rw [array_pointer oracle state]
    have live : (offset - 320) / 128 < count state := by omega
    rw [show 384 + 32 = 416 by decide, source_at oracle state _ live budget]
    exact dynamic_byte oracle state _ _ live (Nat.mod_lt _ (by decide))

def abiBytes (state : DenoteState) : ByteArray :=
  ⟨((List.range (320 + 128 * count state)).map fun offset =>
    UInt8.ofNat (abiByte state offset).val).toArray⟩

theorem abi_bytes (oracle : DenoteOracle) (state : DenoteState)
    (budget : head state ≤ 2^64 - 1) :
    ImportedCreationAbiLayout.abiBytes (completed oracle state) 128 = abiBytes state := by
  have size : ImportedCreationAbiLayout.payloadSize (completed oracle state) 128 =
      320 + 128 * count state := by
    unfold ImportedCreationAbiLayout.payloadSize
    rw [array_count oracle state budget]
  have lists : (List.range (ImportedCreationAbiLayout.payloadSize (completed oracle state) 128)).map
      (fun offset => UInt8.ofNat (ImportedCreationAbiLayout.abiByte (completed oracle state) 128 offset).val) =
      (List.range (320 + 128 * count state)).map (fun offset => UInt8.ofNat (abiByte state offset).val) := by
    rw [size]
    apply List.map_congr_left
    intro offset member
    rw [abi_byte oracle state offset budget (List.mem_range.mp member)]
  exact congrArg (fun bytes : List UInt8 => ByteArray.mk bytes.toArray) lists

theorem execute (oracle : DenoteOracle) (state : DenoteState)
    (headAvailable : 100 ≤ state.world.calldataSize.val)
    (rootOffsetBound : ImportedAbiTupleHead.rawOffset state 0 ≤ 2^64 - 1)
    (tupleAvailable : rootPointer state + 256 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit)
    (canonical32 : ImportedCalldataWord.word state (rootPointer state + 32) < 2^160)
    (canonical64 : ImportedCalldataWord.word state (rootPointer state + 64) < 2^160)
    (offsetBound : ImportedCreationDecoderArrayHead.relative state (rootPointer state) ≤ 2^64 - 1)
    (arrayAvailable : header state + 32 ≤ state.world.calldataSize.val)
    (payloadAvailable : data state + count state * 128 ≤ state.world.calldataSize.val)
    (canonical : ∀ i < count state, ImportedCalldataWord.word state (data state + i * 128) < 2^160 ∧
      ImportedCalldataWord.word state (data state + i * 128 + 96) < 2^160)
    (canonical192 : ImportedCalldataWord.word state (rootPointer state + 192) < 2^160)
    (canonical224 : ImportedCalldataWord.word state (rootPointer state + 224) < 2^160)
    (budget : head state + (320 + 128 * count state) + 32 +
      32 * ((11 + (320 + 128 * count state) + 31) / 32) ≤ 2^64 - 1) :
    ∃ final, execStmtList oracle actualFields state ImportedCreationOriginalExecution.segment = .continue final ∧
      Verity.Core.Model.Create2.physicalInitcodeBytes final.world
        (head state + (320 + 128 * count state) + 32) (11 + (320 + 128 * count state)) =
        ImportedCreationHeaderAllocation.prefixBytes ++
          abiBytes state := by
  obtain ⟨final, run, bytes⟩ := ImportedCreationOriginalExecution.execute oracle state
    headAvailable rootOffsetBound tupleAvailable sizeBound canonical32 canonical64 offsetBound arrayAvailable
    payloadAvailable canonical canonical192 canonical224 budget
  rw [abi_bytes oracle state (by omega)] at bytes
  exact ⟨final, run, bytes⟩

end Contracts.SolidityImportSmoke.ImportedCreationCanonicalBytes
