import Verity.Core
import Verity.Core.Model.ByteMemoryRoundtrip

/-! Physical byte-memory/world bridge. These APIs are preparation for canonical
Denote/source memory integration. They are not used by existing statements yet,
and do not admit raw Yul pointers, CREATE2 or overlapping memory in the importer.
The legacy word observation is recomputed from byte memory, never approximated.
A caller preserving pre-existing word observations must supply Coherent. -/
namespace Compiler.CompilationModel.PhysicalMemory

open Verity.Core
open DenoteMemory

def Coherent (world : Verity.ContractState) : Prop :=
  ∀ offset, world.memory offset = wordValue (world.byteMemory.readWord offset)

end Compiler.CompilationModel.PhysicalMemory

namespace Verity.ContractState

open Compiler.CompilationModel.DenoteMemory

/-- Install an explicit physical memory and its complete, overlapping word view.
This is a replacement operation, not a reconstruction from a legacy word map. -/
def installPhysicalMemory (world : ContractState) (memory : Memory) : ContractState :=
  { world with byteMemory := memory, memory := fun offset => wordValue (memory.readWord offset) }

def writePhysicalMemoryWord (world : ContractState) (offset : Nat) (word : Word) : ContractState :=
  world.installPhysicalMemory (world.byteMemory.writeWord offset word)

def writePhysicalMemoryValue (world : ContractState) (offset : Nat) (value : Verity.Core.Uint256) : ContractState :=
  world.writePhysicalMemoryWord offset (valueWord value)

def writePhysicalMemoryByte (world : ContractState) (offset : Nat) (byte : Byte) : ContractState :=
  world.installPhysicalMemory (world.byteMemory.writeByte offset byte)

def copyPhysicalMemory (world : ContractState) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) : ContractState :=
  world.installPhysicalMemory (world.byteMemory.copyFrom source destOffset sourceOffset size)

def physicalByte (world : ContractState) (offset : Nat) : Byte :=
  world.byteMemory.readByte offset

end Verity.ContractState

namespace Compiler.CompilationModel.PhysicalMemory

open Verity.Core
open DenoteMemory

theorem installPhysicalMemory_identity (world : Verity.ContractState)
    (coherent : Coherent world) :
    world.installPhysicalMemory world.byteMemory = world := by
  have words : (fun offset => wordValue (world.byteMemory.readWord offset)) = world.memory :=
    funext fun offset => (coherent offset).symm
  unfold Verity.ContractState.installPhysicalMemory
  rw [words]

theorem copyPhysicalMemory_zero (world : Verity.ContractState) (source : Nat → Byte)
    (destOffset sourceOffset : Nat) (coherent : Coherent world) :
    world.copyPhysicalMemory source destOffset sourceOffset 0 = world := by
  unfold Verity.ContractState.copyPhysicalMemory
  rw [Memory.copyFrom_zero]
  exact installPhysicalMemory_identity world coherent

theorem installPhysicalMemory_coherent (world : Verity.ContractState) (memory : Memory) :
    Coherent (world.installPhysicalMemory memory) := by
  intro offset
  rfl

theorem writePhysicalMemoryWord_coherent (world : Verity.ContractState) (offset : Nat) (word : Word) :
    Coherent (world.writePhysicalMemoryWord offset word) :=
  installPhysicalMemory_coherent _ _

theorem writePhysicalMemoryByte_coherent (world : Verity.ContractState) (offset : Nat) (byte : Byte) :
    Coherent (world.writePhysicalMemoryByte offset byte) :=
  installPhysicalMemory_coherent _ _

theorem copyPhysicalMemory_coherent (world : Verity.ContractState) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) :
    Coherent (world.copyPhysicalMemory source destOffset sourceOffset size) :=
  installPhysicalMemory_coherent _ _

theorem writePhysicalMemoryWord_at (world : Verity.ContractState) (offset : Nat) (word : Word) :
    (world.writePhysicalMemoryWord offset word).memory offset = wordValue word := by
  change wordValue ((world.byteMemory.writeWord offset word).readWord offset) = _
  rw [Memory.readWord_writeWord_at]

theorem writePhysicalMemoryValue_at (world : Verity.ContractState) (offset : Nat)
    (value : Uint256) :
    (world.writePhysicalMemoryValue offset value).memory offset = value := by
  unfold Verity.ContractState.writePhysicalMemoryValue
  rw [writePhysicalMemoryWord_at, wordValue_valueWord]

theorem writePhysicalMemoryValue_byte_at (world : Verity.ContractState)
    (offset : Nat) (value : Uint256) (index : Fin 32) :
    (world.writePhysicalMemoryValue offset value).physicalByte (offset + index.val) =
      (valueWord value) index := by
  unfold Verity.ContractState.writePhysicalMemoryValue
    Verity.ContractState.writePhysicalMemoryWord
    Verity.ContractState.physicalByte
  exact Memory.readByte_writeWord_at world.byteMemory offset (valueWord value) index

theorem writePhysicalMemoryValue_byte_outside (world : Verity.ContractState)
    (offset : Nat) (value : Uint256) (query : Nat)
    (outside : query < offset ∨ offset + 32 ≤ query) :
    (world.writePhysicalMemoryValue offset value).physicalByte query =
      world.physicalByte query := by
  unfold Verity.ContractState.writePhysicalMemoryValue
    Verity.ContractState.writePhysicalMemoryWord
    Verity.ContractState.physicalByte
  exact Memory.readByte_writeWord_outside world.byteMemory offset (valueWord value) query outside

def PhysicalZeroPrefix (initial world : Verity.ContractState)
    (base count : Nat) : Prop :=
  ∀ query, world.physicalByte query =
    if base ≤ query ∧ query < base + 32 * count then
      zeroByte else initial.physicalByte query

theorem physicalZeroPrefix_step (initial world : Verity.ContractState)
    (base count : Nat) (copied : PhysicalZeroPrefix initial world base count) :
    PhysicalZeroPrefix initial
      (world.writePhysicalMemoryValue (base + 32 * count) (Uint256.ofNat 0))
      base (count + 1) := by
  intro query
  by_cases inside : base ≤ query ∧ query < base + 32 * count
  · rw [writePhysicalMemoryValue_byte_outside world _ _ query (by omega), copied]
    by_cases hnew : base ≤ query ∧ query < base + 32 * (count + 1)
    · simp only [if_pos inside, if_pos hnew]
    · omega
  · by_cases current : base + 32 * count ≤ query ∧ query < base + 32 * (count + 1)
    · have lower : query ≥ base + 32 * count := current.1
      have upper : query < base + 32 * count + 32 := by omega
      let index : Fin 32 := ⟨query - (base + 32 * count), by omega⟩
      have hquery : query = base + 32 * count + index.val := by
        dsimp [index]
        omega
      have written := writePhysicalMemoryValue_byte_at world
        (base + 32 * count) (Uint256.ofNat 0) index
      have cond : base ≤ query ∧ query < base + 32 * (count + 1) := by omega
      rw [if_pos cond]
      calc
        (world.writePhysicalMemoryValue (base + 32 * count) (Uint256.ofNat 0)).physicalByte query =
            (valueWord (Uint256.ofNat 0)) index := by simpa [hquery] using written
        _ = zeroByte := by
          apply Fin.ext
          simp [valueWord, zeroByte]
    · have outside : query < base + 32 * count ∨ base + 32 * count + 32 ≤ query := by omega
      rw [writePhysicalMemoryValue_byte_outside world _ _ query outside, copied]
      have hnew : ¬ (base ≤ query ∧ query < base + 32 * (count + 1)) := by omega
      simp only [if_neg inside, if_neg hnew]

theorem writePhysicalMemoryByte_at (world : Verity.ContractState) (offset : Nat)
    (byte : Byte) :
    (world.writePhysicalMemoryByte offset byte).byteMemory.readByte offset = byte := by
  unfold Verity.ContractState.writePhysicalMemoryByte
    Verity.ContractState.installPhysicalMemory
  have hcover := expandedLength_covers (offset + 1)
  have hsize : expandedLength (offset + 1) ≤
      (world.byteMemory.expand (offset + 1)).size := by
    exact Nat.le_max_right _ _
  simp [Memory.readByte, Memory.writeByte]
  omega

@[simp] theorem physicalByte_writePhysicalMemoryByte (world : Verity.ContractState)
    (offset : Nat) (byte : Byte) :
    Verity.ContractState.physicalByte
      (world.writePhysicalMemoryByte offset byte) offset = byte := by
  exact writePhysicalMemoryByte_at world offset byte

/-- Byte insertion preserves every other byte, including overlapping word views. -/
theorem physicalByte_writePhysicalMemoryByte_outside (world : Verity.ContractState)
    (offset : Nat) (byte : Byte) (query : Nat) (outside : query ≠ offset) :
    (world.writePhysicalMemoryByte offset byte).physicalByte query =
      world.physicalByte query := by
  exact Memory.readByte_writeByte_outside world.byteMemory offset byte query outside

/-- Physical copy observation: the copied prefix is exact and all other bytes
retain their initial values. This does not assume an aligned word-grid model. -/
def PhysicalCopyPrefix (initial world : Verity.ContractState) (bytes : Nat → Byte)
    (destination count : Nat) : Prop :=
  ∀ query, world.physicalByte query =
    if destination ≤ query ∧ query < destination + count then
      bytes (query - destination) else initial.physicalByte query

theorem physicalCopyPrefix_zero (initial : Verity.ContractState)
    (bytes : Nat → Byte) (destination : Nat) :
    PhysicalCopyPrefix initial initial bytes destination 0 := by
  intro query
  rw [if_neg (by omega)]

/-- Extending a byte prefix needs no zero-initialization assumption: the
physical write replaces exactly one byte and preserves the full outside frame. -/
theorem physicalCopyPrefix_step (initial world : Verity.ContractState)
    (bytes : Nat → Byte) (destination count : Nat)
    (copied : PhysicalCopyPrefix initial world bytes destination count) :
    PhysicalCopyPrefix initial
      (world.writePhysicalMemoryByte (destination + count) (bytes count))
      bytes destination (count + 1) := by
  intro query
  by_cases current : query = destination + count
  · subst query
    rw [physicalByte_writePhysicalMemoryByte, if_pos (by omega)]
    simp
  · rw [physicalByte_writePhysicalMemoryByte_outside _ _ _ _ current, copied]
    have same : (destination ≤ query ∧ query < destination + count) ↔
        (destination ≤ query ∧ query < destination + (count + 1)) := by omega
    simp only [same]

theorem writePhysicalMemoryValue_coherent (world : Verity.ContractState) (offset : Nat)
    (value : Uint256) : Coherent (world.writePhysicalMemoryValue offset value) :=
  writePhysicalMemoryWord_coherent _ _ _

theorem writePhysicalMemoryWord_outside (world : Verity.ContractState) (offset : Nat) (word : Word)
    (query : Nat) (coherent : Coherent world)
    (disjoint : query + 32 ≤ offset ∨ offset + 32 ≤ query) :
    (world.writePhysicalMemoryWord offset word).memory query = world.memory query := by
  change wordValue ((world.byteMemory.writeWord offset word).readWord query) = _
  rw [Memory.readWord_writeWord_outside _ _ _ _ disjoint]
  exact (coherent query).symm

theorem writePhysicalMemoryValue_aligned_cell
    (world : Verity.ContractState) (offset query : Nat) (value : Uint256)
    (coherent : Coherent world) (aligned : query % 32 = 0)
    (different : query ≠ offset) (disjoint : query + 32 ≤ offset ∨ offset + 32 ≤ query) :
    (world.writePhysicalMemoryValue offset value).memory query = world.memory query := by
  exact writePhysicalMemoryWord_outside world offset (valueWord value) query coherent disjoint

theorem writePhysicalMemoryByte_outside (world : Verity.ContractState) (offset : Nat)
    (byte : Byte) (query : Nat) (coherent : Coherent world)
    (disjoint : query + 32 ≤ offset ∨ offset + 1 ≤ query) :
    (world.writePhysicalMemoryByte offset byte).memory query = world.memory query := by
  change wordValue ((world.byteMemory.writeByte offset byte).readWord query) = _
  rw [Memory.readWord_writeByte_outside _ _ _ _ disjoint]
  exact (coherent query).symm

theorem installPhysicalMemory_storage_frame (world : Verity.ContractState) (memory : Memory) :
    (world.installPhysicalMemory memory).storageWords = world.storageWords := rfl

theorem installPhysicalMemory_selector_frame (world : Verity.ContractState) (memory : Memory) :
    (world.installPhysicalMemory memory).selector = world.selector := rfl

theorem installPhysicalMemory_events_frame (world : Verity.ContractState) (memory : Memory) :
    (world.installPhysicalMemory memory).events = world.events := rfl

theorem installPhysicalMemory_returndata_frame (world : Verity.ContractState) (memory : Memory) :
    (world.installPhysicalMemory memory).returndata = world.returndata := rfl

end Compiler.CompilationModel.PhysicalMemory
