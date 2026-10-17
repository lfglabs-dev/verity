import Verity.Core.Model.PhysicalMemory

/-! Exact byte sources and opcode copy updates. Unlike an installation of a
word projection, a zero-length copy must preserve even an incoherent legacy
entry state. Nonempty copies install bytes and every overlapping word read.
The returndata source here is the existing whole-word buffer; raw call receipts
are handled separately at the byte-call boundary. -/
namespace Compiler.CompilationModel.DenoteMemory

def wordListByte (words : List Nat) (offset : Nat) : Byte :=
  valueWord (Verity.Core.Uint256.ofNat (words.getD (offset / 32) 0))
    ⟨offset % 32, Nat.mod_lt _ (by decide)⟩

/-- The real four-byte selector followed by the ABI data, including reads
inside the selector and reads crossing its boundary. -/
def calldataPhysicalByte (selector : Nat) (words : List Nat) (offset : Nat) : Byte :=
  if offset < 4 then
    ⟨selector / 256 ^ (3 - offset) % 256, Nat.mod_lt _ (by decide)⟩
  else wordListByte words (offset - 4)

theorem Memory.readByte_copyFrom_at (memory : Memory) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) (index : Fin size) :
    (memory.copyFrom source destOffset sourceOffset size).readByte (destOffset + index.val) =
      source (sourceOffset + index.val) := by
  have nonzero : size ≠ 0 := by have := index.isLt; omega
  have extent : destOffset + size ≤ (memory.copyFrom source destOffset sourceOffset size).size := by
    simp only [Memory.copyFrom, nonzero, if_false, Memory.expand]
    exact Nat.le_trans (expandedLength_covers _) (Nat.le_max_right _ _)
  have active : destOffset + index.val < (memory.copyFrom source destOffset sourceOffset size).size :=
    Nat.lt_of_lt_of_le (by have := index.isLt; omega) extent
  rw [Memory.readByte, if_pos active]
  exact Memory.copyFrom_at memory source destOffset sourceOffset size index

theorem Memory.readByte_copyFrom_outside (memory : Memory) (source : Nat → Byte)
    (destOffset sourceOffset size query : Nat)
    (outside : query < destOffset ∨ destOffset + size ≤ query) :
    (memory.copyFrom source destOffset sourceOffset size).readByte query = memory.readByte query := by
  by_cases nonzero : size = 0
  · simp only [nonzero, Memory.copyFrom_zero]
  have disjoint : ¬ (destOffset ≤ query ∧ query < destOffset + size) := by omega
  simp only [Memory.copyFrom, nonzero, if_false, Memory.expand, Memory.readByte, disjoint]
  by_cases active : query < memory.size
  · have expandedActive : query < Nat.max memory.size (expandedLength (destOffset + size)) :=
      Nat.lt_of_lt_of_le active (Nat.le_max_left _ _)
    simp [active, expandedActive]
  · simp only [active, if_false]
    split <;> simp

theorem Memory.readWord_copyFrom_outside (memory : Memory) (source : Nat → Byte)
    (destOffset sourceOffset size query : Nat)
    (outside : query + 32 ≤ destOffset ∨ destOffset + size ≤ query) :
    (memory.copyFrom source destOffset sourceOffset size).readWord query = memory.readWord query := by
  funext index
  apply Memory.readByte_copyFrom_outside
  have := index.isLt
  omega

end Compiler.CompilationModel.DenoteMemory

namespace Verity.ContractState
open Compiler.CompilationModel.DenoteMemory

/-- Opcode update, with an unconditional complete-state identity at size zero. -/
def copyPhysicalBytes (world : ContractState) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) : ContractState :=
  if size = 0 then world else world.copyPhysicalMemory source destOffset sourceOffset size

def copyPhysicalCalldata (world : ContractState) (selector destOffset sourceOffset size : Nat) : ContractState :=
  world.copyPhysicalBytes (calldataPhysicalByte selector world.calldata) destOffset sourceOffset size

def copyPhysicalReturndata (world : ContractState) (destOffset sourceOffset size : Nat) : ContractState :=
  world.copyPhysicalBytes (wordListByte world.returndata) destOffset sourceOffset size

@[simp] theorem copyPhysicalBytes_zero (world : ContractState) (source : Nat → Byte)
    (destOffset sourceOffset : Nat) :
    world.copyPhysicalBytes source destOffset sourceOffset 0 = world := rfl

theorem copyPhysicalBytes_memory (world : ContractState) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) (nonzero : size ≠ 0) :
    (world.copyPhysicalBytes source destOffset sourceOffset size).memory =
      fun query => wordValue ((world.byteMemory.copyFrom source destOffset sourceOffset size).readWord query) := by
  simp only [copyPhysicalBytes, nonzero, if_false]
  rfl

theorem copyPhysicalBytes_byteMemory (world : ContractState) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) :
    (world.copyPhysicalBytes source destOffset sourceOffset size).byteMemory =
      world.byteMemory.copyFrom source destOffset sourceOffset size := by
  by_cases nonzero : size = 0
  · simp only [nonzero, copyPhysicalBytes_zero, Memory.copyFrom_zero]
  · simp only [copyPhysicalBytes, nonzero, if_false]
    rfl

/-- Complete frame, erasing only the two memory observations. -/
theorem copyPhysicalBytes_frame (world : ContractState) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) :
    (world.copyPhysicalBytes source destOffset sourceOffset size).installPhysicalMemory Memory.empty =
      world.installPhysicalMemory Memory.empty := by
  by_cases nonzero : size = 0 <;> simp only [copyPhysicalBytes, nonzero, if_true, if_false] <;> rfl

theorem copyPhysicalBytes_at (world : ContractState) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) (index : Fin size) :
    (world.copyPhysicalBytes source destOffset sourceOffset size).physicalByte (destOffset + index.val) =
      source (sourceOffset + index.val) := by
  unfold physicalByte
  rw [copyPhysicalBytes_byteMemory]
  exact Memory.readByte_copyFrom_at _ _ _ _ _ index

theorem copyPhysicalBytes_outside (world : ContractState) (source : Nat → Byte)
    (destOffset sourceOffset size query : Nat)
    (outside : query < destOffset ∨ destOffset + size ≤ query) :
    (world.copyPhysicalBytes source destOffset sourceOffset size).physicalByte query = world.physicalByte query := by
  unfold physicalByte
  rw [copyPhysicalBytes_byteMemory]
  exact Memory.readByte_copyFrom_outside _ _ _ _ _ _ outside

end Verity.ContractState
