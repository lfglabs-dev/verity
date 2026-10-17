import Compiler.Proofs.IRGeneration.NativeSourceContextPreCreate
import EvmYul.EVM.Proof.MemoryStep

namespace Compiler.Proofs.IRGeneration.NativeSourceMemoryFrame
open EvmYul

theorem read_below (machine : MachineState) (address value : UInt256) (start length : Nat)
    (fits : address.toNat + 32 ≤ machine.memory.size) (positive : 0 < length)
    (bounded : length < 2 ^ 64) (below : start + length ≤ address.toNat) :
    (machine.mstore address value).memory.readWithPadding start length =
      machine.memory.readWithPadding start length := by
  exact ByteArray.readWithPadding_write_of_le value.toByteArray machine.memory address.toNat 32 start length
    (by decide) (UInt256.size_toByteArray value) fits positive bounded below

theorem read_above (machine : MachineState) (address value : UInt256) (start length : Nat)
    (fits : address.toNat + 32 ≤ machine.memory.size) (positive : 0 < length)
    (bounded : length < 2 ^ 64) (above : address.toNat + 32 ≤ start)
    (inside : start + length ≤ machine.memory.size) :
    (machine.mstore address value).memory.readWithPadding start length =
      machine.memory.readWithPadding start length := by
  exact ByteArray.readWithPadding_write_of_ge value.toByteArray machine.memory address.toNat 32 start length
    (by decide) (UInt256.size_toByteArray value) fits positive bounded above inside

theorem lookup_of_read (before after : MachineState) (address : UInt256)
    (beforeCarrier : address.toNat < before.memory.size)
    (afterCarrier : address.toNat < after.memory.size)
    (beforeActive : ¬address ≥ before.activeWords * ⟨32⟩)
    (afterActive : ¬address ≥ after.activeWords * ⟨32⟩)
    (bytes : after.memory.readWithPadding address.toNat 32 = before.memory.readWithPadding address.toNat 32) :
    after.lookupMemory address = before.lookupMemory address := by
  unfold MachineState.lookupMemory
  rw [if_neg (not_or_intro (by omega) afterActive), if_neg (not_or_intro (by omega) beforeActive), bytes]

end Compiler.Proofs.IRGeneration.NativeSourceMemoryFrame
