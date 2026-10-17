import Compiler.Proofs.IRGeneration.NativeSourceGrowingFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceStoreFrame
open EvmYul

theorem read_below (machine : MachineState) (address value : UInt256) (start length : Nat)
    (padding : address.toNat - machine.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ machine.memory.size) (below : start + length ≤ address.toNat) :
    (machine.mstore address value).memory.readWithPadding start length =
      machine.memory.readWithPadding start length := by
  by_cases fits : address.toNat + 32 ≤ machine.memory.size
  · exact NativeSourceMemoryFrame.read_below machine address value start length fits positive bounded below
  · exact NativeSourceGrowingFrame.read_below machine address value start length (by omega)
      padding positive bounded inside below

theorem lookup_below (machine : MachineState) (address value read : UInt256)
    (padding : address.toNat - machine.memory.size < 2 ^ System.Platform.numBits)
    (inside : read.toNat + 32 ≤ machine.memory.size) (below : read.toNat + 32 ≤ address.toNat)
    (beforeActive : ¬read ≥ machine.activeWords * ⟨32⟩)
    (afterActive : ¬read ≥ (machine.mstore address value).activeWords * ⟨32⟩) :
    (machine.mstore address value).lookupMemory read = machine.lookupMemory read := by
  have expanded := MachineState.le_size_memory_mstore machine address value padding
  apply NativeSourceMemoryFrame.lookup_of_read machine (machine.mstore address value) read
    (by omega) (by omega) beforeActive afterActive
  exact read_below machine address value read.toNat 32 padding (by decide) (by decide) inside below

end Compiler.Proofs.IRGeneration.NativeSourceStoreFrame
