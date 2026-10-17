import Compiler.Proofs.IRGeneration.NativeSourceIntercopyStoreFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceIntercopyCarrier
open EvmYul

theorem stored_size (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).memory.size =
      max pre.memory.size (((e + length) + d).toNat + 32) := by
  rw [NativeSourceIntercopyStoreFrame.stored_memory]
  exact MachineState.size_memory_mstore_of_pad pre.toMachineState ((e + length) + d) x padding

theorem stored_monotone (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    pre.memory.size ≤ (NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).memory.size := by
  rw [stored_size cost pre length b c d e f g dest x y tail padding]
  exact Nat.le_max_left _ _

theorem loaded_size (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size =
      max pre.memory.size (((e + length) + d).toNat + 32) := by
  unfold NativeSourceSecondCopyStore.loaded
  rw [NativeSourceIntercopyStoreFrame.load_memory]
  exact stored_size cost pre length b c d e f g dest x y tail padding

end Compiler.Proofs.IRGeneration.NativeSourceIntercopyCarrier
