import Compiler.Proofs.IRGeneration.NativeSourceTotalCopyFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceIntercopyStoreFrame
open EvmYul

theorem head_memory (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceSecondCopyHead.s9 cost pre length b c d e f g dest x y tail).memory = pre.memory := by
  rfl

theorem load_memory (cost : Nat) (pre : EVM.State) (address : UInt256) (rest : Stack UInt256) :
    (NativeSourceLoadStep.loaded cost pre address rest).memory = pre.memory := by
  rfl

theorem stored_memory (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).memory =
      (pre.toMachineState.mstore ((e + length) + d) x).memory := by
  rfl

theorem read_below (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (start count : Nat)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (inside : start + count ≤ pre.memory.size) (below : start + count ≤ ((e + length) + d).toNat) :
    (NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).memory.readWithPadding start count =
      pre.memory.readWithPadding start count := by
  rw [stored_memory]
  exact NativeSourceStoreFrame.read_below pre.toMachineState ((e + length) + d) x start count
    padding positive bounded inside below

theorem loaded_read_below (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (start count : Nat)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (inside : start + count ≤ pre.memory.size) (below : start + count ≤ ((e + length) + d).toNat) :
    (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.readWithPadding start count =
      pre.memory.readWithPadding start count := by
  unfold NativeSourceSecondCopyStore.loaded
  rw [load_memory]
  exact read_below cost pre length b c d e f g dest x y tail start count padding positive bounded inside below

end Compiler.Proofs.IRGeneration.NativeSourceIntercopyStoreFrame
