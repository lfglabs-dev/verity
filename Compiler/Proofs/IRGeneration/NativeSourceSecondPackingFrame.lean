import Compiler.Proofs.IRGeneration.NativeSourceIntercopyCarrier

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondPackingFrame
open EvmYul

theorem loaded_monotone (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    pre.memory.size ≤ (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size := by
  rw [NativeSourceIntercopyCarrier.loaded_size cost pre length b c d e f g dest x y tail padding]
  exact Nat.le_max_left _ _

theorem read_below (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (start count : Nat)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (copySource : c.toNat + ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b).toNat ≤
      (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (inside : start + count ≤ pre.memory.size) (below : start + count ≤ ((e + length) + d).toNat) :
    (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.readWithPadding start count =
      pre.memory.readWithPadding start count := by
  have copyPadding : ((e + length) + d).toNat -
      (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size <
      2 ^ System.Platform.numBits := by
    rw [NativeSourceIntercopyCarrier.loaded_size cost pre length b c d e f g dest x y tail padding]
    rw [Nat.sub_eq_zero_of_le (Nat.le_trans (by omega) (Nat.le_max_right _ _))]
    exact Nat.two_pow_pos _
  have insideLoaded := inside.trans (loaded_monotone cost pre length b c d e f g dest x y tail padding)
  unfold NativeSourceSecondPacking.packed
  rw [NativeSourceTotalCopyFrame.second_below cost
    (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail)
    ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b)
    ((e + length) + d) (e + length) c (d :: e :: f :: g :: dest :: x :: y :: tail)
    start count copySource copyPadding positive bounded insideLoaded below]
  exact NativeSourceIntercopyStoreFrame.loaded_read_below cost pre length b c d e f g dest x y tail
    start count padding positive bounded inside below

end Compiler.Proofs.IRGeneration.NativeSourceSecondPackingFrame
