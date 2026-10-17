import Compiler.Proofs.IRGeneration.NativeSourceRoundedCarrier

namespace Compiler.Proofs.IRGeneration.NativeSourcePackedReturnFrame
open EvmYul

theorem preserve (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (start count : Nat)
    (padding : (NativeSourceFinalSizeContext.finish cost pre length b c d e f g dest x y tail).toNat -
      (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (inside : start + count ≤ (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size)
    (below : start + count ≤ (NativeSourceFinalSizeContext.finish cost pre length b c d e f g dest x y tail).toNat)
    (above : g.toNat + 32 ≤ start) (allocatorAbove : 96 ≤ start) :
    (NativeSourcePackedAllocation.returned cost pre length b c d e f g dest x y tail).memory.readWithPadding start count =
      (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.readWithPadding start count := by
  have insideSized : start + count ≤ (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail).memory.size := by
    rw [NativeSourceFinalSizeContext.carrier cost pre length b c d e f g dest x y tail padding]
    exact inside.trans (Nat.le_max_left _ _)
  have insideRounded : start + count ≤ (NativeSourceRoundedSecondCopy.rounded cost pre length b c d e f g dest x y tail).memory.size := by
    rw [NativeSourceRoundedCarrier.context_fits cost pre length b c d e f g dest x y tail start count above insideSized]
    exact insideSized
  rw [NativeSourceSecondAllocatorFrame.packed_read_above cost pre length b c d e f g dest x y tail
    start count positive bounded allocatorAbove insideRounded]
  exact NativeSourceFinalSizeContext.rounded_read cost pre length b c d e f g dest x y tail
    start count padding positive bounded inside below above

theorem operands_memory (cost : Nat) (pre : EVM.State) (pointer offset value salt : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceCreateOperands.s4 cost pre pointer offset value salt tail).memory = pre.memory := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourcePackedReturnFrame
