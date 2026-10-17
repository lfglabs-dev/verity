import Compiler.Proofs.IRGeneration.NativeSourcePackedReturnFrame

namespace Compiler.Proofs.IRGeneration.NativeSourcePayloadReturn
open EvmYul NativeSourceFirstPayloadSurvival

theorem copy_monotone (memory : ByteArray) (dest source size : Nat)
    (sourceInside : source + size ≤ memory.size)
    (padding : dest - memory.size < 2 ^ System.Platform.numBits) :
    memory.size ≤ (memory.write source memory dest size).size := by
  by_cases zero : size = 0
  · subst size
    rw [NativeSourceEmptyCopy.write_zero]
  · rw [NativeSourceMcopyGrowth.write_snapshot memory dest source size (by omega) sourceInside padding]
    rw [ByteArray.size_write _ memory dest size (by omega) (by rw [ByteArray.size_extract]; omega) padding]
    exact Nat.le_max_left _ _

theorem packed_monotone (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (sourceInside : c.toNat + ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b).toNat ≤
      (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size) :
    pre.memory.size ≤ (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size := by
  have copyPadding : ((e + length) + d).toNat -
      (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits := by
    rw [NativeSourceIntercopyCarrier.loaded_size cost pre length b c d e f g dest x y tail padding]
    rw [Nat.sub_eq_zero_of_le (Nat.le_trans (by omega) (Nat.le_max_right _ _))]
    exact Nat.two_pow_pos _
  have before := NativeSourceSecondPackingFrame.loaded_monotone cost pre length b c d e f g dest x y tail padding
  unfold NativeSourceSecondPacking.packed
  rw [NativeSourceFirstCopyProvenance.second_copied_memory]
  exact before.trans (copy_monotone _ _ _ _ sourceInside copyPadding)

theorem readback (original : ByteArray) (cost : Nat) (pre : EVM.State)
    (length a b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (positive : 0 < length.toNat) (bounded : length.toNat < 2 ^ 64)
    (originalInside : a.toNat + length.toNat ≤ original.size)
    (sourceInside : a.toNat + length.toNat ≤ pre.memory.size)
    (firstPadding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (preserved : pre.memory.readWithPadding a.toNat length.toNat = original.readWithPadding a.toNat length.toNat)
    (padding : ((e + length) + d).toNat - (first cost pre length a b c d e f g dest (x :: y :: tail)).memory.size < 2 ^ System.Platform.numBits)
    (secondSource : c.toNat + ((NativeSourceSecondCopyStore.stored cost
      (first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).toMachineState.lookupMemory b).toNat ≤
      (NativeSourceSecondCopyStore.loaded cost (first cost pre length a b c d e f g dest (x :: y :: tail))
        length b c d e f g dest x y tail).memory.size)
    (finalPadding : (NativeSourceFinalSizeContext.finish cost (first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).toNat - (NativeSourceSecondPacking.packed cost (first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits)
    (finalBelow : dest.toNat + length.toNat ≤ (NativeSourceFinalSizeContext.finish cost (first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).toNat)
    (finalAbove : g.toNat + 32 ≤ dest.toNat) (allocatorAbove : 96 ≤ dest.toNat)
    (below : dest.toNat + length.toNat ≤ ((e + length) + d).toNat) :
    (NativeSourcePackedAllocation.returned cost (first cost pre length a b c d e f g dest (x :: y :: tail))
      length b c d e f g dest x y tail).memory.readWithPadding dest.toNat length.toNat =
      original.extract a.toNat (a.toNat + length.toNat) := by
  have finalInside : dest.toNat + length.toNat ≤
      (NativeSourceSecondPacking.packed cost (first cost pre length a b c d e f g dest (x :: y :: tail))
        length b c d e f g dest x y tail).memory.size := by
    have firstInside : dest.toNat + length.toNat ≤ (first cost pre length a b c d e f g dest (x :: y :: tail)).memory.size := by
      rw [first_size cost pre length a b c d e f g dest (x :: y :: tail) positive sourceInside firstPadding]
      exact Nat.le_max_right _ _
    exact firstInside.trans (packed_monotone cost _ length b c d e f g dest x y tail padding secondSource)
  rw [NativeSourcePackedReturnFrame.preserve cost (first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail dest.toNat length.toNat
    finalPadding positive bounded finalInside finalBelow finalAbove allocatorAbove]
  exact NativeSourceFirstPayloadSurvival.readback original cost pre length a b c d e f g dest x y tail
    positive bounded originalInside sourceInside firstPadding preserved padding secondSource below

end Compiler.Proofs.IRGeneration.NativeSourcePayloadReturn
