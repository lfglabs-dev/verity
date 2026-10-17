import Compiler.Proofs.IRGeneration.NativeSourceBoundedSecondPayload

namespace Compiler.Proofs.IRGeneration.NativeSourceTotalFirstPayload
open EvmYul NativeSourceFirstPayloadSurvival

theorem readback (original : ByteArray) (cost : Nat) (pre : EVM.State)
    (length a b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (bounded : length.toNat < 2 ^ 64)
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
  by_cases zero : length.toNat = 0
  · rw [zero, NativeSourceEmptyPayload.read_zero, NativeSourceEmptyPayload.extract_zero]
  · exact NativeSourcePayloadReturn.readback original cost pre length a b c d e f g dest x y tail
      (by omega) bounded originalInside sourceInside firstPadding preserved padding secondSource
      finalPadding finalBelow finalAbove allocatorAbove below

end Compiler.Proofs.IRGeneration.NativeSourceTotalFirstPayload
