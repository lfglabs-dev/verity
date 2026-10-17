import Compiler.Proofs.IRGeneration.NativeSourceContextPaddingReadback

namespace Compiler.Proofs.IRGeneration.NativeSourceCopiedPayloadReturn
open EvmYul

theorem preserve (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (bounded : length.toNat < 2 ^ 64)
    (inside : dest.toNat + length.toNat ≤ pre.memory.size)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (secondSource : c.toNat + ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b).toNat ≤
      (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size)
    (below : dest.toNat + length.toNat ≤ ((e + length) + d).toNat)
    (finalPadding : (NativeSourceFinalSizeContext.finish cost pre length b c d e f g dest x y tail).toNat -
      (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits)
    (finalBelow : dest.toNat + length.toNat ≤ (NativeSourceFinalSizeContext.finish cost pre length b c d e f g dest x y tail).toNat)
    (finalAbove : g.toNat + 32 ≤ dest.toNat) (allocatorAbove : 96 ≤ dest.toNat) :
    (NativeSourcePackedAllocation.returned cost pre length b c d e f g dest x y tail).memory.readWithPadding dest.toNat length.toNat =
      pre.memory.readWithPadding dest.toNat length.toNat := by
  by_cases zero : length.toNat = 0
  · rw [zero, NativeSourceEmptyPayload.read_zero, NativeSourceEmptyPayload.read_zero]
  have positive : 0 < length.toNat := by omega
  have packedInside := inside.trans
    (NativeSourcePayloadReturn.packed_monotone cost pre length b c d e f g dest x y tail padding secondSource)
  rw [NativeSourcePackedReturnFrame.preserve cost pre length b c d e f g dest x y tail
    dest.toNat length.toNat finalPadding positive bounded packedInside finalBelow finalAbove allocatorAbove]
  exact NativeSourceSecondPackingFrame.read_below cost pre length b c d e f g dest x y tail
    dest.toNat length.toNat padding secondSource positive bounded inside below

end Compiler.Proofs.IRGeneration.NativeSourceCopiedPayloadReturn
