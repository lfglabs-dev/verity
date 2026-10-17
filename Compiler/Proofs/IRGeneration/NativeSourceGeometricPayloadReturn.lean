import Compiler.Proofs.IRGeneration.NativeSourceFirstOutputGeometry
namespace Compiler.Proofs.IRGeneration.NativeSourceGeometricPayloadReturn
open EvmYul
theorem preserve (cost : Nat) (pre : EVM.State) (length b c base f x y : UInt256)
    (tail : Stack UInt256) (bounded : length.toNat < 2 ^ 64)
    (inside : (base + UInt256.ofNat 32).toNat + length.toNat ≤ pre.memory.size)
    (padding : ((base + length) + (UInt256.ofNat 32)).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (secondSource : c.toNat + ((NativeSourceSecondCopyStore.stored cost pre length b c (UInt256.ofNat 32) base f base (base + UInt256.ofNat 32) x y tail).toMachineState.lookupMemory b).toNat ≤
      (NativeSourceSecondCopyStore.loaded cost pre length b c (UInt256.ofNat 32) base f base (base + UInt256.ofNat 32) x y tail).memory.size)
    (finalPadding : (NativeSourceFinalSizeContext.finish cost pre length b c (UInt256.ofNat 32) base f base (base + UInt256.ofNat 32) x y tail).toNat -
      (NativeSourceSecondPacking.packed cost pre length b c (UInt256.ofNat 32) base f base (base + UInt256.ofNat 32) x y tail).memory.size < 2 ^ System.Platform.numBits)
    (above : 64 ≤ base.toNat)
    (endFits : ((base.toNat + length.toNat) +
      (NativeSourcePackedRequested.amount cost pre length b c (UInt256.ofNat 32) base f base
        (base + UInt256.ofNat 32) x y tail).toNat) + 32 < 2 ^ 256) :
    (NativeSourcePackedAllocation.returned cost pre length b c (UInt256.ofNat 32) base f base (base + UInt256.ofNat 32) x y tail).memory.readWithPadding (base + UInt256.ofNat 32).toNat length.toNat =
      pre.memory.readWithPadding (base + UInt256.ofNat 32).toNat length.toNat := by
  have outputFits : base.toNat + 32 < 2 ^ 256 := by omega
  have below := NativeSourceFirstOutputGeometry.output_below_second base length (by omega)
  have finalBound := NativeSourceAddressGeometry.final_bound base length (UInt256.ofNat 32)
    (NativeSourcePackedRequested.amount cost pre length b c (UInt256.ofNat 32) base f base
      (base + UInt256.ofNat 32) x y tail) endFits
  have finalBelow : (base + UInt256.ofNat 32).toNat + length.toNat ≤
      (NativeSourceFinalSizeContext.finish cost pre length b c (UInt256.ofNat 32) base f base
        (base + UInt256.ofNat 32) x y tail).toNat := by
    exact below.trans ((Nat.le_add_right _ _).trans finalBound)
  exact NativeSourceCopiedPayloadReturn.preserve cost pre length b c (UInt256.ofNat 32) base f base
    (base + UInt256.ofNat 32) x y tail bounded inside padding secondSource below finalPadding finalBelow
    (NativeSourceFirstOutputGeometry.output_above base outputFits)
    (NativeSourceFirstOutputGeometry.output_allocator base above outputFits)

end Compiler.Proofs.IRGeneration.NativeSourceGeometricPayloadReturn
