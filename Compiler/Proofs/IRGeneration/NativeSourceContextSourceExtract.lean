import Compiler.Proofs.IRGeneration.NativeSourceContextEncodedReadback

namespace Compiler.Proofs.IRGeneration.NativeSourceContextSourceExtract
open EvmYul

theorem allocator_extract (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (start length : Nat) (bounded : length < 2 ^ 64) (above : 96 ≤ start)
    (inside : start + length ≤ (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size) :
    (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.extract start (start + length) = (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k (z :: tail)).memory.extract start (start + length) := by
  by_cases zero : length = 0
  · subst length
    rw [NativeSourceEmptyPayload.extract_zero, NativeSourceEmptyPayload.extract_zero]
  · have positive : 0 < length := by omega
    have fits : 96 ≤ (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size := by omega
    have size := NativeSourceAllocatorCarrier.context_size cost pre a b c d e f g h i j k (z :: tail) fits
    have frame := NativeSourceFirstAllocatorFrame.context_read_above cost pre a b c d e f g h i j k (z :: tail)
      start length positive bounded above inside
    have entryInside : start + length ≤ (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size := by rw [size]; exact inside
    exact (ByteArray.readWithPadding_eq_extract _ _ _ positive bounded entryInside).symm.trans
      (frame.trans (ByteArray.readWithPadding_eq_extract _ _ _ positive bounded inside))

theorem readback (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (firstSource : i.toNat + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat ≤ (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size)
    (firstPadding : ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat - (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits)
    (firstBelow : h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat ≤ ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat)
    (bounded : (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat < 2 ^ 64)
    (storePadding : (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat - (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits)
    (below : h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat ≤ (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat)
    (endBound : ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail)).toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat + (UInt256.ofNat 32).toNat < 2 ^ 256)
    (above : (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail).toNat + 32 ≤ (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat)
    (allocatorAbove : 96 ≤ (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat)
    (sourceAbove : 96 ≤ h.toNat)
    (sizedInside : h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat ≤ (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size) :
    (NativeSourcePackedAllocation.returned cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).memory.readWithPadding (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat = (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k (z :: tail)).memory.extract h.toNat (h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat) := by
  have fits : 96 ≤ (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size := by omega
  have sourceInside : h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat ≤
      (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size := by
    rw [NativeSourceAllocatorCarrier.context_size cost pre a b c d e f g h i j k (z :: tail) fits]
    exact sizedInside
  have bytes := NativeSourceContextSecondPayloadBytes.readback cost pre a b c d e f g h i j k z tail
    firstSource firstPadding firstBelow bounded sourceInside storePadding below endBound above allocatorAbove
  exact bytes.trans (allocator_extract cost pre a b c d e f g h i j k z tail h.toNat (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat bounded sourceAbove sizedInside)

end Compiler.Proofs.IRGeneration.NativeSourceContextSourceExtract
