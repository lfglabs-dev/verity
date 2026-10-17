import Compiler.Proofs.IRGeneration.NativeSourceTwoCopySecondPayload
import Compiler.Proofs.IRGeneration.NativeSourceContextPacked

namespace Compiler.Proofs.IRGeneration.NativeSourceContextSecondPayloadBytes
open EvmYul

theorem decoded_memory (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) :
    (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail).memory = pre.memory.write c.toNat pre.memory
      (NativeSourceDecodedPackingStart.free cost pre + b).toNat
      (NativeSourceDecodedCopyProvenance.length cost pre a b c d e f g h tail).toNat := by
  unfold NativeSourceDecodedPackingStart.copied NativeSourcePreludeCopy.copied
  rw [NativeSourceFirstCopyProvenance.copied_memory, NativeSourceDecodedCopyProvenance.entry_memory]

theorem copied_memory (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256) :
    (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory = (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.write i.toNat (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat := by
  exact decoded_memory cost (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k (UInt256.ofNat 0) z tail

theorem readback (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (firstSource : i.toNat + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat ≤ (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size)
    (firstPadding : ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat - (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits)
    (firstBelow : h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat ≤ ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat)
    (bounded : (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat < 2 ^ 64)
    (sourceInside : h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat ≤ (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size)
    (storePadding : (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat - (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits)
    (below : h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat ≤ (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat)
    (endBound : ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail)).toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat + (UInt256.ofNat 32).toNat < 2 ^ 256)
    (above : (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail).toNat + 32 ≤ (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat)
    (allocatorAbove : 96 ≤ (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat) :
    (NativeSourcePackedAllocation.returned cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).memory.readWithPadding (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat = (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.extract h.toNat (h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat) := by
  have preserved : (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.readWithPadding h.toNat (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat = (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.readWithPadding h.toNat (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat := by
    rw [copied_memory]
    exact NativeSourceFirstCopySourceWindow.preserving_read_below _ _ _ _ _ _ firstSource firstPadding bounded sourceInside firstBelow
  have monotone : (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size ≤ (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.size := by
    rw [copied_memory]
    exact NativeSourcePayloadReturn.copy_monotone _ _ _ _ firstSource firstPadding
  exact NativeSourceSecondPayloadOriginalTotal.readback (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail
    bounded sourceInside (sourceInside.trans monotone) storePadding preserved below endBound above allocatorAbove

end Compiler.Proofs.IRGeneration.NativeSourceContextSecondPayloadBytes

