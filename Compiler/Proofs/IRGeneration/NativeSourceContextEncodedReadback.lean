import Compiler.Proofs.IRGeneration.NativeSourceContextAllocatedBytes
import Compiler.Proofs.IRGeneration.NativeSourceContextSecondPayloadBytes

namespace Compiler.Proofs.IRGeneration.NativeSourceContextEncodedReadback
open EvmYul

def encoded (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256) : ByteArray :=
  (j + NativeSourceAllocatorOverflowEntry.amount (b - c)).toByteArray.write 0
        (((b - c) + UInt256.lnot (UInt256.ofNat 31)).toByteArray.write 0
        ((((NativeSourceThirdField.stored cost pre a b c d e f g h i j k (z :: tail)).toMachineState.lookupMemory g).land a).toByteArray.write 0
          ((((NativeSourceSecondField.stored cost pre a b c d e f g h i j k (z :: tail)).toMachineState.lookupMemory f).land a).toByteArray.write 0
            (((NativeSourceFirstField.stored cost pre a b c d e f g h i j k (z :: tail)).toMachineState.lookupMemory e).toByteArray.write 0
              (((NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k (z :: tail)).toMachineState.lookupMemory d).toByteArray.write 0
                pre.memory (c + UInt256.ofNat 192).toNat 32)
              (c + UInt256.ofNat 224).toNat 32)
            (c + UInt256.ofNat 256).toNat 32)
          (c + UInt256.ofNat 288).toNat 32)
        j.toNat 32) 64 32

theorem entry_memory (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256) :
    (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory = encoded cost pre a b c d e f g h i j k z tail := by
  exact NativeSourceContextAllocatedBytes.encoded_context cost pre a b c d e f g h i j k (z :: tail)

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
    (NativeSourcePackedAllocation.returned cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).memory.readWithPadding (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat = (encoded cost pre a b c d e f g h i j k z tail).extract h.toNat (h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat) := by
  have copied := NativeSourceContextSecondPayloadBytes.readback cost pre a b c d e f g h i j k z tail
    firstSource firstPadding firstBelow bounded sourceInside storePadding below endBound above allocatorAbove
  rw [entry_memory] at copied
  exact copied

end Compiler.Proofs.IRGeneration.NativeSourceContextEncodedReadback
