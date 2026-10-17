import Compiler.Proofs.IRGeneration.NativeSourceAllocatorCarrier

namespace Compiler.Proofs.IRGeneration.NativeSourceContextOriginalCopy
open EvmYul

theorem readback (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256)
    (tail : Stack UInt256) (count : Nat)
    (above : 96 ≤ i.toNat)
    (bounded : count < 2 ^ 64)
    (padding0 : (c + UInt256.ofNat 192).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (inside0 : i.toNat + count ≤ pre.memory.size)
    (below0 : i.toNat + count ≤ (c + UInt256.ofNat 192).toNat)
    (padding1 : (c + UInt256.ofNat 224).toNat - (NativeSourceFirstField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size < 2 ^ System.Platform.numBits)
    (below1 : i.toNat + count ≤ (c + UInt256.ofNat 224).toNat)
    (padding2 : (c + UInt256.ofNat 256).toNat - (NativeSourceSecondField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size < 2 ^ System.Platform.numBits)
    (below2 : i.toNat + count ≤ (c + UInt256.ofNat 256).toNat)
    (padding3 : (c + UInt256.ofNat 288).toNat - (NativeSourceThirdField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size < 2 ^ System.Platform.numBits)
    (below3 : i.toNat + count ≤ (c + UInt256.ofNat 288).toNat)
    (padding4 : j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size < 2 ^ System.Platform.numBits)
    (below4 : i.toNat + count ≤ j.toNat)
    (extent : (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat = count)
    (copyPadding : (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat -
      (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.readWithPadding
      (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat count =
      pre.memory.extract i.toNat (i.toNat + count) := by
  by_cases zero : count = 0
  · rw [zero, NativeSourceEmptyPayload.read_zero, NativeSourceEmptyPayload.extract_zero]
  have positive : 0 < count := by omega
  have inside1 := inside0.trans (NativeSourceContextMemorySize.first cost pre a b c d e f g h i j k (z :: tail) padding0)
  have inside2 := inside1.trans (NativeSourceContextMemorySize.second cost pre a b c d e f g h i j k (z :: tail) padding1)
  have inside3 := inside2.trans (NativeSourceContextMemorySize.third cost pre a b c d e f g h i j k (z :: tail) padding2)
  have inside4 := inside3.trans (NativeSourceContextMemorySize.fourth cost pre a b c d e f g h i j k (z :: tail) padding3)
  have inside5 := inside4.trans (NativeSourceSizeCarrier.context_monotone cost pre a b c d e f g h i j k (z :: tail) padding4)
  have returnedInside : i.toNat + count ≤ (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size := by
    rw [NativeSourceAllocatorCarrier.context_size cost pre a b c d e f g h i j k (z :: tail) (by omega)]
    exact inside5
  have readback := NativeSourceContextCopy.readback cost pre a b c d e f g h i j k z tail
    (by rw [extent]; exact bounded) (by rw [extent]; exact returnedInside) copyPadding
  rw [extent] at readback
  rw [readback]
  apply NativeSourceCopyProvenance.extract_of_read pre.memory _ i.toNat count
    positive bounded inside0 returnedInside
  exact NativeSourceAllocatedWindowFrame.preserve cost pre a b c d e f g h i j k (z :: tail)
    i.toNat count above positive bounded padding0 inside0 below0 padding1 below1 padding2 below2
    padding3 below3 padding4 below4

end Compiler.Proofs.IRGeneration.NativeSourceContextOriginalCopy
