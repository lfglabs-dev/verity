import Compiler.Proofs.IRGeneration.NativeSourceCopyCarrierMonotone

namespace Compiler.Proofs.IRGeneration.NativeSourceContextCopyCarrier
open EvmYul NativeSourceContextCopy

theorem prelude_monotone (cost : Nat) (pre : EVM.State)
    (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (inside : c.toNat + (NativeSourcePreludeCopy.length cost pre free a b c d e f g h tail).toNat ≤ pre.memory.size)
    (padding : (free + b).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    pre.memory.size ≤ (NativeSourcePreludeCopy.copied cost cost cost cost cost cost pre free a b c d e f g h tail).memory.size := by
  have growth := NativeSourceCopyCarrierMonotone.first_monotone
    (NativeSourcePreludeCopy.entry cost cost pre free a b c d e f g h tail)
    cost cost cost cost (NativeSourcePreludeCopy.length cost pre free a b c d e f g h tail)
    c e a b free d free (free + b) (g :: h :: tail)
  rw [NativeSourcePreludeCopySize.entry_memory] at growth
  exact growth inside padding

theorem decoded_monotone (cost : Nat) (pre : EVM.State)
    (a b c d e f g h : UInt256) (tail : Stack UInt256)
    (inside : c.toNat + (NativeSourceDecodedCopyProvenance.length cost pre a b c d e f g h tail).toNat ≤ pre.memory.size)
    (padding : (NativeSourceDecodedPackingStart.free cost pre + b).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    pre.memory.size ≤ (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail).memory.size := by
  have growth := prelude_monotone cost (NativeSourceFreePointer.loaded cost pre)
    (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h tail
  rw [NativeSourcePreludeCopySize.loaded_memory] at growth
  exact growth inside padding

theorem monotone (cost : Nat) (pre : EVM.State)
    (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (inside : i.toNat + (length cost pre a b c d e f g h i j k z tail).toNat ≤
      (entry cost pre a b c d e f g h i j k z tail).memory.size)
    (padding : (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat -
      (entry cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits) :
    (entry cost pre a b c d e f g h i j k z tail).memory.size ≤
      (copied cost pre a b c d e f g h i j k z tail).memory.size := by
  exact decoded_monotone cost _ h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k
    (UInt256.ofNat 0) z tail inside padding

theorem sizeword_inside (cost : Nat) (pre : EVM.State)
    (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (above : 64 ≤ j.toNat)
    (sizePadding : j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size < 2 ^ System.Platform.numBits)
    (inside : i.toNat + (length cost pre a b c d e f g h i j k z tail).toNat ≤
      (entry cost pre a b c d e f g h i j k z tail).memory.size)
    (padding : (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat -
      (entry cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits) :
    j.toNat + 32 ≤ (copied cost pre a b c d e f g h i j k z tail).memory.size := by
  exact (NativeSourceSizewordCarrier.returned_inside cost pre a b c d e f g h i j k
    (z :: tail) above sizePadding).trans
    (monotone cost pre a b c d e f g h i j k z tail inside padding)

end Compiler.Proofs.IRGeneration.NativeSourceContextCopyCarrier

