import Compiler.Proofs.IRGeneration.NativeSourcePackedRequested

namespace Compiler.Proofs.IRGeneration.NativeSourceContextPacked
open EvmYul
open NativeSourceContextCopy

theorem copied_stack (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256)
    (tail : Stack UInt256) :
    (copied cost pre a b c d e f g h i j k z tail).stack =
      length cost pre a b c d e f g h i j k z tail :: j :: h :: UInt256.ofNat 32 ::
      free cost pre a b c d e f g h i j k z tail :: UInt256.ofNat 681 ::
      free cost pre a b c d e f g h i j k z tail ::
      (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32) :: UInt256.ofNat 0 :: z :: tail := by
  rfl

abbrev requested (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256)
    (tail : Stack UInt256) :=
  NativeSourcePackedAllocation.size cost (copied cost pre a b c d e f g h i j k z tail)
    (length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32)
    (free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681)
    (free cost pre a b c d e f g h i j k z tail)
    (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32) (UInt256.ofNat 0) z tail

abbrev second_amount (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256)
    (tail : Stack UInt256) :=
  NativeSourcePackedRequested.amount cost (copied cost pre a b c d e f g h i j k z tail)
    (length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32)
    (free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681)
    (free cost pre a b c d e f g h i j k z tail)
    (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32) (UInt256.ofNat 0) z tail

theorem copy_padding (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256)
    (tail : Stack UInt256) (memory : ByteArray) (platform : 64 ≤ System.Platform.numBits)
    (endBound : (((free cost pre a b c d e f g h i j k z tail).toNat +
      (length cost pre a b c d e f g h i j k z tail).toNat) +
      (second_amount cost pre a b c d e f g h i j k z tail).toNat) + 32 + 31 < 2 ^ 256)
    (guard : NativeSourceAllocatorDecision.flag (free cost pre a b c d e f g h i j k z tail)
      (requested cost pre a b c d e f g h i j k z tail) = ⟨0⟩) :
    (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat - memory.size <
      2 ^ System.Platform.numBits := by
  exact NativeSourcePackedRequested.copy_padding cost _ _ j h (UInt256.ofNat 32) _ (UInt256.ofNat 681)
    _ _ (UInt256.ofNat 0) z tail memory endBound (by decide) platform guard

end Compiler.Proofs.IRGeneration.NativeSourceContextPacked

