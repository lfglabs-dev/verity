import Compiler.Proofs.IRGeneration.NativeSourcePreludeCopySize

namespace Compiler.Proofs.IRGeneration.NativeSourceContextCopySize
open EvmYul NativeSourceContextCopy

theorem size (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256)
    (tail : Stack UInt256)
    (positive : 0 < (length cost pre a b c d e f g h i j k z tail).toNat)
    (source : i.toNat + (length cost pre a b c d e f g h i j k z tail).toNat ≤
      (entry cost pre a b c d e f g h i j k z tail).memory.size)
    (padding : (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat -
      (entry cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits) :
    (copied cost pre a b c d e f g h i j k z tail).memory.size =
      max (entry cost pre a b c d e f g h i j k z tail).memory.size
        ((free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat +
          (length cost pre a b c d e f g h i j k z tail).toNat) := by
  exact NativeSourcePreludeCopySize.decoded_size cost _ h (UInt256.ofNat 32) i
    (UInt256.ofNat 681) j k (UInt256.ofNat 0) z tail positive source padding

theorem inside (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256)
    (tail : Stack UInt256)
    (positive : 0 < (length cost pre a b c d e f g h i j k z tail).toNat)
    (source : i.toNat + (length cost pre a b c d e f g h i j k z tail).toNat ≤
      (entry cost pre a b c d e f g h i j k z tail).memory.size)
    (padding : (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat -
      (entry cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits) :
    (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat +
      (length cost pre a b c d e f g h i j k z tail).toNat ≤
      (copied cost pre a b c d e f g h i j k z tail).memory.size := by
  rw [size cost pre a b c d e f g h i j k z tail positive source padding]
  exact Nat.le_max_right _ _

end Compiler.Proofs.IRGeneration.NativeSourceContextCopySize
