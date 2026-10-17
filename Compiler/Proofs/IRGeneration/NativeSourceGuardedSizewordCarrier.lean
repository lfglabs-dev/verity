import Compiler.Proofs.IRGeneration.NativeSourceContextCopyCarrier

namespace Compiler.Proofs.IRGeneration.NativeSourceGuardedSizewordCarrier
open EvmYul NativeSourceContextCopy

theorem inside (cost : Nat) (pre : EVM.State)
    (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (above : 64 ≤ j.toNat) (address : j.toNat < 2 ^ 64)
    (platform : 64 ≤ System.Platform.numBits)
    (sourceAbove : 96 ≤ i.toNat)
    (original : i.toNat + (length cost pre a b c d e f g h i j k z tail).toNat ≤ pre.memory.size)
    (fields : c.toNat + 288 < 2 ^ 64)
    (sizeBelow : j.toNat ≤ (c + UInt256.ofNat 288).toNat + 32)
    (endBound : (((free cost pre a b c d e f g h i j k z tail).toNat + (length cost pre a b c d e f g h i j k z tail).toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat) + 32) + 31 < 2 ^ 256)
    (guard : NativeSourceAllocatorDecision.flag (free cost pre a b c d e f g h i j k z tail) (NativeSourceContextPacked.requested cost pre a b c d e f g h i j k z tail) = ⟨0⟩) :
    j.toNat + 32 ≤ (copied cost pre a b c d e f g h i j k z tail).memory.size := by
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  have firstPadding := NativeSourceBoundedPadding.field_padding c pre.memory (by omega) (by omega)
  have sizePadding := NativeSourceBoundedPadding.padding_of_address j.toNat
    (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size (by omega)
  have source := NativeSourceContextSourceInside.inside cost pre a b c d e f g h i j k
    (z :: tail) (length cost pre a b c d e f g h i j k z tail).toNat sourceAbove original (by omega) firstPadding sizeBelow
  have copyPadding := NativeSourceContextPacked.copy_padding cost pre a b c d e f g h i j k z tail (entry cost pre a b c d e f g h i j k z tail).memory
    platform endBound guard
  exact NativeSourceContextCopyCarrier.sizeword_inside cost pre a b c d e f g h i j k z tail above sizePadding source copyPadding

end Compiler.Proofs.IRGeneration.NativeSourceGuardedSizewordCarrier
