import Compiler.Proofs.IRGeneration.NativeSourceContextSecondAmountGuards
import Compiler.Proofs.IRGeneration.NativeSourceContextSecondPayloadBytes

namespace Compiler.Proofs.IRGeneration.NativeSourceContextSizewordCarrier
open EvmYul NativeSourceContextCopy

theorem entry_inside (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (sizeAbove : 96 ≤ j.toNat) (sizeAddress : j.toNat < 2 ^ 64)
    (platform : 64 ≤ System.Platform.numBits) :
    j.toNat + 32 ≤ (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size := by
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  have padding := NativeSourceBoundedPadding.padding_of_address j.toNat
    (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size (by omega)
  have sized := NativeSourceSizeCarrier.size cost (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail))
    b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k
    (UInt256.ofNat 0 :: z :: tail) padding
  have fits : 96 ≤ (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size := by
    change 96 ≤ (NativeSourceFieldSize.stored cost (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail))
      b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k (UInt256.ofNat 0 :: z :: tail)).memory.size
    rw [sized]
    omega
  rw [NativeSourceAllocatorCarrier.context_size cost pre a b c d e f g h i j k (z :: tail) fits]
  change j.toNat + 32 ≤ (NativeSourceFieldSize.stored cost (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail))
    b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k (UInt256.ofNat 0 :: z :: tail)).memory.size
  rw [sized]
  exact Nat.le_max_right _ _

theorem copied_inside (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (sizeAbove : 96 ≤ j.toNat) (sizeAddress : j.toNat < 2 ^ 64)
    (platform : 64 ≤ System.Platform.numBits)
    (source : i.toNat + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat ≤ (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size)
    (padding : ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat - (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits) :
    j.toNat + 32 ≤ (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.size := by
  have inside := entry_inside cost pre a b c d e f g h i j k z tail sizeAbove sizeAddress platform
  rw [NativeSourceContextSecondPayloadBytes.copied_memory]
  exact inside.trans (NativeSourcePayloadReturn.copy_monotone _ _ _ _ source padding)

theorem natural_length (cost : Nat) (pre : EVM.State)
    (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (sd : d.toNat < 2 ^ 64) (se : e.toNat < 2 ^ 64)
    (sf : f.toNat < 2 ^ 64) (sg : g.toNat < 2 ^ 64)
    (fields : c.toNat + 288 < 2 ^ 64) (sizeAddress : j.toNat < 2 ^ 64)
    (lengthAddress : k.toNat < 2 ^ 64)
    (destBound : (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat < 2 ^ 64)
    (sourceBound : i.toNat < 2 ^ 64)
    (countBound : (length cost pre a b c d e f g h i j k z tail).toNat < 2 ^ 64)
    (platform : 64 ≤ System.Platform.numBits) (sizeAbove : 96 ≤ j.toNat)
    (sourceAbove : 96 ≤ i.toNat) (original : i.toNat + (length cost pre a b c d e f g h i j k z tail).toNat ≤ pre.memory.size)
    (sizeBelow : j.toNat ≤ (c + UInt256.ofNat 288).toNat + 32)
    (firstGuard : NativeSourceAllocatorDecision.flag j (b - c) = ⟨0⟩)
    (firstSource : i.toNat + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat ≤ (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size)
    (below : j.toNat + 32 ≤ (((free cost pre a b c d e f g h i j k z tail) + (length cost pre a b c d e f g h i j k z tail)) + UInt256.ofNat 32).toNat)
    (storeBound : (((free cost pre a b c d e f g h i j k z tail) + (length cost pre a b c d e f g h i j k z tail)) + UInt256.ofNat 32).toNat < 2 ^ 64)
    (ordered : c.toNat + 32 ≤ b.toNat) :
    (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat = b.toNat - c.toNat - 32 := by
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  have firstPadding := NativeSourceBoundedPadding.padding_of_address
    ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size (lt_of_lt_of_le destBound power)
  have inside := copied_inside cost pre a b c d e f g h i j k z tail sizeAbove sizeAddress platform firstSource firstPadding
  have padding := NativeSourceBoundedPadding.padding_of_address
    (((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail)) + UInt256.ofNat 32).toNat
    (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.size (lt_of_lt_of_le storeBound power)
  exact NativeSourceContextSecondAmountGuards.natural_length cost pre a b c d e f g h i j k z tail
    upper sd se sf sg fields sizeAddress lengthAddress destBound sourceBound countBound
    platform sizeAbove sourceAbove original sizeBelow firstGuard padding inside below storeBound ordered

end Compiler.Proofs.IRGeneration.NativeSourceContextSizewordCarrier
