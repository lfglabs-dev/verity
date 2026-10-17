import Compiler.Proofs.IRGeneration.NativeSourceContextSizewordCarrier
import Compiler.Proofs.IRGeneration.NativeSourceContextSourceInside

namespace Compiler.Proofs.IRGeneration.NativeSourceContextSecondAmountContained
open EvmYul NativeSourceContextCopy

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
    (below : j.toNat + 32 ≤ (((free cost pre a b c d e f g h i j k z tail) + (length cost pre a b c d e f g h i j k z tail)) + UInt256.ofNat 32).toNat)
    (storeBound : (((free cost pre a b c d e f g h i j k z tail) + (length cost pre a b c d e f g h i j k z tail)) + UInt256.ofNat 32).toNat < 2 ^ 64)
    (ordered : c.toNat + 32 ≤ b.toNat) :
    (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat = b.toNat - c.toNat - 32 := by
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  have fits : c.toNat + 288 < 2 ^ 256 := by omega
  have padding := NativeSourceBoundedPadding.field_padding c pre.memory (by omega) (by omega)
  have firstSource := NativeSourceContextSourceInside.inside cost pre a b c d e f g h i j k
    (z :: tail) (length cost pre a b c d e f g h i j k z tail).toNat sourceAbove original fits padding sizeBelow
  exact NativeSourceContextSizewordCarrier.natural_length cost pre a b c d e f g h i j k z tail
    upper sd se sf sg fields sizeAddress lengthAddress destBound sourceBound countBound
    platform sizeAbove sourceAbove original sizeBelow firstGuard firstSource below storeBound ordered

end Compiler.Proofs.IRGeneration.NativeSourceContextSecondAmountContained
