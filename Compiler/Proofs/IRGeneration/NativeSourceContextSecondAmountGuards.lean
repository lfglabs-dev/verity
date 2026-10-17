import Compiler.Proofs.IRGeneration.NativeSourceContextSecondAmount
import Compiler.Proofs.IRGeneration.NativeSourceIntercopyActiveLookup
import Compiler.Proofs.IRGeneration.NativeSourceContextCopyActive
import Compiler.Proofs.IRGeneration.NativeSourceContextActiveGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceContextSecondAmountGuards
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
    (padding : (((free cost pre a b c d e f g h i j k z tail) + (length cost pre a b c d e f g h i j k z tail)) + UInt256.ofNat 32).toNat - (copied cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits)
    (inside : j.toNat + 32 ≤ (copied cost pre a b c d e f g h i j k z tail).memory.size)
    (below : j.toNat + 32 ≤ (((free cost pre a b c d e f g h i j k z tail) + (length cost pre a b c d e f g h i j k z tail)) + UInt256.ofNat 32).toNat)
    (storeBound : (((free cost pre a b c d e f g h i j k z tail) + (length cost pre a b c d e f g h i j k z tail)) + UInt256.ofNat 32).toNat < 2 ^ 64)
    (ordered : c.toNat + 32 ≤ b.toNat) :
    (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat = b.toNat - c.toNat - 32 := by
  have copiedUpper := NativeSourceContextCopyActive.copied_bound cost pre a b c d e f g h i j k z tail
    upper sd se sf sg fields sizeAddress lengthAddress destBound sourceBound countBound
  have active := NativeSourceContextActiveGuard.copied_guard cost pre a b c d e f g h i j k z tail
    upper sd se sf sg fields sizeAddress lengthAddress destBound sourceBound countBound
  have loaded := NativeSourceIntercopyActiveLookup.amount cost (copied cost pre a b c d e f g h i j k z tail) (length cost pre a b c d e f g h i j k z tail) j h
    (UInt256.ofNat 32) (free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (free cost pre a b c d e f g h i j k z tail)
    ((free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail
    inside below padding copiedUpper storeBound active
  have word := NativeSourceContextSizewordValue.value cost pre a b c d e f g h i j k z tail
    upper sd se sf sg fields sizeAddress lengthAddress destBound sourceBound countBound
    platform sizeAbove sourceAbove original sizeBelow firstGuard
  change (NativeSourcePackedRequested.amount cost (copied cost pre a b c d e f g h i j k z tail) (length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32)
    (free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (free cost pre a b c d e f g h i j k z tail) ((free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).toNat = _
  rw [loaded, word]
  exact NativeSourceLengthwordGeometry.length_toNat b c ordered

end Compiler.Proofs.IRGeneration.NativeSourceContextSecondAmountGuards
