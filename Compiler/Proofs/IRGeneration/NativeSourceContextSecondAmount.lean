import Compiler.Proofs.IRGeneration.NativeSourceSecondAmountGeometry
import Compiler.Proofs.IRGeneration.NativeSourceContextSizewordValue
import Compiler.Proofs.IRGeneration.NativeSourceContextPacked

namespace Compiler.Proofs.IRGeneration.NativeSourceContextSecondAmount
open EvmYul NativeSourceContextCopy

abbrev intercopy (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256) :=
  NativeSourceSecondCopyStore.stored cost (copied cost pre a b c d e f g h i j k z tail) (length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (free cost pre a b c d e f g h i j k z tail) ((free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail

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
    (beforeActive : ¬j ≥ (copied cost pre a b c d e f g h i j k z tail).activeWords * ⟨32⟩)
    (afterActive : ¬j ≥ (intercopy cost pre a b c d e f g h i j k z tail).activeWords * ⟨32⟩)
    (ordered : c.toNat + 32 ≤ b.toNat) :
    (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat = b.toNat - c.toNat - 32 := by
  have word := NativeSourceContextSizewordValue.value cost pre a b c d e f g h i j k z tail
    upper sd se sf sg fields sizeAddress lengthAddress destBound sourceBound countBound
    platform sizeAbove sourceAbove original sizeBelow firstGuard
  exact NativeSourceSecondAmountGeometry.natural_length cost (copied cost pre a b c d e f g h i j k z tail) (length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (free cost pre a b c d e f g h i j k z tail) ((free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z b c tail
    padding inside below beforeActive afterActive word ordered

theorem source_endpoint (cost : Nat) (pre : EVM.State)
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
    (beforeActive : ¬j ≥ (copied cost pre a b c d e f g h i j k z tail).activeWords * ⟨32⟩)
    (afterActive : ¬j ≥ (intercopy cost pre a b c d e f g h i j k z tail).activeWords * ⟨32⟩)
    (ordered : c.toNat + 32 ≤ b.toNat)
    (source : h.toNat = c.toNat + 32) :
    h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat = b.toNat := by
  have amount := natural_length cost pre a b c d e f g h i j k z tail
    upper sd se sf sg fields sizeAddress lengthAddress destBound sourceBound countBound
    platform sizeAbove sourceAbove original sizeBelow firstGuard
    padding inside below beforeActive afterActive ordered
  rw [amount, source]
  omega

end Compiler.Proofs.IRGeneration.NativeSourceContextSecondAmount
