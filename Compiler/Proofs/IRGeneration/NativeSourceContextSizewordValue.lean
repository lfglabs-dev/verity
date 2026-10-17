import Compiler.Proofs.IRGeneration.NativeSourceAllocatedSizewordBytes

namespace Compiler.Proofs.IRGeneration.NativeSourceContextSizewordValue
open EvmYul NativeSourceContextCopy

theorem value (cost : Nat) (pre : EVM.State)
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
    (firstGuard : NativeSourceAllocatorDecision.flag j (b - c) = ⟨0⟩) :
    (copied cost pre a b c d e f g h i j k z tail).toMachineState.lookupMemory j = ((b - c) + UInt256.lnot (UInt256.ofNat 31)) := by
  have preserved := NativeSourceGuardedContextLookup.copied_lookup cost pre a b c d e f g h i j k z tail
    upper sd se sf sg fields sizeAddress lengthAddress destBound sourceBound countBound
    platform (by omega) sourceAbove original sizeBelow firstGuard
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  have padding := NativeSourceBoundedPadding.padding_of_address j.toNat
    (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size (by omega)
  obtain ⟨d1, d2, d3, d4⟩ := NativeSourceFieldAddressBounds.field_bounds c fields
  have first := NativeSourceFirstFieldExtent.stored_bound cost pre a b c d e f g h i j k (z :: tail) upper sd d1
  have second := NativeSourceSecondFieldExtent.stored_bound cost pre a b c d e f g h i j k (z :: tail) first se d2
  have third := NativeSourceThirdFieldExtent.stored_bound cost pre a b c d e f g h i j k (z :: tail) second sf d3
  have fourth := NativeSourceFourthFieldExtent.stored_bound cost pre a b c d e f g h i j k (z :: tail) third sg d4
  exact preserved.trans (NativeSourceAllocatedSizewordBytes.lookup cost pre a b c d e f g h i j k
    (z :: tail) sizeAbove padding fourth sizeAddress)

end Compiler.Proofs.IRGeneration.NativeSourceContextSizewordValue
