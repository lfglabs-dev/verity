import Compiler.Proofs.IRGeneration.NativeSourceContextLookup

namespace Compiler.Proofs.IRGeneration.NativeSourceGuardedContextLookup
open EvmYul NativeSourceContextCopy

theorem copied_lookup (cost : Nat) (pre : EVM.State)
    (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (sd : d.toNat < 2 ^ 64) (se : e.toNat < 2 ^ 64)
    (sf : f.toNat < 2 ^ 64) (sg : g.toNat < 2 ^ 64)
    (fields : c.toNat + 288 < 2 ^ 64) (sizeAddress : j.toNat < 2 ^ 64)
    (lengthAddress : k.toNat < 2 ^ 64)
    (destBound : (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat < 2 ^ 64)
    (sourceBound : i.toNat < 2 ^ 64)
    (countBound : (length cost pre a b c d e f g h i j k z tail).toNat < 2 ^ 64)
    (platform : 64 ≤ System.Platform.numBits) (sizeAbove : 64 ≤ j.toNat)
    (sourceAbove : 96 ≤ i.toNat) (original : i.toNat + (length cost pre a b c d e f g h i j k z tail).toNat ≤ pre.memory.size)
    (sizeBelow : j.toNat ≤ (c + UInt256.ofNat 288).toNat + 32)
    (firstGuard : NativeSourceAllocatorDecision.flag j (b - c) = ⟨0⟩) :
    (copied cost pre a b c d e f g h i j k z tail).toMachineState.lookupMemory j = (entry cost pre a b c d e f g h i j k z tail).toMachineState.lookupMemory j := by
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  have firstPadding := NativeSourceBoundedPadding.field_padding c pre.memory (by omega) (by omega)
  have sizePadding := NativeSourceBoundedPadding.padding_of_address j.toNat
    (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size (by omega)
  have sourceInside := NativeSourceContextSourceInside.inside cost pre a b c d e f g h i j k
    (z :: tail) (length cost pre a b c d e f g h i j k z tail).toNat sourceAbove original (by omega) firstPadding sizeBelow
  have padding := NativeSourceBoundedPadding.padding_of_address
    ((free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat (entry cost pre a b c d e f g h i j k z tail).memory.size (by omega)
  have wordInside := NativeSourceSizewordCarrier.returned_inside cost pre a b c d e f g h i j k
    (z :: tail) sizeAbove sizePadding
  have ordered := NativeSourceSizewordSeparation.context_free_above cost pre a b c d e f g h i j k
    (z :: tail) (by omega) upper sd se sf sg fields firstGuard
  have freeBound := NativeSourceAcceptedFree.free_bound cost pre a b c d e f g h i j k
    (z :: tail) (by omega) upper sd se sf sg fields firstGuard
  change j.toNat ≤ (free cost pre a b c d e f g h i j k z tail).toNat at ordered
  change (free cost pre a b c d e f g h i j k z tail).toNat < 2 ^ 64 at freeBound
  have value := NativeSourceFirstOutputGeometry.output_value (free cost pre a b c d e f g h i j k z tail) (by omega)
  have below : j.toNat + 32 ≤ ((free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat := by
    rw [value]
    omega
  exact NativeSourceContextLookup.copied_lookup cost pre a b c d e f g h i j k z tail upper sd se sf sg fields sizeAddress
    lengthAddress destBound sourceBound countBound sourceInside padding wordInside below

end Compiler.Proofs.IRGeneration.NativeSourceGuardedContextLookup
