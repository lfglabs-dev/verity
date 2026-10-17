import Compiler.Proofs.IRGeneration.NativeSourceCarrierDerivedReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceSizewordSeparation
open EvmYul

theorem context_free_above (cost : Nat) (pre : EVM.State)
    (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (platform : 7 ≤ System.Platform.numBits) (upper : pre.activeWords.toNat < 2 ^ 251)
    (sd : d.toNat < 2 ^ 64) (se : e.toNat < 2 ^ 64)
    (sf : f.toNat < 2 ^ 64) (sg : g.toNat < 2 ^ 64)
    (fields : c.toNat + 288 < 2 ^ 64)
    (guard : NativeSourceAllocatorDecision.flag j (b - c) = ⟨0⟩) :
    j.toNat ≤ (NativeSourceDecodedPackingStart.free cost
      (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail)).toNat := by
  rw [NativeSourceGeometricFree.context_free cost pre a b c d e f g h i j k tail
    platform upper sd se sf sg fields (NativeSourceAllocatorMargin.base_bound j (b - c) guard)]
  exact (NativeSourceAllocatorAcceptedBounds.natural_bounds j (b - c) guard).2

theorem below (base length query : UInt256)
    (ordered : query.toNat ≤ base.toNat)
    (fits : base.toNat + length.toNat + 32 < 2 ^ 256) :
    query.toNat + 32 ≤ ((base + length) + UInt256.ofNat 32).toNat := by
  have first := NativeSourceAddressGeometry.add_toNat base length (by omega)
  have output := NativeSourceAddressGeometry.add_toNat (base + length) (UInt256.ofNat 32) (by rw [first]; exact fits)
  rw [output, first]
  change query.toNat + 32 ≤ base.toNat + length.toNat + 32
  omega

end Compiler.Proofs.IRGeneration.NativeSourceSizewordSeparation
