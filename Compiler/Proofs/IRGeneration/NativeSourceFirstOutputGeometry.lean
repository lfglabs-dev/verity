import Compiler.Proofs.IRGeneration.NativeSourceCopiedPayloadReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstOutputGeometry
open EvmYul

theorem output_value (base : UInt256) (fits : base.toNat + 32 < 2 ^ 256) :
    (base + UInt256.ofNat 32).toNat = base.toNat + 32 := by
  exact NativeSourceFieldGeometry.offset_toNat base 32 (by decide) fits

theorem output_above (base : UInt256) (fits : base.toNat + 32 < 2 ^ 256) :
    base.toNat + 32 ≤ (base + UInt256.ofNat 32).toNat := by
  rw [output_value base fits]

theorem output_allocator (base : UInt256) (above : 64 ≤ base.toNat)
    (fits : base.toNat + 32 < 2 ^ 256) :
    96 ≤ (base + UInt256.ofNat 32).toNat := by
  rw [output_value base fits]
  omega

theorem output_below_second (base length : UInt256)
    (fits : (base.toNat + length.toNat) + 32 < 2 ^ 256) :
    (base + UInt256.ofNat 32).toNat + length.toNat ≤
      ((base + length) + UInt256.ofNat 32).toNat := by
  have first := NativeSourceAddressGeometry.add_toNat base length (by omega)
  have second := NativeSourceAddressGeometry.add_toNat (base + length) (UInt256.ofNat 32) (by rw [first]; exact fits)
  rw [output_value base (by omega), second, first]
  change base.toNat + 32 + length.toNat ≤ base.toNat + length.toNat + 32
  omega

end Compiler.Proofs.IRGeneration.NativeSourceFirstOutputGeometry
