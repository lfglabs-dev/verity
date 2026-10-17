import Compiler.Proofs.IRGeneration.NativeSourceContextOriginalCopy

namespace Compiler.Proofs.IRGeneration.NativeSourceFieldGeometry
open EvmYul

theorem offset_toNat (base : UInt256) (offset : Nat)
    (offsetFits : offset < 2 ^ 256) (fits : base.toNat + offset < 2 ^ 256) :
    (base + UInt256.ofNat offset).toNat = base.toNat + offset := by
  have offsetValue : (UInt256.ofNat offset).toNat = offset := Nat.mod_eq_of_lt offsetFits
  rw [NativeSourceAddressGeometry.add_toNat base (UInt256.ofNat offset) (by omega), offsetValue]

theorem fields_below (base : UInt256) (finish : Nat)
    (fits : base.toNat + 288 < 2 ^ 256)
    (below : finish ≤ (base + UInt256.ofNat 192).toNat) :
    finish ≤ (base + UInt256.ofNat 224).toNat ∧
      finish ≤ (base + UInt256.ofNat 256).toNat ∧
      finish ≤ (base + UInt256.ofNat 288).toNat := by
  have first := offset_toNat base 192 (by decide) (by omega)
  have second := offset_toNat base 224 (by decide) (by omega)
  have third := offset_toNat base 256 (by decide) (by omega)
  have fourth := offset_toNat base 288 (by decide) fits
  omega

theorem payload_boundary (base length gap : UInt256)
    (fits : (base.toNat + length.toNat) + gap.toNat < 2 ^ 256) :
    (base + gap).toNat + length.toNat = ((base + length) + gap).toNat := by
  have output := NativeSourceAddressGeometry.add_toNat base gap (by omega)
  have first := NativeSourceAddressGeometry.add_toNat base length (by omega)
  have last := NativeSourceAddressGeometry.add_toNat (base + length) gap (by omega)
  omega

end Compiler.Proofs.IRGeneration.NativeSourceFieldGeometry
