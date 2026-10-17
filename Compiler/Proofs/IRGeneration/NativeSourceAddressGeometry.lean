import Compiler.Proofs.IRGeneration.NativeSourceTotalSecondPayload

namespace Compiler.Proofs.IRGeneration.NativeSourceAddressGeometry
open EvmYul

theorem add_toNat (a b : UInt256) (fits : a.toNat + b.toNat < 2 ^ 256) :
    (a + b).toNat = a.toNat + b.toNat := by
  change (a.toNat + b.toNat) % (2 ^ 256) = _
  exact Nat.mod_eq_of_lt fits

theorem final_bound (base length gap amount : UInt256)
    (endFits : ((base.toNat + length.toNat) + amount.toNat) + gap.toNat < 2 ^ 256) :
    ((base + length) + gap).toNat + amount.toNat ≤
      (((base + length) + amount) + gap).toNat := by
  have first := add_toNat base length (by omega : base.toNat + length.toNat < 2 ^ 256)
  have output := add_toNat (base + length) gap (by omega)
  have middle := add_toNat (base + length) amount (by omega)
  have last := add_toNat ((base + length) + amount) gap (by omega)
  omega

end Compiler.Proofs.IRGeneration.NativeSourceAddressGeometry
