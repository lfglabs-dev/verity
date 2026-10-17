import Compiler.Proofs.IRGeneration.NativeSourceAddressDecoderLoad

namespace Compiler.Proofs.IRGeneration.NativeSourceAddressCanonicality
open EvmYul

abbrev mask : UInt256 := UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160) - UInt256.ofNat 1

theorem mask_value : mask.toNat = 2 ^ 160 - 1 := by decide

theorem masked_value (word : UInt256) :
    (word.land mask).toNat = word.toNat % 2 ^ 160 := by
  change (word.toNat &&& mask.toNat) % (2 ^ 256) = _
  rw [mask_value, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (by have bound := Nat.mod_lt word.toNat (show 0 < 2 ^ 160 by decide); omega)

theorem masked_eq_iff (word : UInt256) :
    word.land mask = word ↔ word.toNat < 2 ^ 160 := by
  have equal : word.land mask = word ↔ (word.land mask).toNat = word.toNat := by
    constructor
    · intro h; rw [h]
    · intro h; exact congrArg UInt256.mk (Fin.ext h)
  rw [equal, masked_value]
  constructor
  · intro h
    have bound := Nat.mod_lt word.toNat (show 0 < 2 ^ 160 by decide)
    omega
  · exact Nat.mod_eq_of_lt

theorem difference_zero_iff (word : UInt256) :
    word - word.land mask = UInt256.ofNat 0 ↔ word.toNat < 2 ^ 160 := by
  have equal : word - word.land mask = UInt256.ofNat 0 ↔ word.land mask = word := by
    change UInt256.mk (word.val - (word.land mask).val) = UInt256.mk 0 ↔ word.land mask = word
    rw [UInt256.mk.injEq, sub_eq_zero]
    constructor
    · intro h; exact congrArg UInt256.mk h.symm
    · intro h; rw [h]
  rw [equal, masked_eq_iff]

end Compiler.Proofs.IRGeneration.NativeSourceAddressCanonicality
