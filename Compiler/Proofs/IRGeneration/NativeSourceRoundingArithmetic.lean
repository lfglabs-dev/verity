import Compiler.Proofs.IRGeneration.NativeSourceAllocatorMargin

namespace Compiler.Proofs.IRGeneration.NativeSourceRoundingArithmetic
open EvmYul

theorem mask_div (x : Nat) (bounded : x < 2 ^ 256) :
    (x &&& (2 ^ 256 - 32)) / 32 = x / 32 := by
  have divided := Nat.and_div_two_pow (a := x) (b := 2 ^ 256 - 32) (n := 5)
  change (x &&& (2 ^ 256 - 32)) / 32 = (x / 32) &&& ((2 ^ 256 - 32) / 32) at divided
  rw [show (2 ^ 256 - 32) / 32 = 2 ^ 251 - 1 by decide] at divided
  rw [Nat.and_two_pow_sub_one_of_lt_two_pow (by omega : x / 32 < 2 ^ 251)] at divided
  exact divided

theorem mask_mod (x : Nat) : (x &&& (2 ^ 256 - 32)) % 32 = 0 := by
  have reduced := Nat.and_mod_two_pow (a := x) (b := 2 ^ 256 - 32) (n := 5)
  change (x &&& (2 ^ 256 - 32)) % 32 = (x % 32) &&& 0 at reduced
  simpa only [Nat.and_zero] using reduced

theorem mask_value (x : Nat) (bounded : x < 2 ^ 256) :
    x &&& (2 ^ 256 - 32) = x / 32 * 32 := by
  have division := Nat.mod_add_div (x &&& (2 ^ 256 - 32)) 32
  rw [mask_mod, mask_div x bounded] at division
  omega

theorem amount_value (size : UInt256) (fits : size.toNat + 31 < 2 ^ 256) :
    (NativeSourceAllocatorOverflowEntry.amount size).toNat = (size.toNat + 31) / 32 * 32 := by
  have added := NativeSourceFieldGeometry.offset_toNat size 31 (by decide) fits
  change (((size + UInt256.ofNat 31).toNat &&& (2 ^ 256 - 32)) % (2 ^ 256)) = _
  rw [added, Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left fits), mask_value _ fits]

theorem amount_covers (size : UInt256) (fits : size.toNat + 31 < 2 ^ 256) :
    size.toNat ≤ (NativeSourceAllocatorOverflowEntry.amount size).toNat := by
  rw [amount_value size fits]
  omega

theorem positive_margin (size : UInt256) (fits : size.toNat + 31 < 2 ^ 256)
    (positive : 0 < size.toNat) :
    32 ≤ (NativeSourceAllocatorOverflowEntry.amount size).toNat := by
  rw [amount_value size fits]
  omega

end Compiler.Proofs.IRGeneration.NativeSourceRoundingArithmetic



