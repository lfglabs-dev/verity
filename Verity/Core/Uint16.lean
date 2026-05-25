/-
  Core Uint16 type.

  Solidity `uint16` values are ABI-encoded in one 256-bit word but are bounded
  to 16 bits at the surface. This type preserves that bound in Verity models
  while exposing explicit word conversion for ABI/storage encoding.
-/

import Verity.Core.Uint256

namespace Verity.Core

def UINT16_MODULUS : Nat := 2^16

structure Uint16 where
  val : Nat
  isLt : val < UINT16_MODULUS
  deriving DecidableEq

namespace Uint16

def modulus : Nat := UINT16_MODULUS

theorem modulus_pos : 0 < modulus := by
  have h2 : (0 : Nat) < (2 : Nat) := by decide
  have h : 0 < (2 : Nat) ^ 16 := Nat.pow_pos h2
  simp [modulus, UINT16_MODULUS]

def ofNat (n : Nat) : Uint16 :=
  ⟨n % modulus, Nat.mod_lt _ modulus_pos⟩

def toNat (value : Uint16) : Nat := value.val

def toUint256 (value : Uint16) : Uint256 :=
  Uint256.ofNat value.val

def ofUint256 (value : Uint256) : Uint16 :=
  ofNat value.val

instance : OfNat Uint16 n := ⟨ofNat n⟩
instance : Inhabited Uint16 := ⟨ofNat 0⟩
instance : Repr Uint16 := ⟨fun u _ => repr u.val⟩
instance : Coe Uint16 Nat := ⟨Uint16.val⟩
instance : Coe Uint16 Uint256 := ⟨toUint256⟩

@[simp] theorem val_ofNat (n : Nat) : (ofNat n).val = n % modulus := rfl
@[simp] theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n % modulus := rfl
@[simp] theorem val_zero : (0 : Uint16).val = 0 := by
  change (ofNat 0).val = 0
  simp [ofNat]

@[ext] theorem ext {a b : Uint16} (h : a.val = b.val) : a = b := by
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      cases h
      have : ha = hb := by apply Subsingleton.elim
      cases this
      rfl

instance : BEq Uint16 := ⟨fun a b => decide (a = b)⟩

instance : LawfulBEq Uint16 where
  eq_of_beq {a b} h := by
    simp only [BEq.beq] at h
    exact of_decide_eq_true h
  rfl {a} := by
    show decide (a = a) = true
    exact decide_eq_true rfl

@[simp] theorem toUint256_ofNat (n : Nat) :
    (ofNat n).toUint256 = Uint256.ofNat (n % modulus) := rfl

@[simp] theorem ofUint256_toUint256 (value : Uint16) :
    ofUint256 value.toUint256 = value := by
  apply ext
  have hUint256 : value.val < Uint256.modulus := by
    exact Nat.lt_trans value.isLt (by native_decide)
  simp [ofUint256, toUint256, ofNat, modulus, Uint256.val_ofNat,
    Nat.mod_eq_of_lt hUint256, Nat.mod_eq_of_lt value.isLt]

end Uint16

end Verity.Core
