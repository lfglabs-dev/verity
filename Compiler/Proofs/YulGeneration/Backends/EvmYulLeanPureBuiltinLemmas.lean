import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeLowering
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeSignedArithLemmas
import Mathlib.Data.Nat.Bitwise
import Verity.Core.Int256
import Verity.Core.Uint256

namespace Compiler.Proofs.YulGeneration.Backends

private theorem uint256_size_eq_evmModulus :
    EvmYul.UInt256.size = Compiler.Constants.evmModulus := by
  decide

private theorem word_lt_uint256_size (x : Nat) :
    x % EvmYul.UInt256.size < 2 ^ 256 := by
  simpa [EvmYul.UInt256.size] using Nat.mod_lt x (by decide : 0 < EvmYul.UInt256.size)

@[simp] theorem evalPureBuiltinViaEvmYulLean_add_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "add" [a, b] =
      some ((a + b) % Compiler.Constants.evmModulus) := by
  rw [← uint256_size_eq_evmModulus]
  change some ((Fin.ofNat EvmYul.UInt256.size a + Fin.ofNat EvmYul.UInt256.size b).val) =
      some ((a + b) % EvmYul.UInt256.size)
  simp [Fin.val_add, Nat.add_mod]

@[simp] theorem evalPureBuiltinViaEvmYulLean_sub_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "sub" [a, b] =
      some ((Compiler.Constants.evmModulus + (a % Compiler.Constants.evmModulus) -
        (b % Compiler.Constants.evmModulus)) % Compiler.Constants.evmModulus) := by
  rw [← uint256_size_eq_evmModulus]
  change some ((Fin.ofNat EvmYul.UInt256.size a - Fin.ofNat EvmYul.UInt256.size b).val) =
      some ((EvmYul.UInt256.size + a % EvmYul.UInt256.size - b % EvmYul.UInt256.size) %
        EvmYul.UInt256.size)
  have hsub :
      EvmYul.UInt256.size + a % EvmYul.UInt256.size - b % EvmYul.UInt256.size =
        EvmYul.UInt256.size - b % EvmYul.UInt256.size + a % EvmYul.UInt256.size := by
    have hb : b % EvmYul.UInt256.size ≤ EvmYul.UInt256.size := by
      exact Nat.le_of_lt (Nat.mod_lt _ (by simp [EvmYul.UInt256.size]))
    omega
  simp [Fin.sub_def, Nat.add_mod, hsub]

@[simp] theorem evalPureBuiltinViaEvmYulLean_mul_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "mul" [a, b] =
      some ((a * b) % Compiler.Constants.evmModulus) := by
  rw [← uint256_size_eq_evmModulus]
  change some ((Fin.ofNat EvmYul.UInt256.size a * Fin.ofNat EvmYul.UInt256.size b).val) =
      some ((a * b) % EvmYul.UInt256.size)
  simp [Fin.mul_def, Nat.mul_mod]

@[simp] theorem evalPureBuiltinViaEvmYulLean_div_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "div" [a, b] =
      some (if b % Compiler.Constants.evmModulus = 0 then 0 else
        (a % Compiler.Constants.evmModulus) / (b % Compiler.Constants.evmModulus)) := by
  rw [← uint256_size_eq_evmModulus]
  change some ((Fin.ofNat EvmYul.UInt256.size a / Fin.ofNat EvmYul.UInt256.size b).val) =
      some (if b % EvmYul.UInt256.size = 0 then 0 else
        (a % EvmYul.UInt256.size) / (b % EvmYul.UInt256.size))
  by_cases hb : b % EvmYul.UInt256.size = 0 <;> simp [hb]

@[simp] theorem evalPureBuiltinViaEvmYulLean_mod_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "mod" [a, b] =
      some (if b % Compiler.Constants.evmModulus = 0 then 0 else
        (a % Compiler.Constants.evmModulus) % (b % Compiler.Constants.evmModulus)) := by
  rw [← uint256_size_eq_evmModulus]
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.mod (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) =
    some (if b % EvmYul.UInt256.size = 0 then 0 else
      (a % EvmYul.UInt256.size) % (b % EvmYul.UInt256.size))
  by_cases hb : b % EvmYul.UInt256.size = 0
  · have hb0val : ((EvmYul.UInt256.ofNat b).val).val = 0 := by
      change b % EvmYul.UInt256.size = 0
      exact hb
    have hb0 : (EvmYul.UInt256.ofNat b).val = 0 := Fin.ext hb0val
    simp [EvmYul.UInt256.mod, EvmYul.UInt256.toNat, hb, hb0]
  · have hb0 : ¬ (EvmYul.UInt256.ofNat b).val = 0 := by
      intro h
      exact hb (congrArg Fin.val h)
    rw [show EvmYul.UInt256.mod (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b) =
          ⟨(EvmYul.UInt256.ofNat a).val % (EvmYul.UInt256.ofNat b).val⟩ by
            simp [EvmYul.UInt256.mod, hb0]]
    simp [hb, EvmYul.UInt256.toNat]
    rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_eq_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "eq" [a, b] =
      some (if a % Compiler.Constants.evmModulus = b % Compiler.Constants.evmModulus then 1 else 0) := by
  rw [← uint256_size_eq_evmModulus]
  rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_iszero_native (a : Nat) :
    evalPureBuiltinViaEvmYulLean "iszero" [a] =
      some (if a % Compiler.Constants.evmModulus = 0 then 1 else 0) := by
  rw [← uint256_size_eq_evmModulus]
  rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_lt_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "lt" [a, b] =
      some (if a % Compiler.Constants.evmModulus < b % Compiler.Constants.evmModulus then 1 else 0) := by
  rw [← uint256_size_eq_evmModulus]
  rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_gt_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "gt" [a, b] =
      some (if b % Compiler.Constants.evmModulus < a % Compiler.Constants.evmModulus then 1 else 0) := by
  rw [← uint256_size_eq_evmModulus]
  rfl

private theorem toNat_fromBool (b : Bool) :
    EvmYul.UInt256.toNat (Bool.toUInt256 b) = if b then 1 else 0 := by
  cases b <;> rfl

private theorem uint256_lt_iff_nat_lt {a b : Nat}
    (ha : a < EvmYul.UInt256.size) (hb : b < EvmYul.UInt256.size) :
    ((⟨⟨a, ha⟩⟩ : EvmYul.UInt256) < ⟨⟨b, hb⟩⟩) ↔ (a < b) :=
  Iff.rfl

private theorem slt_int256_eq_sltBool (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus)
    (hb : b < Compiler.Constants.evmModulus) :
    (if Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 ⟨a, ha⟩) <
        Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)
     then (1 : Nat) else 0) =
    (EvmYul.UInt256.toNat
      (EvmYul.UInt256.slt ⟨⟨a, by simpa [uint256_size_eq_evmModulus] using ha⟩⟩
        ⟨⟨b, by simpa [uint256_size_eq_evmModulus] using hb⟩⟩)) := by
  unfold EvmYul.UInt256.slt
  rw [toNat_fromBool]
  unfold EvmYul.UInt256.sltBool
  simp only [EvmYul.UInt256.toNat, ge_iff_le]
  have ha' : a < EvmYul.UInt256.size := by simpa [uint256_size_eq_evmModulus] using ha
  have hb' : b < EvmYul.UInt256.size := by simpa [uint256_size_eq_evmModulus] using hb
  simp only [uint256_lt_iff_nat_lt ha' hb']
  simp only [Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
    Verity.Core.Int256.signBit, Verity.Core.Int256.modulus,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
  split_ifs <;> simp_all [Compiler.Constants.evmModulus, EvmYul.UInt256.size] <;> omega

@[simp] theorem evalPureBuiltinViaEvmYulLean_slt_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "slt" [a, b] =
      some (if Verity.Core.Int256.toInt
              (Verity.Core.Int256.ofUint256
                (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus))) <
            Verity.Core.Int256.toInt
              (Verity.Core.Int256.ofUint256
                (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus)))
           then 1 else 0) := by
  have ha : a % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus :=
    Nat.mod_lt a (by unfold Compiler.Constants.evmModulus; omega)
  have hb : b % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus :=
    Nat.mod_lt b (by unfold Compiler.Constants.evmModulus; omega)
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.slt (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) =
    some (if Verity.Core.Int256.toInt
              (Verity.Core.Int256.ofUint256
                (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus))) <
            Verity.Core.Int256.toInt
              (Verity.Core.Int256.ofUint256
                (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus)))
           then 1 else 0)
  congr 1
  rw [show EvmYul.UInt256.ofNat a =
      (⟨⟨a % Compiler.Constants.evmModulus, by
        simpa [uint256_size_eq_evmModulus] using ha⟩⟩ : EvmYul.UInt256) by
        simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  rw [show EvmYul.UInt256.ofNat b =
      (⟨⟨b % Compiler.Constants.evmModulus, by
        simpa [uint256_size_eq_evmModulus] using hb⟩⟩ : EvmYul.UInt256) by
        simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  have hmod_a :
      (a % Compiler.Constants.evmModulus) % Verity.Core.UINT256_MODULUS =
        a % Compiler.Constants.evmModulus := by
    exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using ha)
  have hmod_b :
      (b % Compiler.Constants.evmModulus) % Verity.Core.UINT256_MODULUS =
        b % Compiler.Constants.evmModulus := by
    exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using hb)
  simp only [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, hmod_a, hmod_b]
  exact (slt_int256_eq_sltBool
    (a % Compiler.Constants.evmModulus) (b % Compiler.Constants.evmModulus) ha hb).symm

private theorem sgt_int256_eq_sgtBool (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus)
    (hb : b < Compiler.Constants.evmModulus) :
    (if Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 ⟨b, hb⟩) <
        Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
     then (1 : Nat) else 0) =
    (EvmYul.UInt256.toNat
      (EvmYul.UInt256.sgt ⟨⟨a, by simpa [uint256_size_eq_evmModulus] using ha⟩⟩
        ⟨⟨b, by simpa [uint256_size_eq_evmModulus] using hb⟩⟩)) := by
  unfold EvmYul.UInt256.sgt
  rw [toNat_fromBool]
  unfold EvmYul.UInt256.sgtBool
  simp only [EvmYul.UInt256.toNat, ge_iff_le]
  have ha' : a < EvmYul.UInt256.size := by simpa [uint256_size_eq_evmModulus] using ha
  have hb' : b < EvmYul.UInt256.size := by simpa [uint256_size_eq_evmModulus] using hb
  simp only [uint256_lt_iff_nat_lt hb' ha']
  simp only [Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
    Verity.Core.Int256.signBit, Verity.Core.Int256.modulus,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
  split_ifs <;> simp_all [Compiler.Constants.evmModulus, EvmYul.UInt256.size] <;> omega

@[simp] theorem evalPureBuiltinViaEvmYulLean_sgt_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "sgt" [a, b] =
      some (if Verity.Core.Int256.toInt
              (Verity.Core.Int256.ofUint256
                (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus))) <
            Verity.Core.Int256.toInt
              (Verity.Core.Int256.ofUint256
                (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus)))
           then 1 else 0) := by
  have ha : a % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus :=
    Nat.mod_lt a (by unfold Compiler.Constants.evmModulus; omega)
  have hb : b % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus :=
    Nat.mod_lt b (by unfold Compiler.Constants.evmModulus; omega)
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.sgt (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) =
    some (if Verity.Core.Int256.toInt
              (Verity.Core.Int256.ofUint256
                (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus))) <
            Verity.Core.Int256.toInt
              (Verity.Core.Int256.ofUint256
                (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus)))
           then 1 else 0)
  congr 1
  rw [show EvmYul.UInt256.ofNat a =
      (⟨⟨a % Compiler.Constants.evmModulus, by
        simpa [uint256_size_eq_evmModulus] using ha⟩⟩ : EvmYul.UInt256) by
        simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  rw [show EvmYul.UInt256.ofNat b =
      (⟨⟨b % Compiler.Constants.evmModulus, by
        simpa [uint256_size_eq_evmModulus] using hb⟩⟩ : EvmYul.UInt256) by
        simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  have hmod_a :
      (a % Compiler.Constants.evmModulus) % Verity.Core.UINT256_MODULUS =
        a % Compiler.Constants.evmModulus := by
    exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using ha)
  have hmod_b :
      (b % Compiler.Constants.evmModulus) % Verity.Core.UINT256_MODULUS =
        b % Compiler.Constants.evmModulus := by
    exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using hb)
  simp only [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, hmod_a, hmod_b]
  exact (sgt_int256_eq_sgtBool
    (a % Compiler.Constants.evmModulus) (b % Compiler.Constants.evmModulus) ha hb).symm

@[simp] theorem evalPureBuiltinViaEvmYulLean_sdiv_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "sdiv" [a, b] =
      some (Verity.Core.Int256.div
        (Verity.Core.Int256.ofUint256
          (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus)))
        (Verity.Core.Int256.ofUint256
          (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus)))).toUint256.val := by
  have ha : a % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus :=
    Nat.mod_lt a (by unfold Compiler.Constants.evmModulus; omega)
  have hb : b % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus :=
    Nat.mod_lt b (by unfold Compiler.Constants.evmModulus; omega)
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.sdiv (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) =
    some (Verity.Core.Int256.div
      (Verity.Core.Int256.ofUint256
        (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus)))
      (Verity.Core.Int256.ofUint256
        (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus)))).toUint256.val
  congr 1
  rw [show EvmYul.UInt256.ofNat a =
      (⟨⟨a % Compiler.Constants.evmModulus, by
        simpa [uint256_size_eq_evmModulus] using ha⟩⟩ : EvmYul.UInt256) by
        simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  rw [show EvmYul.UInt256.ofNat b =
      (⟨⟨b % Compiler.Constants.evmModulus, by
        simpa [uint256_size_eq_evmModulus] using hb⟩⟩ : EvmYul.UInt256) by
        simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  have hmod_a :
      (a % Compiler.Constants.evmModulus) % Verity.Core.UINT256_MODULUS =
        a % Compiler.Constants.evmModulus := by
    exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using ha)
  have hmod_b :
      (b % Compiler.Constants.evmModulus) % Verity.Core.UINT256_MODULUS =
        b % Compiler.Constants.evmModulus := by
    exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using hb)
  simp only [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, hmod_a, hmod_b]
  exact (int256_div_toUint256_val_eq_uint256_sdiv
    (a % Compiler.Constants.evmModulus) (b % Compiler.Constants.evmModulus) ha hb).symm

@[simp] theorem evalPureBuiltinViaEvmYulLean_smod_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "smod" [a, b] =
      some (Verity.Core.Int256.mod
        (Verity.Core.Int256.ofUint256
          (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus)))
        (Verity.Core.Int256.ofUint256
          (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus)))).toUint256.val := by
  have ha : a % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus :=
    Nat.mod_lt a (by unfold Compiler.Constants.evmModulus; omega)
  have hb : b % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus :=
    Nat.mod_lt b (by unfold Compiler.Constants.evmModulus; omega)
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.smod (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) =
    some (Verity.Core.Int256.mod
      (Verity.Core.Int256.ofUint256
        (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus)))
      (Verity.Core.Int256.ofUint256
        (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus)))).toUint256.val
  congr 1
  rw [show EvmYul.UInt256.ofNat a =
      (⟨⟨a % Compiler.Constants.evmModulus, by
        simpa [uint256_size_eq_evmModulus] using ha⟩⟩ : EvmYul.UInt256) by
        simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  rw [show EvmYul.UInt256.ofNat b =
      (⟨⟨b % Compiler.Constants.evmModulus, by
        simpa [uint256_size_eq_evmModulus] using hb⟩⟩ : EvmYul.UInt256) by
        simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  have hmod_a :
      (a % Compiler.Constants.evmModulus) % Verity.Core.UINT256_MODULUS =
        a % Compiler.Constants.evmModulus := by
    exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using ha)
  have hmod_b :
      (b % Compiler.Constants.evmModulus) % Verity.Core.UINT256_MODULUS =
        b % Compiler.Constants.evmModulus := by
    exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using hb)
  simp only [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, hmod_a, hmod_b]
  exact (int256_mod_toUint256_val_eq_uint256_smod
    (a % Compiler.Constants.evmModulus) (b % Compiler.Constants.evmModulus) ha hb).symm

@[simp] theorem evalPureBuiltinViaEvmYulLean_sar_native (shift value : Nat) :
    evalPureBuiltinViaEvmYulLean "sar" [shift, value] =
      some (Verity.Core.Int256.sar
        (Verity.Core.Int256.ofUint256
          (Verity.Core.Uint256.ofNat (shift % Compiler.Constants.evmModulus)))
        (Verity.Core.Int256.ofUint256
          (Verity.Core.Uint256.ofNat (value % Compiler.Constants.evmModulus)))).toUint256.val := by
  have hs : shift % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus :=
    Nat.mod_lt shift (by unfold Compiler.Constants.evmModulus; omega)
  have hv : value % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus :=
    Nat.mod_lt value (by unfold Compiler.Constants.evmModulus; omega)
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.sar (EvmYul.UInt256.ofNat shift) (EvmYul.UInt256.ofNat value))) =
    some (Verity.Core.Int256.sar
      (Verity.Core.Int256.ofUint256
        (Verity.Core.Uint256.ofNat (shift % Compiler.Constants.evmModulus)))
      (Verity.Core.Int256.ofUint256
        (Verity.Core.Uint256.ofNat (value % Compiler.Constants.evmModulus)))).toUint256.val
  congr 1
  rw [show EvmYul.UInt256.ofNat shift =
      (⟨⟨shift % Compiler.Constants.evmModulus, by
        simpa [uint256_size_eq_evmModulus] using hs⟩⟩ : EvmYul.UInt256) by
        simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  rw [show EvmYul.UInt256.ofNat value =
      (⟨⟨value % Compiler.Constants.evmModulus, by
        simpa [uint256_size_eq_evmModulus] using hv⟩⟩ : EvmYul.UInt256) by
        simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  have hmod_s :
      (shift % Compiler.Constants.evmModulus) % Verity.Core.UINT256_MODULUS =
        shift % Compiler.Constants.evmModulus := by
    exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using hs)
  have hmod_v :
      (value % Compiler.Constants.evmModulus) % Verity.Core.UINT256_MODULUS =
        value % Compiler.Constants.evmModulus := by
    exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using hv)
  simp only [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, hmod_s, hmod_v]
  exact (int256_sar_toUint256_val_eq_uint256_sar
    (shift % Compiler.Constants.evmModulus) (value % Compiler.Constants.evmModulus) hs hv).symm

@[simp] theorem evalPureBuiltinViaEvmYulLean_signextend_native (byteIdx value : Nat) :
    evalPureBuiltinViaEvmYulLean "signextend" [byteIdx, value] =
      some (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat (byteIdx % Compiler.Constants.evmModulus))
        (Verity.Core.Uint256.ofNat (value % Compiler.Constants.evmModulus))).val := by
  have hb : byteIdx % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus :=
    Nat.mod_lt byteIdx (by unfold Compiler.Constants.evmModulus; omega)
  have hv : value % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus :=
    Nat.mod_lt value (by unfold Compiler.Constants.evmModulus; omega)
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.signextend (EvmYul.UInt256.ofNat byteIdx) (EvmYul.UInt256.ofNat value))) =
    some (Verity.Core.Uint256.signextend
      (Verity.Core.Uint256.ofNat (byteIdx % Compiler.Constants.evmModulus))
      (Verity.Core.Uint256.ofNat (value % Compiler.Constants.evmModulus))).val
  congr 1
  rw [show EvmYul.UInt256.ofNat byteIdx =
      (⟨⟨byteIdx % Compiler.Constants.evmModulus, by
        simpa [uint256_size_eq_evmModulus] using hb⟩⟩ : EvmYul.UInt256) by
        simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  rw [show EvmYul.UInt256.ofNat value =
      (⟨⟨value % Compiler.Constants.evmModulus, by
        simpa [uint256_size_eq_evmModulus] using hv⟩⟩ : EvmYul.UInt256) by
        simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  have hmod_b :
      (byteIdx % Compiler.Constants.evmModulus) % Verity.Core.UINT256_MODULUS =
        byteIdx % Compiler.Constants.evmModulus := by
    exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using hb)
  have hmod_v :
      (value % Compiler.Constants.evmModulus) % Verity.Core.UINT256_MODULUS =
        value % Compiler.Constants.evmModulus := by
    exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using hv)
  simp only [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, hmod_b, hmod_v]
  exact (uint256_signextend_val_eq_uint256_signextend
    (byteIdx % Compiler.Constants.evmModulus) (value % Compiler.Constants.evmModulus) hb hv).symm

@[simp] theorem evalPureBuiltinViaEvmYulLean_and_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "and" [a, b] =
      some ((a % Compiler.Constants.evmModulus) &&& (b % Compiler.Constants.evmModulus)) := by
  rw [← uint256_size_eq_evmModulus]
  change some (((Nat.bitwise Bool.and (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size)) %
      EvmYul.UInt256.size)) =
    some (Nat.bitwise Bool.and (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size))
  congr 1
  rw [Nat.mod_eq_of_lt]
  exact Nat.bitwise_lt_two_pow (f := Bool.and) (n := 256)
    (by simpa [EvmYul.UInt256.size] using Nat.mod_lt a (by decide : 0 < EvmYul.UInt256.size))
    (by simpa [EvmYul.UInt256.size] using Nat.mod_lt b (by decide : 0 < EvmYul.UInt256.size))

@[simp] theorem evalPureBuiltinViaEvmYulLean_or_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "or" [a, b] =
      some ((a % Compiler.Constants.evmModulus) ||| (b % Compiler.Constants.evmModulus)) := by
  rw [← uint256_size_eq_evmModulus]
  change some (((Nat.bitwise Bool.or (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size)) %
      EvmYul.UInt256.size)) =
    some (Nat.bitwise Bool.or (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size))
  congr 1
  rw [Nat.mod_eq_of_lt]
  exact Nat.bitwise_lt_two_pow (f := Bool.or) (n := 256)
    (word_lt_uint256_size a) (word_lt_uint256_size b)

@[simp] theorem evalPureBuiltinViaEvmYulLean_xor_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "xor" [a, b] =
      some (Nat.xor (a % Compiler.Constants.evmModulus) (b % Compiler.Constants.evmModulus)) := by
  rw [← uint256_size_eq_evmModulus]
  change some (((a % EvmYul.UInt256.size ^^^ b % EvmYul.UInt256.size) %
      EvmYul.UInt256.size)) =
    some (a % EvmYul.UInt256.size ^^^ b % EvmYul.UInt256.size)
  congr 1
  rw [Nat.mod_eq_of_lt]
  exact Nat.xor_lt_two_pow (word_lt_uint256_size a) (word_lt_uint256_size b)

private theorem xor_all_ones_uint256_word (a : Nat) :
    (a % EvmYul.UInt256.size) ^^^ (EvmYul.UInt256.size - 1) =
      EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size) := by
  calc
    (a % EvmYul.UInt256.size) ^^^ (EvmYul.UInt256.size - 1) =
        ((BitVec.ofNat 256 a) ^^^ BitVec.allOnes 256).toNat := by
      simp [BitVec.toNat_xor, EvmYul.UInt256.size]
    _ = (~~~(BitVec.ofNat 256 a)).toNat := by
      rw [BitVec.xor_allOnes]
    _ = EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size) := by
      simp [BitVec.toNat_not, EvmYul.UInt256.size]

@[simp] theorem evalPureBuiltinViaEvmYulLean_not_native (a : Nat) :
    evalPureBuiltinViaEvmYulLean "not" [a] =
      some (Nat.xor (a % Compiler.Constants.evmModulus)
        (Compiler.Constants.evmModulus - 1)) := by
  rw [← uint256_size_eq_evmModulus]
  change evalPureBuiltinViaEvmYulLean "not" [a] =
    some ((a % EvmYul.UInt256.size) ^^^ (EvmYul.UInt256.size - 1))
  have hsub : evalPureBuiltinViaEvmYulLean "not" [a] =
      some (EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size)) := by
    change evalPureBuiltinViaEvmYulLean "sub" [EvmYul.UInt256.size - 1, a] =
      some (EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size))
    rw [evalPureBuiltinViaEvmYulLean_sub_native]
    rw [← uint256_size_eq_evmModulus]
    have hs : 0 < EvmYul.UInt256.size := by simp [EvmYul.UInt256.size]
    have ha : a % EvmYul.UInt256.size < EvmYul.UInt256.size := Nat.mod_lt _ hs
    have hlt : EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size) < EvmYul.UInt256.size := by
      omega
    have hmod :
        ((EvmYul.UInt256.size + (EvmYul.UInt256.size - 1) % EvmYul.UInt256.size -
            a % EvmYul.UInt256.size) % EvmYul.UInt256.size) =
          EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size) := by
      have hsizeMinusOneMod :
          (EvmYul.UInt256.size - 1) % EvmYul.UInt256.size = EvmYul.UInt256.size - 1 := by
        exact Nat.mod_eq_of_lt (by omega)
      rw [hsizeMinusOneMod]
      have harr :
          EvmYul.UInt256.size + (EvmYul.UInt256.size - 1) - a % EvmYul.UInt256.size =
            EvmYul.UInt256.size +
              (EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size)) := by
        omega
      rw [harr, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]
    exact congrArg some hmod
  rw [hsub]
  simp [xor_all_ones_uint256_word]

@[simp] theorem evalPureBuiltinViaEvmYulLean_shl_native (shift value : Nat) :
    evalPureBuiltinViaEvmYulLean "shl" [shift, value] =
      some (if shift % Compiler.Constants.evmModulus < 256 then
        ((value % Compiler.Constants.evmModulus) *
          2 ^ (shift % Compiler.Constants.evmModulus)) % Compiler.Constants.evmModulus
      else
        0) := by
  rw [← uint256_size_eq_evmModulus]
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftLeft (EvmYul.UInt256.ofNat value) (EvmYul.UInt256.ofNat shift))) =
    some (if shift % EvmYul.UInt256.size < 256 then
      ((value % EvmYul.UInt256.size) * 2 ^ (shift % EvmYul.UInt256.size)) %
        EvmYul.UInt256.size
    else
      0)
  by_cases hs : shift % EvmYul.UInt256.size < 256
  · have hs' : ¬ 256 ≤ (EvmYul.UInt256.ofNat shift).val := by
      change ¬ 256 ≤ shift % EvmYul.UInt256.size
      exact Nat.not_le_of_lt hs
    simp [hs, EvmYul.UInt256.shiftLeft, EvmYul.UInt256.toNat, hs', Nat.shiftLeft_eq]
    change (value % EvmYul.UInt256.size) * 2 ^ (shift % EvmYul.UInt256.size) %
        EvmYul.UInt256.size =
      value * 2 ^ (shift % EvmYul.UInt256.size) % EvmYul.UInt256.size
    rw [Nat.mul_mod, Nat.mul_mod]
    simp
  · have hs' : 256 ≤ (EvmYul.UInt256.ofNat shift).val := by
      change 256 ≤ shift % EvmYul.UInt256.size
      exact Nat.not_lt.mp hs
    simp [hs, EvmYul.UInt256.shiftLeft, EvmYul.UInt256.toNat, hs']

@[simp] theorem evalPureBuiltinViaEvmYulLean_shr_native (shift value : Nat) :
    evalPureBuiltinViaEvmYulLean "shr" [shift, value] =
      some (if shift % Compiler.Constants.evmModulus < 256 then
        (value % Compiler.Constants.evmModulus) /
          2 ^ (shift % Compiler.Constants.evmModulus)
      else
        0) := by
  rw [← uint256_size_eq_evmModulus]
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftRight (EvmYul.UInt256.ofNat value) (EvmYul.UInt256.ofNat shift))) =
    some (if shift % EvmYul.UInt256.size < 256 then
      (value % EvmYul.UInt256.size) / 2 ^ (shift % EvmYul.UInt256.size)
    else
      0)
  by_cases hs : shift % EvmYul.UInt256.size < 256
  · have hs' : ¬ 256 ≤ (EvmYul.UInt256.ofNat shift).val := by
      change ¬ 256 ≤ shift % EvmYul.UInt256.size
      exact Nat.not_le_of_lt hs
    simp [hs, EvmYul.UInt256.shiftRight, EvmYul.UInt256.toNat, hs', Nat.shiftRight_eq_div_pow]
    change value % EvmYul.UInt256.size / 2 ^ (shift % EvmYul.UInt256.size) =
      value % EvmYul.UInt256.size / 2 ^ (shift % EvmYul.UInt256.size)
    rfl
  · have hs' : 256 ≤ (EvmYul.UInt256.ofNat shift).val := by
      change 256 ≤ shift % EvmYul.UInt256.size
      exact Nat.not_lt.mp hs
    simp [hs, EvmYul.UInt256.shiftRight, EvmYul.UInt256.toNat, hs']

private theorem nat_land_0xFF (n : Nat) : Nat.land n 255 = n % 256 := by
  rw [show (255 : Nat) = 2 ^ 8 - 1 from by omega]
  exact Nat.and_two_pow_sub_one_eq_mod n 8

set_option maxHeartbeats 16000000 in
private theorem evalPureBuiltinViaEvmYulLean_byte_normalized (index value : Nat) :
    evalPureBuiltinViaEvmYulLean "byte" [index, value] =
      (if index % EvmYul.UInt256.size > 31 then some 0
       else some ((value % EvmYul.UInt256.size /
          2 ^ ((31 - index % EvmYul.UInt256.size) * 8)) % 256)) := by
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.byteAt (EvmYul.UInt256.ofNat index) (EvmYul.UInt256.ofNat value))) = _
  by_cases hgt : index % EvmYul.UInt256.size > 31
  · have hgt' : EvmYul.UInt256.ofNat index > (⟨31⟩ : EvmYul.UInt256) := by
      show (31 : Fin EvmYul.UInt256.size) < (EvmYul.UInt256.ofNat index).val
      show (31 : Nat) < index % EvmYul.UInt256.size
      exact hgt
    simp [hgt, EvmYul.UInt256.byteAt, hgt', EvmYul.UInt256.toNat]
  · have hle' : ¬(EvmYul.UInt256.ofNat index > (⟨31⟩ : EvmYul.UInt256)) := by
      show ¬((31 : Fin EvmYul.UInt256.size) < (EvmYul.UInt256.ofNat index).val)
      show ¬((31 : Nat) < index % EvmYul.UInt256.size)
      exact hgt
    have hshift_small : (31 - index % EvmYul.UInt256.size) * 8 < EvmYul.UInt256.size := by
      unfold EvmYul.UInt256.size; omega
    have hguard : ¬ 256 ≤ (EvmYul.UInt256.ofNat
        ((31 - (EvmYul.UInt256.ofNat index).toNat) * 8)).val := by
      change ¬ 256 ≤ ((31 - index % EvmYul.UInt256.size) * 8) % EvmYul.UInt256.size
      rw [Nat.mod_eq_of_lt hshift_small]; omega
    have hofNat_toNat : (EvmYul.UInt256.ofNat index).toNat =
        index % EvmYul.UInt256.size := rfl
    unfold EvmYul.UInt256.byteAt
    rw [if_neg hle']
    show some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.land
          (EvmYul.UInt256.shiftRight (EvmYul.UInt256.ofNat value)
            (EvmYul.UInt256.ofNat ((31 - (EvmYul.UInt256.ofNat index).toNat) * 8)))
          ⟨255⟩)) = _
    unfold EvmYul.UInt256.shiftRight
    rw [if_neg hguard]
    rw [hofNat_toNat]
    simp only [hgt, ite_false, EvmYul.UInt256.land, EvmYul.UInt256.toNat,
      EvmYul.UInt256.ofNat, Id.run, Fin.land, Fin.shiftRight, Fin.ofNat,
      Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt hshift_small]
    rw [show (255 : Nat) % EvmYul.UInt256.size = 255 from by unfold EvmYul.UInt256.size; omega]
    have hdiv_lt :
        value % EvmYul.UInt256.size / 2 ^ ((31 - index % EvmYul.UInt256.size) * 8) <
          EvmYul.UInt256.size :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
        (Nat.mod_lt value (by unfold EvmYul.UInt256.size; omega))
    rw [Nat.mod_eq_of_lt hdiv_lt]
    rw [nat_land_0xFF]
    have hmod256_lt_size :
        (value % EvmYul.UInt256.size / 2 ^ ((31 - index % EvmYul.UInt256.size) * 8)) %
          256 < EvmYul.UInt256.size :=
      Nat.lt_trans (Nat.mod_lt _ (by omega)) (by unfold EvmYul.UInt256.size; omega)
    rw [Nat.mod_eq_of_lt hmod256_lt_size]

@[simp] theorem evalPureBuiltinViaEvmYulLean_byte_native (index value : Nat) :
    evalPureBuiltinViaEvmYulLean "byte" [index, value] =
      some (Verity.Core.Uint256.byte
        (Verity.Core.Uint256.ofNat (index % Compiler.Constants.evmModulus))
        (Verity.Core.Uint256.ofNat (value % Compiler.Constants.evmModulus))).val := by
  rw [evalPureBuiltinViaEvmYulLean_byte_normalized]
  have hindexMod :
      index % Compiler.Constants.evmModulus % Verity.Core.Uint256.modulus =
        index % Compiler.Constants.evmModulus := by
    simp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
  have hvalueMod :
      value % Compiler.Constants.evmModulus % Verity.Core.Uint256.modulus =
        value % Compiler.Constants.evmModulus := by
    simp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
  rw [uint256_size_eq_evmModulus]
  simp [Verity.Core.Uint256.byte, hindexMod, hvalueMod]
  by_cases hgt : 31 < index % Compiler.Constants.evmModulus
  · simp [hgt]
  · simp [hgt, Nat.shiftRight_eq_div_pow]
    rw [show (255 : Nat) = 2 ^ 8 - 1 by omega]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    rw [show (2 ^ 8 : Nat) = 256 by norm_num]
    have hlt :
        (value % Compiler.Constants.evmModulus /
            2 ^ ((31 - index % Compiler.Constants.evmModulus) * 8)) %
          256 < Verity.Core.Uint256.modulus :=
      Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < 256))
        (by norm_num [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS])
    rw [Nat.mod_eq_of_lt hlt]

end Compiler.Proofs.YulGeneration.Backends
