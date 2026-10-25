import Compiler.Constants
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanSignedArithSpec
import EvmYul.UInt256
import Mathlib.Data.Nat.Bitwise
import Verity.Core.Int256
import Verity.Core.Uint256

namespace Compiler.Proofs.YulGeneration.Backends

private theorem fin_val_mul_neg1 (n x : Nat) (hn : 0 < n) (hx : x < n) (hxpos : 0 < x) :
    (x * (n - 1)) % n = n - x := by
  have h1le : 1 ≤ n := hn
  have hadd : x * (n - 1) + x = x * n := by
    have : x * (n - 1) + x * 1 = x * n := by
      rw [← Nat.left_distrib, Nat.sub_add_cancel h1le]
    rwa [Nat.mul_one] at this
  have h1lex : 1 ≤ x := hxpos
  have hadd2 : (x - 1) * n + n = x * n := by
    have : (x - 1) * n + 1 * n = x * n := by
      rw [← Nat.right_distrib, Nat.sub_add_cancel h1lex]
    rwa [Nat.one_mul] at this
  have hdiv : x * (n - 1) = (x - 1) * n + (n - x) := by omega
  rw [hdiv]
  exact Nat.mul_add_mod_of_lt (by omega)

/- Lean 4.31 keeps the `Fin UInt256.size` instance in the elaborated term.
State this normalization at that exact modulus, rather than rewriting the
dependent size parameter to its numeral. -/
private theorem uint256_neg_val (x : Nat) (hx : x < EvmYul.UInt256.size)
    (hxpos : 0 < x) :
    x * (EvmYul.UInt256.size - 1 % EvmYul.UInt256.size) % EvmYul.UInt256.size =
      EvmYul.UInt256.size - x := by
  have hsize : 0 < EvmYul.UInt256.size := by
    unfold EvmYul.UInt256.size
    positivity
  have hone : 1 % EvmYul.UInt256.size = 1 := Nat.mod_eq_of_lt (by omega)
  rw [hone]
  exact fin_val_mul_neg1 EvmYul.UInt256.size x hsize hx hxpos

/-- The corresponding normalization while retaining the exact dependent
`Fin UInt256.size` type.  Keeping this lemma at the original modulus avoids
rewriting a type-indexed multiplication through the numeral representation. -/
private theorem uint256_fin_mul_neg1_val (x : Fin EvmYul.UInt256.size)
    (hxpos : 0 < x.val) :
    (x * (-1 : Fin EvmYul.UInt256.size)).val = EvmYul.UInt256.size - x.val := by
  change x.val * (EvmYul.UInt256.size - 1 % EvmYul.UInt256.size) %
    EvmYul.UInt256.size = EvmYul.UInt256.size - x.val
  exact uint256_neg_val x.val x.isLt hxpos

private theorem uint256_fin_zero_mul_neg1_val :
    ((0 : Fin EvmYul.UInt256.size) * (-1 : Fin EvmYul.UInt256.size)).val = 0 := by
  simp

private theorem uint256_fin_mul_neg1_val_of_zero (x : Fin EvmYul.UInt256.size)
    (hx : x.val = 0) :
    (x * (-1 : Fin EvmYul.UInt256.size)).val = 0 := by
  have hzero : x = 0 := Fin.ext hx
  subst x
  exact uint256_fin_zero_mul_neg1_val

private theorem natAbs_ofNat_sub (a b : Nat) (h : a < b) :
    (Int.ofNat a - Int.ofNat b).natAbs = b - a := by
  simp only [Int.ofNat_eq_natCast]
  rw [show (a : Int) - ((b : Nat) : Int) = -(((b : Nat) : Int) - (a : Int)) from by omega]
  rw [Int.natAbs_neg]
  rw [show ((b : Nat) : Int) - (a : Int) = ((b - a : Nat) : Int) from by omega]
  simp only [Int.natAbs_natCast]

/-- Value of the negated-quotient word produced by `Int256.div` in the mixed-sign cases. -/
private theorem int256_neg_quot_word_val (q : Nat) (hq : q < EvmYul.UInt256.size) (h1 h2) :
    (if 0 < q then ({ word := ⟨(2 ^ 256 - q % 2 ^ 256) % 2 ^ 256, h1⟩ } : Verity.Core.Int256)
      else { word := ⟨0, h2⟩ }).word.val =
    ((⟨q, hq⟩ : Fin EvmYul.UInt256.size) * -1).val := by
  have hqlt : q < 2 ^ 256 := by simpa [EvmYul.UInt256.size] using hq
  split
  · rename_i hqpos
    have hneg := uint256_fin_mul_neg1_val ⟨q, hq⟩ hqpos
    have hsub_lt : 2 ^ 256 - q < 2 ^ 256 := by omega
    show (2 ^ 256 - q % 2 ^ 256) % 2 ^ 256 = _
    rw [Nat.mod_eq_of_lt hqlt, Nat.mod_eq_of_lt hsub_lt, hneg]
    rfl
  · rename_i hq0
    have hzero := uint256_fin_mul_neg1_val_of_zero ⟨q, hq⟩ (by simpa using hq0)
    simpa using hzero.symm

/-- `sdiv` case of `int256_div_toUint256_val_eq_uint256_sdiv`: zero divisor. -/
private theorem int256_div_toUint256_val_eq_uint256_sdiv_of_zero (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus)
    (hb0 : b = 0) :
    (Verity.Core.Int256.div
      (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
      (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.sdiv ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                                               ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) := by
  unfold Compiler.Constants.evmModulus at ha hb
  subst hb0
  simp only [Verity.Core.Int256.div, Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
    Verity.Core.Int256.signBit, Verity.Core.Int256.signedAbsNat,
    Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
    Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    Verity.Core.Uint256.ofNat,
    EvmYul.UInt256.sdiv, EvmYul.UInt256.abs, EvmYul.UInt256.toNat,
    EvmYul.UInt256.size,
    HDiv.hDiv, Div.div, EvmYul.UInt256.div, Fin.div]
  simp only [show (0 : Nat) < 2^255 from by omega,
    show ¬(2^255 ≤ (0:Nat)) from by omega, ↓reduceIte]
  norm_num
  conv_rhs => simp only [show ∀ (n : Nat), Nat.div n 0 = 0 from Nat.div_zero]
  split <;> simp [Neg.neg] <;> decide

/-- `sdiv` case of `int256_div_toUint256_val_eq_uint256_sdiv`: both operands non-negative. -/
private theorem int256_div_toUint256_val_eq_uint256_sdiv_of_pos_pos (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus)
    (hb0 : b ≠ 0) (haS : a < 2 ^ 255) (hbS : b < 2 ^ 255) :
    (Verity.Core.Int256.div
      (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
      (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.sdiv ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                                               ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) := by
  unfold Compiler.Constants.evmModulus at ha hb
  simp only [Verity.Core.Int256.div, Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
    Verity.Core.Int256.signBit, Verity.Core.Int256.signedAbsNat,
    Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
    Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    Verity.Core.Uint256.ofNat,
    EvmYul.UInt256.sdiv, EvmYul.UInt256.abs, EvmYul.UInt256.toNat,
    EvmYul.UInt256.size]
  simp only [eq_true haS, eq_true hbS, ↓reduceIte,
    eq_false (show ¬(2^255 ≤ a) from by omega),
    eq_false (show ¬(2^255 ≤ b) from by omega),
    eq_false (show ¬((Int.ofNat b : Int) = 0) from Int.ofNat_ne_zero.mpr hb0),
    eq_false (show ¬(Int.ofNat a < (0 : Int)) from not_lt.mpr (Int.natCast_nonneg a)),
    eq_false (show ¬(Int.ofNat b < (0 : Int)) from not_lt.mpr (Int.natCast_nonneg b)),
    decide_false]
  simp only [BEq.beq, decide_true, ↓reduceIte]
  simp only [Int.natAbs]
  simp only [eq_false (show ¬(Int.ofNat (a / b) < (0 : Int)) from
      not_lt.mpr (Int.natCast_nonneg _)), ↓reduceIte]
  simp only [Int.toNat]
  simp only [HDiv.hDiv, Div.div, EvmYul.UInt256.div, Fin.div]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha)

/-- `sdiv` case of `int256_div_toUint256_val_eq_uint256_sdiv`: non-negative dividend,
negative divisor. -/
private theorem int256_div_toUint256_val_eq_uint256_sdiv_of_pos_neg (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus)
    (haS : a < 2 ^ 255) (hbS : ¬ b < 2 ^ 255) :
    (Verity.Core.Int256.div
      (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
      (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.sdiv ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                                               ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) := by
  unfold Compiler.Constants.evmModulus at ha hb
  have hb' : (Int.ofNat b : Int) < Int.ofNat (2^256) := Int.ofNat_lt.mpr hb
  simp only [Verity.Core.Int256.div, Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
    Verity.Core.Int256.signBit, Verity.Core.Int256.signedAbsNat,
    Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
    Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    Verity.Core.Uint256.ofNat,
    EvmYul.UInt256.sdiv, EvmYul.UInt256.abs, EvmYul.UInt256.toNat,
    EvmYul.UInt256.size]
  simp only [eq_true haS, eq_false hbS,
    eq_false (show ¬(2^255 ≤ a) from by omega),
    eq_true (show 2^255 ≤ b from by omega), ↓reduceIte,
    eq_false (show ¬(Int.ofNat b - Int.ofNat (2^256) = (0 : Int)) from by omega),
    eq_false (show ¬(Int.ofNat a < (0 : Int)) from not_lt.mpr (Int.natCast_nonneg a)),
    eq_true (show Int.ofNat b - Int.ofNat (2^256) < (0 : Int) from by omega)]
  simp only [BEq.beq, decide_false]
  simp only [show (Int.ofNat a).natAbs = a from rfl, natAbs_ofNat_sub b (2^256) hb]
  simp only [HDiv.hDiv, Div.div, EvmYul.UInt256.div, Fin.div, Fin.mul]
  norm_num
  have habs := uint256_neg_val b (by simpa [EvmYul.UInt256.size] using hb) (by omega)
  simp only [habs]
  exact int256_neg_quot_word_val _ _ _ _

/-- `sdiv` case of `int256_div_toUint256_val_eq_uint256_sdiv`: negative dividend,
non-negative divisor. -/
private theorem int256_div_toUint256_val_eq_uint256_sdiv_of_neg_pos (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus)
    (hb0 : b ≠ 0) (haS : ¬ a < 2 ^ 255) (hbS : b < 2 ^ 255) :
    (Verity.Core.Int256.div
      (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
      (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.sdiv ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                                               ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) := by
  unfold Compiler.Constants.evmModulus at ha hb
  have ha' : (Int.ofNat a : Int) < Int.ofNat (2^256) := Int.ofNat_lt.mpr ha
  simp only [Verity.Core.Int256.div, Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
    Verity.Core.Int256.signBit, Verity.Core.Int256.signedAbsNat,
    Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
    Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    Verity.Core.Uint256.ofNat,
    EvmYul.UInt256.sdiv, EvmYul.UInt256.abs, EvmYul.UInt256.toNat,
    EvmYul.UInt256.size]
  simp only [eq_false haS, eq_true hbS,
    eq_true (show 2^255 ≤ a from by omega),
    eq_false (show ¬(2^255 ≤ b) from by omega), ↓reduceIte,
    eq_true (show Int.ofNat a - Int.ofNat (2^256) < (0 : Int) from by omega),
    eq_false (show ¬(Int.ofNat b < (0 : Int)) from not_lt.mpr (Int.natCast_nonneg b)),
    eq_false (show ¬((Int.ofNat b : Int) = 0) from Int.ofNat_ne_zero.mpr hb0)]
  simp only [BEq.beq, decide_false]
  simp only [natAbs_ofNat_sub a (2^256) ha, show (Int.ofNat b).natAbs = b from rfl]
  simp only [HDiv.hDiv, Div.div, EvmYul.UInt256.div, Fin.div, Fin.mul]
  norm_num
  have habs := uint256_neg_val a (by simpa [EvmYul.UInt256.size] using ha) (by omega)
  simp only [habs]
  exact int256_neg_quot_word_val _ _ _ _

/-- `sdiv` case of `int256_div_toUint256_val_eq_uint256_sdiv`: both operands negative. -/
private theorem int256_div_toUint256_val_eq_uint256_sdiv_of_neg_neg (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus)
    (haS : ¬ a < 2 ^ 255) (hbS : ¬ b < 2 ^ 255) :
    (Verity.Core.Int256.div
      (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
      (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.sdiv ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                                               ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) := by
  unfold Compiler.Constants.evmModulus at ha hb
  have ha' : (Int.ofNat a : Int) < Int.ofNat (2^256) := Int.ofNat_lt.mpr ha
  have hb' : (Int.ofNat b : Int) < Int.ofNat (2^256) := Int.ofNat_lt.mpr hb
  simp only [Verity.Core.Int256.div, Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
    Verity.Core.Int256.signBit, Verity.Core.Int256.signedAbsNat,
    Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
    Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    Verity.Core.Uint256.ofNat,
    EvmYul.UInt256.sdiv, EvmYul.UInt256.abs, EvmYul.UInt256.toNat,
    EvmYul.UInt256.size]
  simp only [eq_false haS, eq_false hbS,
    eq_true (show 2^255 ≤ a from by omega),
    eq_true (show 2^255 ≤ b from by omega), ↓reduceIte,
    eq_false (show ¬(Int.ofNat b - Int.ofNat (2^256) = (0 : Int)) from by omega),
    eq_true (show Int.ofNat a - Int.ofNat (2^256) < (0 : Int) from by omega),
    eq_true (show Int.ofNat b - Int.ofNat (2^256) < (0 : Int) from by omega)]
  simp only [BEq.beq]
  simp only [natAbs_ofNat_sub a (2^256) ha, natAbs_ofNat_sub b (2^256) hb]
  simp only [decide_true, ↓reduceIte,
    eq_false (show ¬(Int.ofNat ((2^256 - a) / (2^256 - b)) < (0 : Int)) from
      not_lt.mpr (Int.natCast_nonneg _))]
  simp only [Int.toNat]
  simp only [HDiv.hDiv, Div.div, EvmYul.UInt256.div, Fin.div, Fin.mul]
  norm_num
  rw [uint256_neg_val a (by simpa [EvmYul.UInt256.size] using ha) (by omega),
    uint256_neg_val b (by simpa [EvmYul.UInt256.size] using hb) (by omega)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))

set_option maxRecDepth 4096 in
theorem int256_div_toUint256_val_eq_uint256_sdiv (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.div
      (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
      (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.sdiv ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                                               ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) := by
  by_cases hb0 : b = 0
  · exact int256_div_toUint256_val_eq_uint256_sdiv_of_zero a b ha hb hb0
  · by_cases haS : a < 2 ^ 255 <;> by_cases hbS : b < 2 ^ 255
    · exact int256_div_toUint256_val_eq_uint256_sdiv_of_pos_pos a b ha hb hb0 haS hbS
    · exact int256_div_toUint256_val_eq_uint256_sdiv_of_pos_neg a b ha hb haS hbS
    · exact int256_div_toUint256_val_eq_uint256_sdiv_of_neg_pos a b ha hb hb0 haS hbS
    · exact int256_div_toUint256_val_eq_uint256_sdiv_of_neg_neg a b ha hb haS hbS

private theorem eq0_true_of_val_eq_zero (x : EvmYul.UInt256) (h : x.val = 0) :
    EvmYul.UInt256.eq0 x = true := by
  have hx : x = ⟨0⟩ := by cases x; exact congrArg EvmYul.UInt256.mk h
  subst hx; decide

private theorem eq0_false_of_val_ne_zero (x : EvmYul.UInt256) (h : x.val ≠ 0) :
    EvmYul.UInt256.eq0 x = false := by
  cases hb : EvmYul.UInt256.eq0 x with
  | false => rfl
  | true =>
    exfalso; apply h
    cases x with | mk v =>
    simp only [EvmYul.UInt256.eq0] at hb
    change (v == (0 : Fin EvmYul.UInt256.size)) = true at hb
    have hv : v = (0 : Fin EvmYul.UInt256.size) := of_decide_eq_true hb
    simp [hv]

private theorem int256_ofInt_nat_toUint256_val (r : Nat) (hr : r < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.ofInt (Int.ofNat r)).toUint256.val = r := by
  simp [Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
    Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
  exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using hr)

/-- Negative-wrapper counterpart to `int256_ofInt_nat_toUint256_val` used by
    the NP/NN sign cases of the `smod` core equivalence:
    `(Verity.Core.Int256.ofInt (-Int.ofNat r)).toUint256.val =
       if r = 0 then 0 else Compiler.Constants.evmModulus - r`. -/
private theorem int256_ofInt_neg_nat_toUint256_val (r : Nat) (hr : r < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.ofInt (-Int.ofNat r)).toUint256.val =
      if r = 0 then 0 else Compiler.Constants.evmModulus - r := by
  by_cases hr0 : r = 0
  · subst hr0
    simp [Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
          Verity.Core.Int256.ofUint256, Verity.Core.Uint256.ofNat]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hneg : (-Int.ofNat r : Int) < 0 := by
      have : (0 : Int) < Int.ofNat r := Int.natCast_pos.mpr hrpos
      omega
    have hnatAbs : Int.natAbs (-Int.ofNat r) = r := by
      simp [Int.natAbs_neg]
    have hmod_eq : Verity.Core.Int256.modulus = Compiler.Constants.evmModulus := by
      simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
            Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
    have hr_lt_mod : r < Verity.Core.Int256.modulus := by rw [hmod_eq]; exact hr
    have hmod_r : r % Verity.Core.Int256.modulus = r := Nat.mod_eq_of_lt hr_lt_mod
    have hsub_lt : Verity.Core.Int256.modulus - r < Verity.Core.Int256.modulus := by
      have : 0 < Verity.Core.Int256.modulus := by rw [hmod_eq]; unfold Compiler.Constants.evmModulus; omega
      omega
    rw [if_neg hr0]
    simp only [Verity.Core.Int256.ofInt, if_pos hneg,
      Verity.Core.Int256.toUint256, Verity.Core.Int256.ofUint256,
      Verity.Core.Uint256.ofNat, hnatAbs, hmod_r]
    show (Verity.Core.Int256.modulus - r) % Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus - r
    have hmod_eq' : Verity.Core.Int256.modulus = Verity.Core.Uint256.modulus := rfl
    rw [hmod_eq', Nat.mod_eq_of_lt (by rw [← hmod_eq']; exact hsub_lt)]
    show Verity.Core.Uint256.modulus - r = Compiler.Constants.evmModulus - r
    rw [hmod_eq.symm.trans hmod_eq']

/-! ### Verity-side reduction for A2

The next three lemmas reduce Verity's `Int256.signedAbsNat ∘ toInt` on a
word to the Nat-level `SignedArithSpec.specAbs`, and reduce the sign
tests on `(ofUint256 ⟨n, _⟩ : Int)` to comparisons on `n`. They compose
into `int256_mod_toUint256_val_eq_smodSpec`, which is the Verity-side
half of the `smod` core equivalence (A2). -/

private theorem int256_ofUint256_coe_eq (a : Nat) (ha : a < Compiler.Constants.evmModulus) :
    ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) =
      if a < SignedArithSpec.specSignBit then Int.ofNat a
      else Int.ofNat a - Int.ofNat Verity.Core.Int256.modulus := by
  show Verity.Core.Int256.toInt _ = _
  unfold Verity.Core.Int256.toInt
  have hword : (Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256).word.val = a := rfl
  have hSB : SignedArithSpec.specSignBit = Verity.Core.Int256.signBit := rfl
  rw [hword, hSB]

private theorem evmModulus_eq_specModulus : Compiler.Constants.evmModulus = SignedArithSpec.specModulus := rfl

private theorem int256_modulus_eq_specModulus :
    Verity.Core.Int256.modulus = SignedArithSpec.specModulus := by
  simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
        Verity.Core.UINT256_MODULUS, SignedArithSpec.specModulus]

private theorem signedAbsNat_of_ofUint256 (a : Nat) (ha : a < Compiler.Constants.evmModulus) :
    Verity.Core.Int256.signedAbsNat
      ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) =
    SignedArithSpec.specAbs a := by
  unfold Verity.Core.Int256.signedAbsNat SignedArithSpec.specAbs
  rw [int256_ofUint256_coe_eq a ha]
  have hMod : Verity.Core.Int256.modulus = Compiler.Constants.evmModulus := by
    simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
          Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
  by_cases hS : a < SignedArithSpec.specSignBit
  · rw [if_pos hS, if_pos hS]
    show (Int.ofNat a).natAbs = a
    rfl
  · rw [if_neg hS, if_neg hS]
    have ha' : a < Verity.Core.Int256.modulus := by rw [hMod]; exact ha
    have hle : a ≤ Verity.Core.Int256.modulus := Nat.le_of_lt ha'
    have hcast : (Int.ofNat (Verity.Core.Int256.modulus - a) : Int) =
                 Int.ofNat Verity.Core.Int256.modulus - Int.ofNat a :=
      Int.ofNat_sub hle
    have hsub : Int.ofNat a - Int.ofNat Verity.Core.Int256.modulus =
                -(Int.ofNat (Verity.Core.Int256.modulus - a)) := by
      rw [hcast]; ring
    rw [hsub, Int.natAbs_neg]
    show Verity.Core.Int256.modulus - a = SignedArithSpec.specModulus - a
    rw [int256_modulus_eq_specModulus]

private theorem int256_coe_lt_zero_iff (a : Nat) (ha : a < Compiler.Constants.evmModulus) :
    ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) < 0 ↔
    SignedArithSpec.specSignBit ≤ a := by
  rw [int256_ofUint256_coe_eq a ha]
  have hMod : Verity.Core.Int256.modulus = Compiler.Constants.evmModulus := by
    simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
          Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
  have ha' : a < Verity.Core.Int256.modulus := by rw [hMod]; exact ha
  by_cases hS : a < SignedArithSpec.specSignBit
  · rw [if_pos hS]
    have hnn : (0 : Int) ≤ Int.ofNat a := Int.natCast_nonneg a
    constructor
    · intro h; omega
    · intro h; exact absurd h (Nat.not_le.mpr hS)
  · rw [if_neg hS]
    have hge : SignedArithSpec.specSignBit ≤ a := Nat.le_of_not_lt hS
    have hlt_int : Int.ofNat a < Int.ofNat Verity.Core.Int256.modulus := Int.ofNat_lt.mpr ha'
    constructor
    · intro _; exact hge
    · intro _; omega

private theorem int256_coe_eq_zero_iff (a : Nat) (ha : a < Compiler.Constants.evmModulus) :
    ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) = 0 ↔
    a = 0 := by
  rw [int256_ofUint256_coe_eq a ha]
  have hMod : Verity.Core.Int256.modulus = Compiler.Constants.evmModulus := by
    simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
          Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
  have ha' : a < Verity.Core.Int256.modulus := by rw [hMod]; exact ha
  by_cases hS : a < SignedArithSpec.specSignBit
  · rw [if_pos hS]; exact Int.ofNat_eq_zero
  · rw [if_neg hS]
    have hge : SignedArithSpec.specSignBit ≤ a := Nat.le_of_not_lt hS
    have hSBpos : 0 < SignedArithSpec.specSignBit := SignedArithSpec.specSignBit_pos
    constructor
    · intro h
      have : Int.ofNat a < Int.ofNat Verity.Core.Int256.modulus := Int.ofNat_lt.mpr ha'
      omega
    · intro h; subst h; exact absurd hge (Nat.not_le.mpr hSBpos)

/-- The signed magnitude of a nonzero word is positive. -/
private theorem specAbs_pos_of_ne_zero (b : Nat) (hb : b < Compiler.Constants.evmModulus)
    (hb0 : b ≠ 0) : 0 < SignedArithSpec.specAbs b := by
  unfold SignedArithSpec.specAbs
  by_cases hbs : b < SignedArithSpec.specSignBit
  · simp [hbs]; exact Nat.pos_of_ne_zero hb0
  · simp [hbs]
    have hbmod : b < SignedArithSpec.specModulus := hb
    omega

/-- The remainder of two signed magnitudes fits in a word. -/
private theorem specAbs_mod_lt_evmModulus (a b : Nat) (hpos : 0 < SignedArithSpec.specAbs b) :
    SignedArithSpec.specAbs a % SignedArithSpec.specAbs b < Compiler.Constants.evmModulus := by
  have hr := Nat.mod_lt (SignedArithSpec.specAbs a) hpos
  have habs_b_le := SignedArithSpec.specAbs_le_specSignBit b
  have hSBlt := SignedArithSpec.specSignBit_lt_specModulus
  show _ < SignedArithSpec.specModulus
  omega

/-- Verity-side half of A2: `Int256.mod`'s `.toUint256.val` view
reduces exactly to `smodSpec` at the Nat level. Composes
`int256_ofInt_nat_toUint256_val` / `int256_ofInt_neg_nat_toUint256_val`
for the non-negative/negative `a` sign cases with the sign-case
characterizations `smodSpec_of_nonneg` / `smodSpec_of_neg`. -/
private theorem int256_mod_toUint256_val_eq_smodSpec (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.mod
      (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
      (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)).toUint256.val =
    SignedArithSpec.smodSpec a b := by
  unfold Verity.Core.Int256.mod
  have hzero_b := int256_coe_eq_zero_iff b hb
  have hneg_a := int256_coe_lt_zero_iff a ha
  by_cases hb0 : b = 0
  · subst hb0
    simp only [hzero_b.mpr rfl, if_true]
    show ((0 : Verity.Core.Int256) : Verity.Core.Uint256).val = _
    rw [SignedArithSpec.smodSpec_b_zero]
    rfl
  · have hrhs_ne : ((Verity.Core.Int256.ofUint256 ⟨b, hb⟩ : Verity.Core.Int256) : Int) ≠ 0 := by
      intro h; exact hb0 (hzero_b.mp h)
    simp only [hrhs_ne, if_false]
    have hr_lt_mod := specAbs_mod_lt_evmModulus a b (specAbs_pos_of_ne_zero b hb hb0)
    rw [signedAbsNat_of_ofUint256 a ha, signedAbsNat_of_ofUint256 b hb]
    by_cases haS : a < SignedArithSpec.specSignBit
    · have hnlt : ¬ ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) < 0 := by
        rw [hneg_a]; exact Nat.not_le.mpr haS
      simp only [hnlt, if_false]
      rw [int256_ofInt_nat_toUint256_val _ hr_lt_mod]
      rw [SignedArithSpec.smodSpec_of_nonneg a b haS hb0]
    · have hge : SignedArithSpec.specSignBit ≤ a := Nat.le_of_not_lt haS
      have hlt : ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) < 0 := by
        rw [hneg_a]; exact hge
      simp only [hlt, if_true]
      rw [int256_ofInt_neg_nat_toUint256_val _ hr_lt_mod]
      rw [SignedArithSpec.smodSpec_of_neg a b hge hb0]
      rw [evmModulus_eq_specModulus]

/-! ### EVMYulLean-side abs reduction for A2

Mirror of the Verity-side `signedAbsNat_of_ofUint256` helper: reduces
`EvmYul.UInt256.abs` on a raw-Nat word to `SignedArithSpec.specAbs`. The
negative branch applies `fin_val_mul_neg1` to collapse Fin-multiplication
by `-1` into two's-complement subtraction. Future A2b work can compose
this with `smodSpec_of_nonneg`/`_of_neg` + `toSigned` characterizations to
close the EVMYulLean side of the `smod` core equivalence, symmetric to
`int256_mod_toUint256_val_eq_smodSpec` on the Verity side. -/
private theorem uint256_abs_toNat_eq_specAbs (a : Nat) (ha : a < Compiler.Constants.evmModulus) :
    EvmYul.UInt256.toNat
      (EvmYul.UInt256.abs ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩) =
    SignedArithSpec.specAbs a := by
  unfold Compiler.Constants.evmModulus at ha
  unfold EvmYul.UInt256.abs EvmYul.UInt256.toNat SignedArithSpec.specAbs
  by_cases haS : a < SignedArithSpec.specSignBit
  · -- Non-negative branch: abs returns the value unchanged, specAbs returns `a`.
    have hnot : ¬ (2^255 ≤ a) := by
      have : a < 2^255 := haS
      omega
    show (if 2^255 ≤ a then _ else (⟨⟨a, _⟩⟩ : EvmYul.UInt256)).val.val =
         if a < SignedArithSpec.specSignBit then a else SignedArithSpec.specModulus - a
    rw [if_neg hnot, if_pos haS]
  · -- Negative branch: abs returns `⟨a.val * (-1)⟩`; specAbs returns `specModulus - a`.
    have hge : 2^255 ≤ a := by
      have hnot : ¬ a < SignedArithSpec.specSignBit := haS
      have : SignedArithSpec.specSignBit = 2^255 := rfl
      omega
    have hpos : 0 < a := by
      have h255 : 0 < (2 : Nat)^255 := by positivity
      omega
    show (if 2^255 ≤ a then (⟨⟨a, _⟩ * (-1 : Fin EvmYul.UInt256.size)⟩ : EvmYul.UInt256)
          else _).val.val =
         if a < SignedArithSpec.specSignBit then a else SignedArithSpec.specModulus - a
    rw [if_pos hge, if_neg haS]
    show ((⟨a, _⟩ : Fin EvmYul.UInt256.size) * (-1 : Fin EvmYul.UInt256.size)).val =
         SignedArithSpec.specModulus - a
    change a * (EvmYul.UInt256.size - 1 % EvmYul.UInt256.size) %
        EvmYul.UInt256.size = SignedArithSpec.specModulus - a
    rw [uint256_neg_val a (by simpa [EvmYul.UInt256.size] using ha) hpos]
    rfl

/-! ### EVMYulLean-side mod reduction to Nat-level mod (for A2b)

Reduces `(a % b : UInt256).toNat` to `a.toNat % b.toNat` under the nonzero
hypothesis on `b` (the zero branch forces a `0` result on the UInt256 side
but yields `a` on the Nat side, so the conditional is necessary). This is
the straightforward `Fin.mod` unfolding needed to let the A2b composition
push `UInt256.mod` through to `Nat.mod`. -/
private theorem uint256_mod_toNat_of_nonzero
    (a b : EvmYul.UInt256) (hb : EvmYul.UInt256.toNat b ≠ 0) :
    EvmYul.UInt256.toNat (a % b) =
      EvmYul.UInt256.toNat a % EvmYul.UInt256.toNat b := by
  show EvmYul.UInt256.toNat (EvmYul.UInt256.mod a b) = _
  unfold EvmYul.UInt256.mod EvmYul.UInt256.toNat
  split_ifs with h
  · exfalso
    apply hb
    simp only [beq_iff_eq] at h
    show b.val.val = 0
    rw [h]; rfl
  · rfl

/-! ### EVMYulLean toSigned characterizations (A2b scaffolds)

Splits `toNat ∘ toSigned` by the `Int` constructor. `toSigned` is defined on
the Verity side as
```
match i with
  | .ofNat n     => ofNat n
  | .negSucc n   => ofNat (UInt256.size - 1 - n)
```
so `toNat` reduces to `n % size` and `(size - 1 - n) % size` respectively.
Bounded inputs remove the modulus, which is what A2b's case split needs. -/
private theorem uint256_toSigned_ofNat_toNat_of_lt
    (n : Nat) (hn : n < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.toSigned (Int.ofNat n)) = n := by
  show EvmYul.UInt256.toNat (EvmYul.UInt256.ofNat n) = n
  unfold EvmYul.UInt256.ofNat EvmYul.UInt256.toNat
  simp only [Id.run]
  show (Fin.ofNat EvmYul.UInt256.size n).val = n
  unfold Fin.ofNat
  exact Nat.mod_eq_of_lt hn

private theorem uint256_toSigned_negSucc_toNat_of_lt
    (n : Nat) (hn : n + 1 < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.toSigned (Int.negSucc n)) =
      EvmYul.UInt256.size - 1 - n := by
  show EvmYul.UInt256.toNat (EvmYul.UInt256.ofNat (EvmYul.UInt256.size - 1 - n)) = _
  unfold EvmYul.UInt256.ofNat EvmYul.UInt256.toNat
  simp only [Id.run]
  show (Fin.ofNat EvmYul.UInt256.size (EvmYul.UInt256.size - 1 - n)).val =
       EvmYul.UInt256.size - 1 - n
  unfold Fin.ofNat
  have h : EvmYul.UInt256.size - 1 - n < EvmYul.UInt256.size := by
    have hpos : 0 < EvmYul.UInt256.size := by
      unfold EvmYul.UInt256.size; decide
    omega
  exact Nat.mod_eq_of_lt h

/-! ### EVMYulLean-side smod reduction to smodSpec (A2c)

Symmetric to `int256_mod_toUint256_val_eq_smodSpec`: reduces
`toNat (UInt256.smod a b)` to `SignedArithSpec.smodSpec a.toNat b.toNat`.

The EVMYulLean definition is
```
smod a b = if b.toNat == 0 then ⟨0⟩
           else toSigned (sgn a * (abs a % abs b).toNat)
```
Each branch is discharged by composing the previously-landed scaffolds:

* Zero-divisor: direct from `smodSpec_b_zero`.
* Non-negative `a` (`a < specSignBit`), `a = 0`: `sgn = 0`, product `= 0 = Int.ofNat 0`, `toSigned` gives `0`; `smodSpec_a_zero` gives `0`.
* Non-negative `a`, `a ≠ 0`: `sgn = 1`, product `= Int.ofNat r` with `r < specSignBit < size`; `toSigned` collapses via `uint256_toSigned_ofNat_toNat_of_lt`; RHS matches `smodSpec_of_nonneg`.
* Negative `a` (`specSignBit ≤ a`), `r = 0`: `sgn * 0 = 0`; `toSigned 0 = 0`; RHS matches `smodSpec_of_neg` at its `r = 0` branch.
* Negative `a`, `r > 0`: `sgn * r = -r = Int.negSucc (r-1)`; `toSigned` collapses via `uint256_toSigned_negSucc_toNat_of_lt` to `size - r = specModulus - r`; RHS matches `smodSpec_of_neg`.
-/

/-- `toSigned` of zero is the zero word. -/
private theorem uint256_toSigned_zero_toNat :
    EvmYul.UInt256.toNat (EvmYul.UInt256.toSigned 0) = 0 :=
  uint256_toSigned_ofNat_toNat_of_lt 0 (by unfold EvmYul.UInt256.size; decide)

/-- `toSigned` of a negated positive magnitude is its two's complement. -/
private theorem uint256_toSigned_neg_toNat (r : Nat) (hr0 : ¬ r = 0)
    (hr : r < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.toSigned ((-1 : Int) * (r : Int))) =
      SignedArithSpec.specModulus - r := by
  have hprod : (-1 : Int) * (r : Int) = Int.negSucc (r - 1) := by
    cases h : r with
    | zero => exact False.elim (hr0 h)
    | succ k => simp [Int.negSucc_eq]
  rw [hprod, uint256_toSigned_negSucc_toNat_of_lt (r - 1) (by omega)]
  show EvmYul.UInt256.size - 1 - (r - 1) = SignedArithSpec.specModulus - r
  have h_eq : EvmYul.UInt256.size = SignedArithSpec.specModulus := rfl
  rw [h_eq]
  omega

/-- Sign-case core of `uint256_smod_toNat_eq_smodSpec` for a nonzero divisor. -/
private theorem uint256_toSigned_sgn_mul_mod_toNat (a b : Nat)
    (hsize_a : a < EvmYul.UInt256.size) (hb : b < Compiler.Constants.evmModulus)
    (hb0 : b ≠ 0) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.toSigned
      (EvmYul.UInt256.sgn ⟨⟨a, hsize_a⟩⟩ *
        ((SignedArithSpec.specAbs a % SignedArithSpec.specAbs b : Nat) : Int))) =
    SignedArithSpec.smodSpec a b := by
  have hr_lt := specAbs_mod_lt_evmModulus a b (specAbs_pos_of_ne_zero b hb hb0)
  unfold EvmYul.UInt256.sgn
  by_cases haS : a < SignedArithSpec.specSignBit
  · have h_not_neg : ¬ (2:Nat)^255 ≤ EvmYul.UInt256.toNat ⟨⟨a, hsize_a⟩⟩ :=
      Nat.not_le_of_lt haS
    simp only [h_not_neg, ↓reduceIte]
    by_cases ha0 : a = 0
    · subst ha0
      have h_eq0 : EvmYul.UInt256.eq0 ⟨⟨0, hsize_a⟩⟩ = true :=
        eq0_true_of_val_eq_zero _ (Fin.ext rfl)
      simp only [h_eq0, ↓reduceIte, zero_mul]
      rw [uint256_toSigned_zero_toNat, SignedArithSpec.smodSpec_a_zero]
    · have h_eq0 := eq0_false_of_val_ne_zero ⟨⟨a, hsize_a⟩⟩ (fun h => ha0 (congrArg Fin.val h))
      simp only [h_eq0, Bool.false_eq_true, ↓reduceIte, one_mul]
      rw [← Int.ofNat_eq_natCast, uint256_toSigned_ofNat_toNat_of_lt _ hr_lt,
        SignedArithSpec.smodSpec_of_nonneg a b haS hb0]
  · have hge : SignedArithSpec.specSignBit ≤ a := Nat.le_of_not_lt haS
    have h_is_neg : (2:Nat)^255 ≤ EvmYul.UInt256.toNat ⟨⟨a, hsize_a⟩⟩ := hge
    simp only [h_is_neg, ↓reduceIte]
    rw [SignedArithSpec.smodSpec_of_neg a b hge hb0]
    by_cases hr0 : SignedArithSpec.specAbs a % SignedArithSpec.specAbs b = 0
    · simp only [hr0, ↓reduceIte, Nat.cast_zero, mul_zero]
      exact uint256_toSigned_zero_toNat
    · simp only [hr0, ↓reduceIte]
      exact uint256_toSigned_neg_toNat _ hr0 hr_lt

/-- EVMYulLean-side half of A2: `UInt256.smod` reduces to `smodSpec`. -/
private theorem uint256_smod_toNat_eq_smodSpec (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus) :
    EvmYul.UInt256.toNat
      (EvmYul.UInt256.smod ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                           ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) =
    SignedArithSpec.smodSpec a b := by
  have hsize_a : a < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact ha
  have hsize_b : b < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hb
  unfold EvmYul.UInt256.smod
  by_cases hb0 : b = 0
  · subst hb0
    rw [SignedArithSpec.smodSpec_b_zero]
    rfl
  · have h_beq : (EvmYul.UInt256.toNat ⟨⟨b, hsize_b⟩⟩ == 0) = false := by
      simp [EvmYul.UInt256.toNat, hb0]
    rw [h_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hmod_toNat :
        EvmYul.UInt256.toNat
          (EvmYul.UInt256.abs ⟨⟨a, hsize_a⟩⟩ % EvmYul.UInt256.abs ⟨⟨b, hsize_b⟩⟩) =
        SignedArithSpec.specAbs a % SignedArithSpec.specAbs b := by
      rw [uint256_mod_toNat_of_nonzero, uint256_abs_toNat_eq_specAbs a ha,
        uint256_abs_toNat_eq_specAbs b hb]
      rw [uint256_abs_toNat_eq_specAbs b hb]
      exact (specAbs_pos_of_ne_zero b hb hb0).ne'
    rw [hmod_toNat]
    exact uint256_toSigned_sgn_mul_mod_toNat a b hsize_a hb hb0

/-- Core smod equivalence: Verity's `Int256.mod` agrees with EVMYulLean's `UInt256.smod`.

**Closed via A2a + A2c**: Verity-side reduction
`int256_mod_toUint256_val_eq_smodSpec` and EVMYulLean-side reduction
`uint256_smod_toNat_eq_smodSpec` both go through the shared
`SignedArithSpec.smodSpec`, and the composition discharges the wrapper. -/
theorem int256_mod_toUint256_val_eq_uint256_smod (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.mod
      (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
      (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.smod ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                                               ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) := by
  rw [int256_mod_toUint256_val_eq_smodSpec a b ha hb]
  rw [uint256_smod_toNat_eq_smodSpec a b ha hb]

private theorem uint256_lt_zero_false (value : Nat) (hv : value < EvmYul.UInt256.size) :
    ¬ ((⟨⟨value, hv⟩⟩ : EvmYul.UInt256) < ⟨0⟩) := by
  intro h
  change (⟨value, hv⟩ : Fin EvmYul.UInt256.size) < (0 : Fin EvmYul.UInt256.size) at h
  exact Nat.not_lt_zero _ h

private theorem uint256_complement_val (value : Nat) (hv : value < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.complement ⟨⟨value, hv⟩⟩) =
      EvmYul.UInt256.size - 1 - value := by
  simp [EvmYul.UInt256.complement, EvmYul.UInt256.toNat, Fin.add_def, Fin.neg_def]
  have hle : value + 1 ≤ EvmYul.UInt256.size := by omega
  by_cases hlast : value + 1 = EvmYul.UInt256.size
  · rw [hlast]
    simp
    omega
  · have hlt : value + 1 < EvmYul.UInt256.size := Nat.lt_of_le_of_ne hle hlast
    rw [Nat.mod_eq_of_lt hlt]
    have hsub_lt : EvmYul.UInt256.size - (value + 1) < EvmYul.UInt256.size := by
      unfold EvmYul.UInt256.size
      omega
    rw [Nat.mod_eq_of_lt hsub_lt]
    omega

private theorem uint256_complement_eq (value : Nat) (hv : value < EvmYul.UInt256.size) (hout) :
    EvmYul.UInt256.complement ⟨⟨value, hv⟩⟩ =
      ⟨⟨EvmYul.UInt256.size - 1 - value, hout⟩⟩ := by
  rw [EvmYul.UInt256.mk.injEq]
  apply Fin.ext
  exact uint256_complement_val value hv

private theorem uint256_shiftRight_val (value shift : Nat)
    (hv : value < EvmYul.UInt256.size) (hs : shift < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.shiftRight ⟨⟨value, hv⟩⟩ ⟨⟨shift, hs⟩⟩) =
      if shift < 256 then value / 2 ^ shift else 0 := by
  by_cases hshift : shift < 256
  · have hg : ¬ 256 ≤ (⟨⟨shift, hs⟩⟩ : EvmYul.UInt256).val := by
      change ¬ 256 ≤ shift
      exact Nat.not_le_of_lt hshift
    simp [EvmYul.UInt256.shiftRight, EvmYul.UInt256.toNat, hg, hshift,
      Nat.shiftRight_eq_div_pow]
  · have hg : 256 ≤ (⟨⟨shift, hs⟩⟩ : EvmYul.UInt256).val := by
      change 256 ≤ shift
      exact Nat.not_lt.mp hshift
    simp [EvmYul.UInt256.shiftRight, EvmYul.UInt256.toNat, hg, hshift]

/-- A non-negative word is not signed-less-than zero. -/
private theorem uint256_sltBool_zero_of_lt (value : Nat) (hv : value < EvmYul.UInt256.size)
    (hvalue : value < SignedArithSpec.specSignBit) :
    EvmYul.UInt256.sltBool (⟨⟨value, hv⟩⟩ : EvmYul.UInt256) ⟨0⟩ = false := by
  unfold EvmYul.UInt256.sltBool
  have hnotSign : ¬ 2 ^ 255 ≤ (⟨⟨value, hv⟩⟩ : EvmYul.UInt256).toNat := by
    change ¬ 2 ^ 255 ≤ value
    exact Nat.not_le_of_lt (by simpa [SignedArithSpec.specSignBit] using hvalue)
  rw [if_neg hnotSign]
  have hzeroNotSign : ¬ 2 ^ 255 ≤ (⟨0⟩ : EvmYul.UInt256).toNat := by decide
  rw [if_neg hzeroNotSign]
  simp [uint256_lt_zero_false value hv]

/-- A negative word is signed-less-than zero. -/
private theorem uint256_sltBool_zero_of_ge (value : Nat) (hv : value < EvmYul.UInt256.size)
    (hge : SignedArithSpec.specSignBit ≤ value) :
    EvmYul.UInt256.sltBool (⟨⟨value, hv⟩⟩ : EvmYul.UInt256) ⟨0⟩ = true := by
  unfold EvmYul.UInt256.sltBool
  have hsign : 2 ^ 255 ≤ (⟨⟨value, hv⟩⟩ : EvmYul.UInt256).toNat := by
    change 2 ^ 255 ≤ value
    simpa [SignedArithSpec.specSignBit] using hge
  rw [if_pos hsign]
  have hzeroNotSign : ¬ 2 ^ 255 ≤ (⟨0⟩ : EvmYul.UInt256).toNat := by decide
  rw [if_neg hzeroNotSign]

/-- `uint256_sar_toNat_eq_sarSpec` for a non-negative value. -/
private theorem uint256_sar_toNat_eq_sarSpec_of_nonneg (shift value : Nat)
    (hs : shift < EvmYul.UInt256.size) (hv : value < EvmYul.UInt256.size)
    (hvalue : value < SignedArithSpec.specSignBit) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.sar ⟨⟨shift, hs⟩⟩ ⟨⟨value, hv⟩⟩) =
      SignedArithSpec.sarSpec shift value := by
  unfold EvmYul.UInt256.sar
  rw [uint256_sltBool_zero_of_lt value hv hvalue]
  simp
  show EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftRight ⟨⟨value, hv⟩⟩ ⟨⟨shift, hs⟩⟩) =
    SignedArithSpec.sarSpec shift value
  rw [uint256_shiftRight_val value shift hv hs]
  by_cases hshift : shift < 256
  · rw [SignedArithSpec.sarSpec_of_nonneg shift value hshift hvalue]
    simp [hshift]
  · have hge : 256 ≤ shift := Nat.not_lt.mp hshift
    rw [SignedArithSpec.sarSpec_of_shift_ge_nonneg shift value hge hvalue]
    simp [hshift]

/-- Complement of a logical right shift, as a Nat. -/
private theorem uint256_complement_shiftRight_toNat (c shift : Nat)
    (hc : c < EvmYul.UInt256.size) (hs : shift < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat
        (EvmYul.UInt256.complement (EvmYul.UInt256.shiftRight ⟨⟨c, hc⟩⟩ ⟨⟨shift, hs⟩⟩)) =
      EvmYul.UInt256.size - 1 - (if shift < 256 then c / 2 ^ shift else 0) := by
  have hval := uint256_shiftRight_val c shift hc hs
  generalize EvmYul.UInt256.shiftRight ⟨⟨c, hc⟩⟩ ⟨⟨shift, hs⟩⟩ = x at hval ⊢
  obtain ⟨⟨w, hw⟩⟩ := x
  rw [uint256_complement_val w hw]
  change w = _ at hval
  rw [hval]

/-- `uint256_sar_toNat_eq_sarSpec` for a negative value. -/
private theorem uint256_sar_toNat_eq_sarSpec_of_neg (shift value : Nat)
    (hs : shift < EvmYul.UInt256.size) (hv : value < EvmYul.UInt256.size)
    (hge : SignedArithSpec.specSignBit ≤ value) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.sar ⟨⟨shift, hs⟩⟩ ⟨⟨value, hv⟩⟩) =
      SignedArithSpec.sarSpec shift value := by
  unfold EvmYul.UInt256.sar
  rw [uint256_sltBool_zero_of_ge value hv hge]
  simp
  have hc_lt : EvmYul.UInt256.size - 1 - value < EvmYul.UInt256.size := by
    unfold EvmYul.UInt256.size
    omega
  rw [uint256_complement_eq value hv hc_lt]
  refine (uint256_complement_shiftRight_toNat _ _ hc_lt hs).trans ?_
  by_cases hshift : shift < 256
  · rw [SignedArithSpec.sarSpec_of_neg shift value hshift hge, if_pos hshift]
    simp [EvmYul.UInt256.size, SignedArithSpec.specModulus]
  · rw [SignedArithSpec.sarSpec_of_shift_ge_neg shift value (Nat.not_lt.mp hshift) hge,
      if_neg hshift]
    simp [EvmYul.UInt256.size, SignedArithSpec.specModulus]

/-- EVMYulLean-side `sar` reduction through the shared Nat-level spec. -/
private theorem uint256_sar_toNat_eq_sarSpec (shift value : Nat)
    (hs : shift < EvmYul.UInt256.size) (hv : value < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.sar ⟨⟨shift, hs⟩⟩ ⟨⟨value, hv⟩⟩) =
      SignedArithSpec.sarSpec shift value := by
  by_cases hvalue : value < SignedArithSpec.specSignBit
  · exact uint256_sar_toNat_eq_sarSpec_of_nonneg shift value hs hv hvalue
  · exact uint256_sar_toNat_eq_sarSpec_of_neg shift value hs hv (Nat.le_of_not_lt hvalue)

private theorem int_two_pow_eq_nat (shift : Nat) :
    ((2 : Int) ^ shift) = Int.ofNat (2 ^ shift) := by
  induction shift with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, ih]
      norm_num

private theorem int_fdiv_ofNat_two_pow (value shift : Nat) :
    (Int.ofNat value).fdiv ((2 : Int) ^ shift) =
      Int.ofNat (value / 2 ^ shift) := by
  rw [int_two_pow_eq_nat]
  have hpos : 0 < 2 ^ shift := Nat.pow_pos (by decide : 0 < 2)
  cases hp : 2 ^ shift with
  | zero => omega
  | succ n =>
      cases value with
      | zero => simp [Int.fdiv]
      | succ m => simp [Int.fdiv]

private theorem int_sub_modulus_eq_negSucc (value : Nat)
    (_hge : SignedArithSpec.specSignBit ≤ value) (hv : value < Compiler.Constants.evmModulus) :
    Int.ofNat value - Int.ofNat Compiler.Constants.evmModulus =
      Int.negSucc (Compiler.Constants.evmModulus - 1 - value) := by
  unfold Compiler.Constants.evmModulus at hv ⊢
  rw [Int.negSucc_eq]
  have hdiff : 2 ^ 256 - 1 - value + 1 = 2 ^ 256 - value := by omega
  change Int.ofNat value - Int.ofNat (2 ^ 256) =
    -Int.ofNat ((2 ^ 256 - 1 - value) + 1)
  rw [hdiff]
  have hcast : Int.ofNat (2 ^ 256 - value) =
      Int.ofNat (2 ^ 256) - Int.ofNat value := by
    exact Int.ofNat_sub (Nat.le_of_lt hv)
  rw [hcast]
  omega

private theorem int_fdiv_neg_raw_two_pow (shift value : Nat)
    (hge : SignedArithSpec.specSignBit ≤ value) (hv : value < Compiler.Constants.evmModulus) :
    (Int.ofNat value - Int.ofNat Compiler.Constants.evmModulus).fdiv ((2 : Int) ^ shift) =
      Int.negSucc ((Compiler.Constants.evmModulus - 1 - value) / 2 ^ shift) := by
  rw [int_sub_modulus_eq_negSucc value hge hv]
  rw [int_two_pow_eq_nat]
  have hpos : 0 < 2 ^ shift := Nat.pow_pos (by decide : 0 < 2)
  cases hp : 2 ^ shift with
  | zero => omega
  | succ n =>
      simp [Int.fdiv]

private theorem int256_ofInt_negSucc_toUint256_val (n : Nat)
    (hn : n + 1 < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.ofInt (Int.negSucc n)).toUint256.val =
      Compiler.Constants.evmModulus - (n + 1) := by
  have hneg : (Int.negSucc n) < 0 := by simp
  have hnatAbs : (Int.negSucc n).natAbs = n + 1 := by
    have hnegSucc : Int.negSucc n = -Int.ofNat (n + 1) := by
      rw [Int.negSucc_eq]
      simp
    rw [hnegSucc, Int.natAbs_neg]
    exact Int.natAbs_natCast (n + 1)
  have hmod_eq : Verity.Core.Int256.modulus = Compiler.Constants.evmModulus := by
    simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
          Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
  have hn_lt_mod : n + 1 < Verity.Core.Int256.modulus := by
    rw [hmod_eq]
    exact hn
  have hmod_n : (n + 1) % Verity.Core.Int256.modulus = n + 1 :=
    Nat.mod_eq_of_lt hn_lt_mod
  have hsub_lt : Verity.Core.Int256.modulus - (n + 1) <
      Verity.Core.Int256.modulus := by
    have hpos_mod : 0 < Verity.Core.Int256.modulus := by
      rw [hmod_eq]
      unfold Compiler.Constants.evmModulus
      omega
    omega
  simp only [Verity.Core.Int256.ofInt, if_pos hneg,
    Verity.Core.Int256.toUint256, Verity.Core.Int256.ofUint256,
    Verity.Core.Uint256.ofNat, hnatAbs, hmod_n]
  show (Verity.Core.Int256.modulus - (n + 1)) %
      Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus - (n + 1)
  have hmod_eq' : Verity.Core.Int256.modulus = Verity.Core.Uint256.modulus := rfl
  rw [hmod_eq', Nat.mod_eq_of_lt (by rw [← hmod_eq']; exact hsub_lt)]
  show Verity.Core.Uint256.modulus - (n + 1) = Compiler.Constants.evmModulus - (n + 1)
  rw [← hmod_eq', hmod_eq]

/-- `toInt` of a non-negative raw word. -/
private theorem int256_toInt_of_lt_specSignBit (value : Nat)
    (hv : value < Compiler.Constants.evmModulus) (hval : value < SignedArithSpec.specSignBit) :
    ({ word := { val := value, isLt := hv } } : Verity.Core.Int256).toInt = Int.ofNat value := by
  rw [Verity.Core.Int256.toInt_of_lt_signBit]
  simpa [Verity.Core.Int256.signBit, SignedArithSpec.specSignBit] using hval

/-- `toInt` of a negative raw word. -/
private theorem int256_toInt_of_specSignBit_le (value : Nat)
    (hv : value < Compiler.Constants.evmModulus) (hge : SignedArithSpec.specSignBit ≤ value) :
    ({ word := { val := value, isLt := hv } } : Verity.Core.Int256).toInt =
      Int.ofNat value - Int.ofNat Compiler.Constants.evmModulus := by
  rw [Verity.Core.Int256.toInt_of_ge_signBit]
  · simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
      Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
  · simpa [Verity.Core.Int256.signBit, SignedArithSpec.specSignBit] using hge

/-- Verity-side `sar` for an in-range shift of a non-negative value. -/
private theorem int256_sar_val_of_lt_of_nonneg (shift value : Nat)
    (hv : value < Compiler.Constants.evmModulus) (hshift : shift < 256)
    (hval : value < SignedArithSpec.specSignBit) :
    (Verity.Core.Int256.ofInt
      (({ word := { val := value, isLt := hv } } : Verity.Core.Int256).toInt.fdiv
        (2 ^ shift))).word.val = SignedArithSpec.sarSpec shift value := by
  rw [int256_toInt_of_lt_specSignBit value hv hval,
    SignedArithSpec.sarSpec_of_nonneg shift value hshift hval, int_fdiv_ofNat_two_pow]
  exact int256_ofInt_nat_toUint256_val (value / 2 ^ shift)
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv)

/-- Verity-side `sar` for an in-range shift of a negative value. -/
private theorem int256_sar_val_of_lt_of_neg (shift value : Nat)
    (hv : value < Compiler.Constants.evmModulus) (hshift : shift < 256)
    (hge : SignedArithSpec.specSignBit ≤ value) :
    (Verity.Core.Int256.ofInt
      (({ word := { val := value, isLt := hv } } : Verity.Core.Int256).toInt.fdiv
        (2 ^ shift))).word.val = SignedArithSpec.sarSpec shift value := by
  rw [int256_toInt_of_specSignBit_le value hv hge,
    SignedArithSpec.sarSpec_of_neg shift value hshift hge,
    int_fdiv_neg_raw_two_pow shift value hge hv]
  have hn_bound : (Compiler.Constants.evmModulus - 1 - value) / 2 ^ shift + 1 <
      Compiler.Constants.evmModulus := by
    unfold Compiler.Constants.evmModulus at hv ⊢
    unfold SignedArithSpec.specSignBit at hge
    have hle : (2 ^ 256 - 1 - value) / 2 ^ shift ≤ 2 ^ 256 - 1 - value := Nat.div_le_self _ _
    omega
  refine (int256_ofInt_negSucc_toUint256_val _ hn_bound).trans ?_
  unfold SignedArithSpec.specModulus Compiler.Constants.evmModulus
  omega

/-- Verity-side `sar` for an out-of-range shift. -/
private theorem int256_sar_val_of_shift_ge (shift value : Nat)
    (hv : value < Compiler.Constants.evmModulus) (hgeShift : 256 ≤ shift) :
    (if ({ word := { val := value, isLt := hv } } : Verity.Core.Int256).toInt < 0 then
      Verity.Core.Int256.ofInt (-1) else 0).word.val = SignedArithSpec.sarSpec shift value := by
  by_cases hval : value < SignedArithSpec.specSignBit
  · have hto : ¬ ({ word := { val := value, isLt := hv } } : Verity.Core.Int256).toInt < 0 := by
      rw [int256_toInt_of_lt_specSignBit value hv hval]
      exact not_lt.mpr (Int.natCast_nonneg _)
    rw [if_neg hto, SignedArithSpec.sarSpec_of_shift_ge_nonneg shift value hgeShift hval]
    change (Verity.Core.Uint256.ofNat 0).val = 0
    rfl
  · have hge : SignedArithSpec.specSignBit ≤ value := Nat.le_of_not_lt hval
    have hto : ({ word := { val := value, isLt := hv } } : Verity.Core.Int256).toInt < 0 := by
      rw [int256_toInt_of_specSignBit_le value hv hge]
      have : Int.ofNat value < Int.ofNat Compiler.Constants.evmModulus := Int.ofNat_lt.mpr hv
      omega
    rw [if_pos hto, SignedArithSpec.sarSpec_of_shift_ge_neg shift value hgeShift hge]
    have hnegOne := int256_ofInt_negSucc_toUint256_val 0 (by
      unfold Compiler.Constants.evmModulus
      omega)
    simpa [Int.negSucc_eq, Verity.Core.Int256.toUint256,
      SignedArithSpec.specModulus] using hnegOne

private theorem int256_sar_toUint256_val_eq_sarSpec (shift value : Nat)
    (hs : shift < Compiler.Constants.evmModulus) (hv : value < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.sar
      (Verity.Core.Int256.ofUint256 ⟨shift, hs⟩)
      (Verity.Core.Int256.ofUint256 ⟨value, hv⟩)).toUint256.val =
      SignedArithSpec.sarSpec shift value := by
  simp [Verity.Core.Int256.sar, Verity.Core.Int256.ofUint256,
    Verity.Core.Int256.toUint256]
  have hsMod : shift % Verity.Core.Int256.modulus = shift := by
    rw [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
      Verity.Core.UINT256_MODULUS]
    exact Nat.mod_eq_of_lt hs
  rw [hsMod]
  by_cases hshift : shift < 256
  · rw [if_neg (Nat.not_le_of_lt hshift)]
    by_cases hval : value < SignedArithSpec.specSignBit
    · exact int256_sar_val_of_lt_of_nonneg shift value hv hshift hval
    · exact int256_sar_val_of_lt_of_neg shift value hv hshift (Nat.le_of_not_lt hval)
  · rw [if_pos (Nat.not_lt.mp hshift)]
    exact int256_sar_val_of_shift_ge shift value hv (Nat.not_lt.mp hshift)

/-- Core sar equivalence: Verity's `Int256.sar` agrees with EVMYulLean's `UInt256.sar`.

Both sides reduce through `SignedArithSpec.sarSpec`: the EVMYulLean side
uses complement-shift-complement for negative words, while the Verity side
uses `Int.fdiv`; the helpers above identify the negative `fdiv` branch with
the same two's-complement raw-word result. -/
theorem int256_sar_toUint256_val_eq_uint256_sar (shift value : Nat)
    (hs : shift < Compiler.Constants.evmModulus) (hv : value < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.sar
      (Verity.Core.Int256.ofUint256 ⟨shift, hs⟩)
      (Verity.Core.Int256.ofUint256 ⟨value, hv⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.sar ⟨⟨shift, by rw [EvmYul.UInt256.size]; exact hs⟩⟩
                                               ⟨⟨value, by rw [EvmYul.UInt256.size]; exact hv⟩⟩) := by
  rw [uint256_sar_toNat_eq_sarSpec]
  exact int256_sar_toUint256_val_eq_sarSpec shift value hs hv
private theorem se_uint256_eq_of_val (a b : EvmYul.UInt256) (h : a.val.val = b.val.val) :
    a = b := EvmYul.UInt256.ext_val (Fin.ext h)

private theorem se_lor_val (a b : EvmYul.UInt256) :
    (EvmYul.UInt256.lor a b).val.val = (a.val.val ||| b.val.val) % EvmYul.UInt256.size := by
  unfold EvmYul.UInt256.lor; simp only [Fin.lor]; rfl

private theorem se_land_val (a b : EvmYul.UInt256) :
    (EvmYul.UInt256.land a b).val.val = (a.val.val &&& b.val.val) % EvmYul.UInt256.size := by
  unfold EvmYul.UInt256.land; simp only [Fin.land]; rfl

private theorem se_sub_val (a b : EvmYul.UInt256) :
    (EvmYul.UInt256.sub a b).val.val =
      (EvmYul.UInt256.size - b.val.val + a.val.val) % EvmYul.UInt256.size := by
  unfold EvmYul.UInt256.sub; simp only [Fin.sub_def]

private theorem se_tb_pow_sub_pow {n k : Nat} (hkn : k ≤ n) (i : Nat) :
    (2^n - 2^k).testBit i = (decide (k ≤ i) && decide (i < n)) := by
  have := Nat.one_le_pow k 2 (by omega)
  have := Nat.pow_le_pow_right (show 0 < 2 from by omega) hkn
  rw [show 2^k = (2^k - 1) + 1 from by omega,
      Nat.testBit_two_pow_sub_succ (by omega),
      Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < k <;> by_cases h2 : i < n <;> simp_all

private theorem se_tb_ne_zero {v k : Nat} (h : v &&& 2^k ≠ 0) : v.testBit k = true := by
  by_contra hf; simp only [Bool.not_eq_true] at hf
  apply h; apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hik : k = i
  · subst hik; simp [hf]
  · simp [hik]

private theorem se_tb_eq_zero {v k : Nat} (h : v &&& 2^k = 0) : v.testBit k = false := by
  by_contra hf; simp only [Bool.not_eq_false] at hf
  have : (v &&& 2^k).testBit k = true := by simp [Nat.testBit_and, hf]
  rw [h] at this; simp at this

private theorem se_set_eq {v n k : Nat} (hk1n : k + 1 ≤ n) (hsign : v &&& 2^k ≠ 0) :
    v ||| (2^n - 2^(k+1)) = v ||| (2^n - 2^k) := by
  have hbit := se_tb_ne_zero hsign
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, se_tb_pow_sub_pow (by omega : k + 1 ≤ n),
             se_tb_pow_sub_pow (by omega : k ≤ n)]
  by_cases hik : i = k
  · subst hik; simp [hbit]
  · congr 1
    by_cases hi : i < k
    · simp [show ¬(k ≤ i) from by omega, show ¬(k+1 ≤ i) from by omega]
    · simp [show k ≤ i from by omega, show k+1 ≤ i from by omega]

private theorem se_clear_eq {v k : Nat} (hsign : v &&& 2^k = 0) :
    v &&& (2^(k+1) - 1) = v &&& (2^k - 1) := by
  have hbit := se_tb_eq_zero hsign
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hik : i = k
  · subst hik; simp [hbit, show i < i + 1 from by omega]
  · congr 1; congr 1
    by_cases hi : i < k
    · simp [hi, show i < k + 1 from by omega]
    · simp [show ¬(i < k) from hi, show ¬(i < k + 1) from by omega]

private theorem se_tb_val (byteIdx : Nat) (hb : byteIdx < EvmYul.UInt256.size)
    (hle : byteIdx ≤ 31) :
    ((⟨⟨byteIdx, hb⟩⟩ : EvmYul.UInt256) * ⟨8⟩ + ⟨7⟩).val.val =
    byteIdx * 8 + 7 := by
  show ((EvmYul.UInt256.add (EvmYul.UInt256.mul ⟨⟨byteIdx, hb⟩⟩ ⟨8⟩) ⟨7⟩)).val.val = _
  unfold EvmYul.UInt256.add EvmYul.UInt256.mul
  simp only [Fin.mul_def, Fin.add_def]
  have h8 : (8 : Fin EvmYul.UInt256.size).val = 8 := by simp [EvmYul.UInt256.size]
  have h7 : (7 : Fin EvmYul.UInt256.size).val = 7 := by simp [EvmYul.UInt256.size]
  rw [h8, h7, Nat.mod_eq_of_lt (by rw [EvmYul.UInt256.size]; omega),
      Nat.mod_eq_of_lt (by rw [EvmYul.UInt256.size]; omega)]

private theorem se_shiftLeft_one_val (bitPos : Nat) (hbp : bitPos ≤ 255) :
    (EvmYul.UInt256.shiftLeft ⟨⟨1, by rw [EvmYul.UInt256.size]; omega⟩⟩
      ⟨⟨bitPos, by rw [EvmYul.UInt256.size]; omega⟩⟩).val.val = 2^bitPos := by
  unfold EvmYul.UInt256.shiftLeft; split
  · rename_i h; exact absurd (show bitPos ≥ 256 from h) (by omega)
  · change (1 <<< bitPos) % EvmYul.UInt256.size = 2^bitPos
    simp only [Nat.shiftLeft_eq, Nat.one_mul]
    have : 2^bitPos < 2^256 := Nat.pow_lt_pow_right (by omega) (by omega)
    rw [EvmYul.UInt256.size]; exact Nat.mod_eq_of_lt this

private theorem se_val_val_of_eq (a b : EvmYul.UInt256) (h : a = b) :
    a.val.val = b.val.val := by subst h; rfl

private theorem se_sign_set (value : Nat) (hvS : value < EvmYul.UInt256.size)
    (sb : EvmYul.UInt256) (bp : Nat) (hsb : sb.val.val = 2^bp)
    (h : EvmYul.UInt256.land ⟨⟨value, hvS⟩⟩ sb ≠
      ⟨⟨0, by rw [EvmYul.UInt256.size]; omega⟩⟩) :
    value &&& 2^bp ≠ 0 := by
  intro heq; apply h; apply se_uint256_eq_of_val
  rw [se_land_val, hsb, heq]; simp [EvmYul.UInt256.size]

private theorem se_sign_clear (value : Nat) (hvS : value < EvmYul.UInt256.size)
    (sb : EvmYul.UInt256) (bp : Nat) (hsb : sb.val.val = 2^bp)
    (h : ¬(EvmYul.UInt256.land ⟨⟨value, hvS⟩⟩ sb ≠
      ⟨⟨0, by rw [EvmYul.UInt256.size]; omega⟩⟩)) :
    value &&& 2^bp = 0 := by
  push Not at h
  have h1 := se_val_val_of_eq _ _ h
  rw [se_land_val, hsb] at h1
  rwa [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hvS)] at h1

private theorem se_nat_to_sign (value : Nat) (hvS : value < EvmYul.UInt256.size)
    (sb : EvmYul.UInt256) (bp : Nat) (hsb : sb.val.val = 2^bp)
    (h : value &&& 2^bp ≠ 0) :
    EvmYul.UInt256.land ⟨⟨value, hvS⟩⟩ sb ≠
      ⟨⟨0, by rw [EvmYul.UInt256.size]; omega⟩⟩ := by
  intro heq; apply h
  have h1 := se_val_val_of_eq _ _ heq
  rw [se_land_val, hsb] at h1
  rwa [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hvS)] at h1

private theorem se_verity_ofNat (n : Nat) :
    (Verity.Core.Uint256.ofNat n).val = n % Compiler.Constants.evmModulus := by
  unfold Verity.Core.Uint256.ofNat Verity.Core.Uint256.modulus
    Verity.Core.UINT256_MODULUS Compiler.Constants.evmModulus
  simp

private theorem se_size_to_uint256_val :
    (EvmYul.UInt256.size.toUInt256 : EvmYul.UInt256).val.val = 0 := by
  simp [Nat.toUInt256, EvmYul.UInt256.ofNat, Id.run, EvmYul.UInt256.size]

/-- The EVM `signextend` sign-bit word is `2 ^ (byteIdx * 8 + 7)`. -/
private theorem se_sign_bit_val (byteIdx : Nat) (hbS : byteIdx < EvmYul.UInt256.size)
    (hle : byteIdx ≤ 31) :
    ((⟨1⟩ : EvmYul.UInt256) <<< ((⟨⟨byteIdx, hbS⟩⟩ : EvmYul.UInt256) * ⟨8⟩ + ⟨7⟩)).val.val =
      2 ^ (byteIdx * 8 + 7) := by
  have htb_eq : ((⟨⟨byteIdx, hbS⟩⟩ : EvmYul.UInt256) * ⟨8⟩ + ⟨7⟩) =
      ⟨⟨byteIdx * 8 + 7, by rw [EvmYul.UInt256.size]; omega⟩⟩ :=
    se_uint256_eq_of_val _ _ (se_tb_val byteIdx hbS hle)
  rw [htb_eq]
  exact se_shiftLeft_one_val _ (by omega)

/-- EVM `signextend` branch value for a sign-bit word `sb = 2 ^ bp`. -/
private theorem se_evm_branch_val (value : Nat) (hvS : value < EvmYul.UInt256.size)
    (sb : EvmYul.UInt256) (bp : Nat) (hsb : sb.val.val = 2 ^ bp) (hbp : bp ≤ 255) :
    (if (⟨⟨value, hvS⟩⟩ : EvmYul.UInt256) &&& sb ≠ ⟨0⟩ then
        (⟨⟨value, hvS⟩⟩ : EvmYul.UInt256) ||| (EvmYul.UInt256.size.toUInt256 - sb)
      else (⟨⟨value, hvS⟩⟩ : EvmYul.UInt256) &&& (sb - ⟨1⟩)).val.val =
    if value &&& 2 ^ bp ≠ 0 then value ||| (2 ^ 256 - 2 ^ bp) else value &&& (2 ^ bp - 1) := by
  have hpow_pos := Nat.one_le_pow bp 2 (by omega)
  have hpow_lt := Nat.pow_lt_pow_right (show 1 < 2 from by omega) (show bp < 256 by omega)
  have hv256 : value < 2 ^ 256 := hvS
  split
  · rename_i hsign
    rw [if_pos (se_sign_set value hvS sb bp hsb hsign)]
    change (EvmYul.UInt256.lor _ (EvmYul.UInt256.sub _ sb)).val.val = _
    rw [se_lor_val, se_sub_val, se_size_to_uint256_val, hsb]
    simp only [show EvmYul.UInt256.size = 2 ^ 256 from rfl, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (show 2 ^ 256 - 2 ^ bp < 2 ^ 256 by omega)]
    exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow hv256 (by omega))
  · rename_i hsign
    rw [if_neg (not_not.mpr (se_sign_clear value hvS sb bp hsb hsign))]
    change (EvmYul.UInt256.land _
      (EvmYul.UInt256.sub sb ⟨⟨1, by rw [EvmYul.UInt256.size]; omega⟩⟩)).val.val = _
    rw [se_land_val, se_sub_val, hsb]
    simp only [show EvmYul.UInt256.size = 2 ^ 256 from rfl]
    rw [show (2:Nat) ^ 256 - 1 + 2 ^ bp = (2 ^ bp - 1) + 1 * 2 ^ 256 from by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (show 2 ^ bp - 1 < 2 ^ 256 by omega)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hv256)

/-- Setting an already-set bit is the identity. -/
private theorem se_or_two_pow_of_testBit {v k : Nat} (hbit : v.testBit k = true) :
    v ||| 2 ^ k = v := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hik : k = i
  · subst hik; simp [hbit]
  · simp [hik]

/-- Masking below bit 255 is the identity on a word whose bit 255 is clear. -/
private theorem se_and_mask_255_of_clear (value : Nat) (hv256 : value < 2 ^ 256)
    (hsign : value &&& 2 ^ 255 = 0) : value &&& (2 ^ 255 - 1) = value := by
  have htb_false := se_tb_eq_zero hsign
  have hv255 : value < 2 ^ 255 := by
    apply Nat.lt_of_testBit 255 htb_false
    · rw [Nat.testBit_two_pow]; simp
    · intro j hj
      have hvj : value < 2 ^ j :=
        lt_of_lt_of_le hv256 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_lt_two_pow hvj, Nat.testBit_two_pow_of_ne (by omega)]
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hv255]

/-- At `byteIdx = 31` the sign-bit form of `signextend` is the identity. -/
private theorem se_sign_form_255 (value : Nat) (hv256 : value < 2 ^ 256) :
    value = if value &&& 2 ^ 255 ≠ 0 then value ||| (2 ^ 256 - 2 ^ 255)
      else value &&& (2 ^ 255 - 1) := by
  by_cases hs : value &&& 2 ^ 255 ≠ 0
  · rw [if_pos hs, show (2:Nat) ^ 256 - 2 ^ 255 = 2 ^ 255 from by omega,
      se_or_two_pow_of_testBit (se_tb_ne_zero hs)]
  · rw [if_neg hs, se_and_mask_255_of_clear value hv256 (not_not.mp hs)]

/-- Verity `signextend` for `byteIdx ≤ 30`, in sign-bit form. -/
private theorem se_verity_branch_val_of_lt (bp value : Nat)
    (hv : value < Compiler.Constants.evmModulus) (hbp : bp ≤ 254) :
    (if value &&& 2 ^ bp ≠ 0 then
        Verity.Core.Uint256.ofNat (value ||| Verity.Core.Uint256.modulus - 1 - (2 ^ (bp + 1) - 1))
      else Verity.Core.Uint256.ofNat (value &&& 2 ^ (bp + 1) - 1)).val =
    if value &&& 2 ^ bp ≠ 0 then value ||| (2 ^ 256 - 2 ^ bp) else value &&& (2 ^ bp - 1) := by
  have hv256 : value < 2 ^ 256 := hv
  have := Nat.one_le_pow bp 2 (by omega)
  have := Nat.pow_lt_pow_right (show 1 < 2 from by omega) (show bp + 1 < 256 from by omega)
  have := Nat.pow_lt_pow_right (show 1 < 2 from by omega) (show bp < bp + 1 from by omega)
  by_cases hs : value &&& 2 ^ bp ≠ 0
  · rw [if_pos hs, if_pos hs, se_verity_ofNat]
    unfold Verity.Core.Uint256.modulus Verity.Core.UINT256_MODULUS
    rw [show 2 ^ 256 - 1 - (2 ^ (bp + 1) - 1) = 2 ^ 256 - 2 ^ (bp + 1) from by omega,
      se_set_eq (by omega) hs]
    exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow hv256 (by omega))
  · rw [if_neg hs, if_neg hs, se_verity_ofNat, se_clear_eq (not_not.mp hs)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hv)

/-- Verity `signextend` for `byteIdx ≤ 31`, in sign-bit form. -/
private theorem se_verity_branch_val (byteIdx value : Nat)
    (hv : value < Compiler.Constants.evmModulus) (hle31 : byteIdx ≤ 31) :
    (if byteIdx ≥ 31 then (⟨value, hv⟩ : Verity.Core.Uint256)
      else if value &&& 2 ^ (byteIdx * 8 + 7) ≠ 0 then
        Verity.Core.Uint256.ofNat
          (value ||| Verity.Core.Uint256.modulus - 1 - (2 ^ (byteIdx * 8 + 7 + 1) - 1))
      else Verity.Core.Uint256.ofNat (value &&& 2 ^ (byteIdx * 8 + 7 + 1) - 1)).val =
    if value &&& 2 ^ (byteIdx * 8 + 7) ≠ 0 then value ||| (2 ^ 256 - 2 ^ (byteIdx * 8 + 7))
    else value &&& (2 ^ (byteIdx * 8 + 7) - 1) := by
  by_cases hge31 : byteIdx ≥ 31
  · have hb31 : byteIdx = 31 := by omega
    subst hb31
    rw [if_pos hge31]
    exact se_sign_form_255 value hv
  · rw [if_neg hge31]
    exact se_verity_branch_val_of_lt _ value hv (by omega)

/-- Core signextend equivalence: Verity's `Uint256.signextend` agrees with
EVMYulLean's `UInt256.signextend`.

Both implement EVM SIGNEXTEND using the same bit-level algorithm:
1. Compute sign bit position = byteIdx * 8 + 7
2. Test the sign bit
3. If set: fill high bits (OR with complement mask)
4. If clear: clear high bits (AND with mask)
5. If byteIdx ≥ 31: return value unchanged -/
theorem uint256_signextend_val_eq_uint256_signextend (byteIdx value : Nat)
    (hb : byteIdx < Compiler.Constants.evmModulus) (hv : value < Compiler.Constants.evmModulus) :
    (Verity.Core.Uint256.signextend ⟨byteIdx, hb⟩ ⟨value, hv⟩).val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.signextend
      ⟨⟨byteIdx, by rw [EvmYul.UInt256.size]; exact hb⟩⟩
      ⟨⟨value, by rw [EvmYul.UInt256.size]; exact hv⟩⟩) := by
  have hvS : value < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hv
  have hbS : byteIdx < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hb
  unfold Verity.Core.Uint256.signextend EvmYul.UInt256.signextend
  simp only [EvmYul.UInt256.toNat]
  by_cases hle31 : byteIdx ≤ 31
  · simp only [hle31, ite_true]
    have hsb := se_sign_bit_val byteIdx hbS hle31
    generalize ((⟨1⟩ : EvmYul.UInt256) <<< ((⟨⟨byteIdx, hbS⟩⟩ : EvmYul.UInt256) * ⟨8⟩ + ⟨7⟩))
      = sb at hsb ⊢
    rw [se_evm_branch_val value hvS sb _ hsb (by omega)]
    exact se_verity_branch_val byteIdx value hv hle31
  · simp only [show ¬(byteIdx ≤ 31) from hle31, ite_false]
    simp only [show byteIdx ≥ 31 from by omega, ite_true]
end Compiler.Proofs.YulGeneration.Backends
