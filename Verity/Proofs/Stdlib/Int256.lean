/-
  Two's-complement wrapping of `Int256` agrees with unbounded `Int`
  arithmetic exactly on the Solidity 0.8 success side.
-/

import Verity.Core
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace Verity.Proofs.Stdlib.Int256

open Verity.Core
open Int256

private lemma modulus_def : modulus = UINT256_MODULUS := rfl

private lemma natCast_emod_of_lt {n m : Nat} (h : n < m) :
    (n : Int) % (m : Int) = n :=
  Int.emod_eq_of_lt (Int.natCast_nonneg n) (Nat.cast_lt.mpr h)

private lemma max_sub_min : maxValue - minValue = ((modulus - 1 : Nat) : Int) := by
  have hs : 1 ≤ signBit := Nat.succ_le_of_lt signBit_pos
  have hm : modulus = 2 * signBit := modulus_eq_two_mul_signBit
  have hsb : (signBit : Int) - (1 : Int) = ((signBit - 1 : Nat) : Int) :=
    (Int.natCast_sub hs).symm
  have hsum : ((signBit - 1 : Nat) : Int) + (signBit : Int) =
      ((signBit - 1 + signBit : Nat) : Int) := Int.natCast_add _ _
  have hnat : signBit - 1 + signBit = 2 * signBit - 1 := by omega
  calc
    maxValue - minValue
        = ((signBit : Int) - 1) + (signBit : Int) := by
          simp [maxValue, minValue]
    _ = ((signBit - 1 : Nat) : Int) + (signBit : Int) := by rw [hsb]
    _ = ((2 * signBit - 1 : Nat) : Int) := by rw [hsum, hnat]
    _ = ((modulus - 1 : Nat) : Int) := by simp [hm]

private lemma maxValue_nat :
    maxValue = ((signBit - 1 : Nat) : Int) := by
  have hs : 1 ≤ signBit := Nat.succ_le_of_lt signBit_pos
  simp only [maxValue]
  exact (Int.natCast_sub hs).symm

private lemma natAbs_natCast (n : Nat) : (n : Int).natAbs = n :=
  Int.natAbs_natCast n

/-- Two's-complement word of `v` is `v` modulo `2^256`. -/
theorem toInt_emod (v : Int256) :
    (v : Int) % (modulus : Int) = (v.word.val : Int) := by
  have hw := natCast_emod_of_lt (m := modulus) v.word.isLt
  by_cases hs : v.word.val < signBit
  · have hv := toInt_of_lt_signBit (value := v) hs
    simpa [hv, modulus_def] using hw
  · have hge : signBit ≤ v.word.val := Nat.le_of_not_lt hs
    have hv := toInt_of_ge_signBit (value := v) hge
    have hself : (modulus : Int) % (modulus : Int) = 0 := Int.emod_self
    have hsub :
        ((v.word.val : Int) - (modulus : Int)) % (modulus : Int) =
          (v.word.val : Int) % (modulus : Int) := by
      rw [Int.sub_emod, hself]
      simp
    have hv' : (v : Int) = (v.word.val : Int) - (modulus : Int) := by
      simpa using hv
    rw [hv', hsub]
    simpa [modulus_def] using hw

private lemma emod_neg_congr {x y m : Int} (h : x % m = y % m) :
    (-x) % m = (-y) % m := by
  have h0 : (x - y) % m = 0 := (Int.emod_eq_emod_iff_emod_sub_eq_zero).1 h
  have hdvd : m ∣ (x - y) := (Int.dvd_iff_emod_eq_zero).2 h0
  have hneg : m ∣ (-x - (-y)) := by
    have : -x - (-y) = -(x - y) := by ring
    rw [this]
    exact (Int.dvd_neg).mpr hdvd
  exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
    ((Int.dvd_iff_emod_eq_zero).1 hneg)

/-- In-range integers that agree modulo `2^256` are equal. -/
theorem inRange_eq_of_emod_eq {x y : Int}
    (hx : inRange x) (hy : inRange y)
    (hcong : x % (modulus : Int) = y % (modulus : Int)) : x = y := by
  have hspan := max_sub_min
  have hx1 := hx.1; have hx2 := hx.2; have hy1 := hy.1; have hy2 := hy.2
  have hle : x - y ≤ ((modulus - 1 : Nat) : Int) := by linarith
  have hge : -((modulus - 1 : Nat) : Int) ≤ x - y := by linarith
  have habsInt : |x - y| ≤ ((modulus - 1 : Nat) : Int) := abs_le.2 ⟨hge, hle⟩
  have habs : Int.natAbs (x - y) ≤ modulus - 1 := by
    have : (Int.natAbs (x - y) : Int) ≤ ((modulus - 1 : Nat) : Int) := by
      rwa [← Int.abs_eq_natAbs]
    exact Nat.cast_le.mp this
  have hltAbs : Int.natAbs (x - y) < modulus := by
    have : 1 ≤ modulus := Nat.succ_le_of_lt modulus_pos
    omega
  have hdiv : (x - y) % (modulus : Int) = 0 := by
    rw [Int.sub_emod, hcong, sub_self, Int.zero_emod]
  have hdvd : (modulus : Int) ∣ (x - y) := (Int.dvd_iff_emod_eq_zero).2 hdiv
  have hz : x - y = 0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by
      simpa [natAbs_natCast] using hltAbs)
  linarith

theorem toInt_add_of_inRange (a b : Int256)
    (h : inRange ((a : Int) + (b : Int))) :
    ((a.add b) : Int) = (a : Int) + (b : Int) := by
  apply inRange_eq_of_emod_eq (inRange_toInt _) h
  have ha := toInt_emod a
  have hb := toInt_emod b
  have hr := toInt_emod (a.add b)
  have hw := add_word a b
  have hsum :
      (((a.word.val + b.word.val) % modulus : Nat) : Int) =
        ((a.word.val : Int) + (b.word.val : Int)) % (modulus : Int) := by
    rw [Int.natCast_emod, Int.natCast_add]
  calc
    ((a.add b) : Int) % (modulus : Int)
        = ((a.add b).word.val : Int) := hr
    _ = (((a.word.val + b.word.val) % modulus : Nat) : Int) := by rw [hw]
    _ = ((a.word.val : Int) + (b.word.val : Int)) % (modulus : Int) := hsum
    _ = ((a : Int) % (modulus : Int) + (b : Int) % (modulus : Int)) %
          (modulus : Int) := by rw [← ha, ← hb]
    _ = ((a : Int) + (b : Int)) % (modulus : Int) := (Int.add_emod _ _ _).symm

theorem toInt_mul_of_inRange (a b : Int256)
    (h : inRange ((a : Int) * (b : Int))) :
    ((a.mul b) : Int) = (a : Int) * (b : Int) := by
  apply inRange_eq_of_emod_eq (inRange_toInt _) h
  have ha := toInt_emod a
  have hb := toInt_emod b
  have hr := toInt_emod (a.mul b)
  have hw := mul_word a b
  have hprod :
      (((a.word.val * b.word.val) % modulus : Nat) : Int) =
        ((a.word.val : Int) * (b.word.val : Int)) % (modulus : Int) := by
    rw [Int.natCast_emod, Int.natCast_mul]
  calc
    ((a.mul b) : Int) % (modulus : Int)
        = ((a.mul b).word.val : Int) := hr
    _ = (((a.word.val * b.word.val) % modulus : Nat) : Int) := by rw [hw]
    _ = ((a.word.val : Int) * (b.word.val : Int)) % (modulus : Int) := hprod
    _ = ((a : Int) % (modulus : Int) * ((b : Int) % (modulus : Int))) %
          (modulus : Int) := by rw [← ha, ← hb]
    _ = ((a : Int) * (b : Int)) % (modulus : Int) := (Int.mul_emod _ _ _).symm

private lemma sub_word (a b : Int256) :
    (a.sub b).word.val =
      if b.word.val ≤ a.word.val then
        (a.word.val - b.word.val) % modulus
      else
        (modulus - (b.word.val - a.word.val)) % modulus := by
  simp only [Int256.sub, ofUint256]
  change (Uint256.sub a.word b.word).val = _
  unfold Uint256.sub
  split_ifs <;> simp [Uint256.val_ofNat, modulus]

private lemma sub_word_emod (a b : Int256) :
    ((a.sub b).word.val : Int) % (modulus : Int) =
      ((a.word.val : Int) - (b.word.val : Int)) % (modulus : Int) := by
  have hwa : a.word.val < modulus := a.word.isLt
  have hwb : b.word.val < modulus := b.word.isLt
  have hw := sub_word a b
  split_ifs at hw with hle
  · have hlt : a.word.val - b.word.val < modulus :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) hwa
    have hmod : (a.word.val - b.word.val) % modulus = a.word.val - b.word.val :=
      Nat.mod_eq_of_lt hlt
    rw [hw, hmod, Int.natCast_sub hle]
  · have hgt : a.word.val < b.word.val := Nat.not_le.mp hle
    have hpos : 0 < b.word.val - a.word.val := Nat.sub_pos_of_lt hgt
    have hltm : modulus - (b.word.val - a.word.val) < modulus :=
      Nat.sub_lt modulus_pos hpos
    have hmod : (modulus - (b.word.val - a.word.val)) % modulus =
        modulus - (b.word.val - a.word.val) := Nat.mod_eq_of_lt hltm
    have hle_m : b.word.val - a.word.val ≤ modulus :=
      Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hwb)
    rw [hw, hmod, Int.natCast_sub hle_m, Int.natCast_sub (Nat.le_of_lt hgt)]
    have hrew :
        (modulus : Int) - ((b.word.val : Int) - (a.word.val : Int)) =
          (a.word.val : Int) - (b.word.val : Int) + (modulus : Int) := by
      ring
    rw [hrew, Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]

theorem toInt_sub_of_inRange (a b : Int256)
    (h : inRange ((a : Int) - (b : Int))) :
    ((a.sub b) : Int) = (a : Int) - (b : Int) := by
  apply inRange_eq_of_emod_eq (inRange_toInt _) h
  have ha := toInt_emod a
  have hb := toInt_emod b
  have hr := toInt_emod (a.sub b)
  have hw := sub_word_emod a b
  calc
    ((a.sub b) : Int) % (modulus : Int)
        = ((a.sub b).word.val : Int) := hr
    _ = ((a.sub b).word.val : Int) % (modulus : Int) :=
          (natCast_emod_of_lt (a.sub b).word.isLt).symm
    _ = ((a.word.val : Int) - (b.word.val : Int)) % (modulus : Int) := hw
    _ = ((a : Int) % (modulus : Int) - (b : Int) % (modulus : Int)) %
          (modulus : Int) := by rw [← ha, ← hb]
    _ = ((a : Int) - (b : Int)) % (modulus : Int) := (Int.sub_emod _ _ _).symm

private lemma neg_word (value : Int256) :
    (neg value).word.val = (modulus - value.word.val) % modulus := by
  simp [neg, ofUint256, Uint256.val_ofNat, modulus]

private lemma neg_maxValue : -maxValue = minValue + 1 := by
  simp only [maxValue, minValue]
  ring

private lemma neg_minValue : -minValue = maxValue + 1 := by
  simp only [maxValue, minValue]
  ring

theorem toInt_neg_of_not_min (value : Int256) (h : (value : Int) ≠ minValue) :
    ((neg value) : Int) = -(value : Int) := by
  have hv := toInt_in_range value
  have hlt : minValue < (value : Int) := lt_of_le_of_ne hv.1 h.symm
  have hRange : inRange (-(value : Int)) := by
    refine ⟨?_, ?_⟩
    · have : -(value : Int) ≥ -maxValue := neg_le_neg hv.2
      linarith [neg_maxValue]
    · have h1 : minValue + 1 ≤ (value : Int) := (Int.add_one_le_iff).2 hlt
      have : -(value : Int) ≤ -(minValue + 1) := neg_le_neg h1
      linarith [neg_minValue]
  apply inRange_eq_of_emod_eq (inRange_toInt _) hRange
  have hr := toInt_emod (neg value)
  have hv' := toInt_emod value
  have hwa : value.word.val < modulus := value.word.isLt
  have hword := neg_word value
  have hself : (modulus : Int) % (modulus : Int) = 0 := Int.emod_self
  calc
    ((neg value) : Int) % (modulus : Int)
        = ((neg value).word.val : Int) := hr
    _ = (((modulus - value.word.val) % modulus : Nat) : Int) := by rw [hword]
    _ = ((modulus - value.word.val : Nat) : Int) % (modulus : Int) :=
          (Int.natCast_emod _ _).symm
    _ = ((modulus : Int) - (value.word.val : Int)) % (modulus : Int) := by
          rw [Int.natCast_sub (Nat.le_of_lt hwa)]
    _ = (-(value.word.val : Int)) % (modulus : Int) := by
          have hwmod : ((value.word.val : Int) % (modulus : Int)) =
              (value.word.val : Int) := natCast_emod_of_lt hwa
          rw [Int.sub_emod, hself, zero_sub]
          rw [hwmod]
    _ = (-(value : Int)) % (modulus : Int) := by
          have hcong :
              ((value.word.val : Int) % (modulus : Int)) =
                ((value : Int) % (modulus : Int)) := by
            rw [natCast_emod_of_lt hwa, hv']
          exact emod_neg_congr hcong

private lemma toNat_lt_signBit_of_nonneg {z : Int}
    (_hz : 0 ≤ z) (h : z ≤ maxValue) : z.toNat < signBit := by
  have hs : 1 ≤ signBit := Nat.succ_le_of_lt signBit_pos
  have hle' : z.toNat ≤ maxValue.toNat := Int.toNat_le_toNat h
  have hmaxN : maxValue.toNat = signBit - 1 := by
    rw [maxValue_nat, Int.toNat_natCast]
  omega

private lemma natAbs_le_signBit_of_inRange {z : Int} (h : inRange z) :
    z.natAbs ≤ signBit := by
  by_cases hz : 0 ≤ z
  · have hlt := toNat_lt_signBit_of_nonneg hz h.2
    have hAbs : z.natAbs = z.toNat := by
      have h1 : (z.natAbs : Int) = z := Int.natAbs_of_nonneg hz
      have h2 : (z.toNat : Int) = z := Int.toNat_of_nonneg hz
      exact Int.natCast_inj.mp (h1.trans h2.symm)
    omega
  · have hAbs : (z.natAbs : Int) = -z := by
      have : 0 ≤ -z := by linarith
      have h1 : ((-z).natAbs : Int) = -z := Int.natAbs_of_nonneg this
      simpa [Int.natAbs_neg] using h1
    have : (z.natAbs : Int) ≤ (signBit : Int) := by
      have hle : -z ≤ -minValue := neg_le_neg h.1
      have hle' : -z ≤ (signBit : Int) := by
        simpa [minValue] using hle
      rw [hAbs]
      exact hle'
    exact Nat.cast_le.mp this

private lemma inRange_of_natAbs_lt_signBit {z : Int} (h : z.natAbs < signBit) :
    inRange z := by
  have hle : z.natAbs ≤ signBit - 1 := Nat.le_pred_of_lt h
  have hcast : (z.natAbs : Int) ≤ ((signBit - 1 : Nat) : Int) :=
    Nat.cast_le.mpr hle
  have habs : |z| ≤ maxValue := by
    rw [Int.abs_eq_natAbs, maxValue_nat]
    exact hcast
  have h1 := abs_le.1 habs
  refine ⟨?_, h1.2⟩
  linarith [neg_maxValue, h1.1]

/-- `ofInt` is the identity on the `int256` range. -/
theorem toInt_ofInt {z : Int} (h : inRange z) : (ofInt z : Int) = z := by
  by_cases hz : z < 0
  · have habs_le : z.natAbs ≤ signBit := natAbs_le_signBit_of_inRange h
    have habs_lt : z.natAbs < modulus :=
      Nat.lt_of_le_of_lt habs_le signBit_lt_modulus
    have hmod : z.natAbs % modulus = z.natAbs := Nat.mod_eq_of_lt habs_lt
    have hword :
        (ofInt z).word.val = (modulus - z.natAbs) % modulus := by
      have hw := ofInt_neg z hz
      have hval : (ofInt z).word.val =
          (modulus - (z.natAbs % modulus)) % modulus := by
        change (ofInt z).toUint256.val = _
        rw [hw, Uint256.val_ofNat, modulus]
      rw [hval, hmod]
    have hpos : 0 < z.natAbs := Int.natAbs_pos.mpr (ne_of_lt hz)
    have hdiff : modulus - z.natAbs < modulus := Nat.sub_lt modulus_pos hpos
    have hmod' : (modulus - z.natAbs) % modulus = modulus - z.natAbs :=
      Nat.mod_eq_of_lt hdiff
    have hge : signBit ≤ (ofInt z).word.val := by
      rw [hword, hmod']
      have htwo : modulus - signBit = signBit := by
        have := modulus_eq_two_mul_signBit
        omega
      omega
    have hv := toInt_of_ge_signBit (value := ofInt z) hge
    have hle_m : z.natAbs ≤ modulus := Nat.le_of_lt habs_lt
    have hcast :
        ((ofInt z).word.val : Int) = (modulus : Int) - (z.natAbs : Int) := by
      rw [hword, hmod', Int.natCast_sub hle_m]
    have hzneg : z = - (z.natAbs : Int) := by
      have : 0 ≤ -z := by linarith
      have h1 : ((-z).natAbs : Int) = -z := Int.natAbs_of_nonneg this
      have : (z.natAbs : Int) = -z := by simpa [Int.natAbs_neg] using h1
      linarith
    calc
      (ofInt z : Int)
          = ((ofInt z).word.val : Int) - (modulus : Int) := by simpa using hv
      _ = (modulus : Int) - (z.natAbs : Int) - (modulus : Int) := by rw [hcast]
      _ = z := by linarith
  · have hnn : 0 ≤ z := le_of_not_gt hz
    have hlt := toNat_lt_signBit_of_nonneg hnn h.2
    have hword : (ofInt z).word.val = z.toNat % modulus := by
      have hw := ofInt_nonneg z hz
      change (ofInt z).toUint256.val = _
      rw [hw, Uint256.val_ofNat, modulus]
    have hto : z.toNat < modulus := Nat.lt_trans hlt signBit_lt_modulus
    have hmod : z.toNat % modulus = z.toNat := Nat.mod_eq_of_lt hto
    have hsb : (ofInt z).word.val < signBit := by
      rw [hword, hmod]
      exact hlt
    have hv := toInt_of_lt_signBit (value := ofInt z) hsb
    have hz' : (z.toNat : Int) = z := Int.toNat_of_nonneg hnn
    calc
      (ofInt z : Int)
          = Int.ofNat (ofInt z).word.val := hv
      _ = (z.toNat : Int) := by
            rw [hword, hmod]
            rfl
      _ = z := hz'

private lemma decide_natCast_lt_zero (n : Nat) :
    decide ((n : Int) < 0) = false :=
  decide_eq_false (not_lt.mpr (Int.natCast_nonneg n))

private lemma tdiv_eq_sign_natAbs (x y : Int) (_hy : y ≠ 0) :
    Int.tdiv x y =
      if decide (x < 0) == decide (y < 0) then
        Int.ofNat (x.natAbs / y.natAbs)
      else
        -Int.ofNat (x.natAbs / y.natAbs) := by
  cases x with
  | ofNat n =>
    cases y with
    | ofNat m =>
      simp [Int.tdiv, Int.natAbs_natCast, decide_natCast_lt_zero]
    | negSucc m =>
      simp [Int.tdiv, Int.natAbs, decide_natCast_lt_zero]
  | negSucc n =>
    cases y with
    | ofNat m =>
      simp [Int.tdiv, Int.natAbs, decide_natCast_lt_zero]
    | negSucc m =>
      simp [Int.tdiv, Int.natAbs]

private lemma tmod_eq_sign_natAbs (x y : Int) (hy : y ≠ 0) :
    Int.tmod x y =
      if x < 0 then
        -Int.ofNat (x.natAbs % y.natAbs)
      else
        Int.ofNat (x.natAbs % y.natAbs) := by
  cases x with
  | ofNat n =>
    have hn : ¬ Int.ofNat n < 0 := by simp
    rw [if_neg hn]
    cases y with
    | ofNat m =>
      simp [Int.tmod, Int.natAbs_natCast]
    | negSucc m =>
      simp [Int.tmod, Int.natAbs]
  | negSucc n =>
    have hn : Int.negSucc n < 0 := by simp
    rw [if_pos hn]
    cases y with
    | ofNat m =>
      simp [Int.tmod, Int.natAbs]
    | negSucc m =>
      simp [Int.tmod, Int.natAbs]

theorem div_eq_ofInt_tdiv (a b : Int256) (hb : (b : Int) ≠ 0) :
    a.div b = ofInt (Int.tdiv (a : Int) (b : Int)) := by
  unfold Int256.div
  have hne : ¬ ((b : Int) = 0) := hb
  simp only [hne, ↓reduceIte, signedAbsNat]
  rw [tdiv_eq_sign_natAbs (a : Int) (b : Int) hb]
  split_ifs <;> rfl

private lemma tdiv_inRange_of_not_divFails (a b : Int256) (h : ¬ divFails a b) :
    inRange (Int.tdiv (a : Int) (b : Int)) := by
  have hb : (b : Int) ≠ 0 := fun hz => h (Or.inl hz)
  have ha_le : (a : Int).natAbs ≤ signBit :=
    natAbs_le_signBit_of_inRange (inRange_toInt a)
  have hquot : (Int.tdiv (a : Int) (b : Int)).natAbs ≤ signBit := by
    rw [Int.natAbs_tdiv]
    exact Nat.le_trans (Nat.div_le_self _ _) ha_le
  by_cases hlt : (Int.tdiv (a : Int) (b : Int)).natAbs < signBit
  · exact inRange_of_natAbs_lt_signBit hlt
  · have heq : (Int.tdiv (a : Int) (b : Int)).natAbs = signBit := by omega
    have hdiv : (a : Int).natAbs / (b : Int).natAbs = signBit := by
      have h := heq
      rw [Int.natAbs_tdiv] at h
      exact h
    have hmul : signBit * (b : Int).natAbs ≤ (a : Int).natAbs := by
      rw [← hdiv]
      exact Nat.div_mul_le_self _ _
    have hb1 : (b : Int).natAbs = 1 := by
      have : signBit * (b : Int).natAbs ≤ signBit * 1 := by
        simpa using (le_trans hmul ha_le)
      have : (b : Int).natAbs ≤ 1 :=
        Nat.le_of_mul_le_mul_left this signBit_pos
      have hbpos : 0 < (b : Int).natAbs := Int.natAbs_pos.mpr hb
      omega
    have ha_eq : (a : Int).natAbs = signBit := by
      have : signBit ≤ (a : Int).natAbs := by simpa [hb1] using hmul
      omega
    have ha_min : (a : Int) = minValue := by
      have hx := (Int.natAbs_eq_iff (a := (a : Int)) (n := signBit)).1 ha_eq
      cases hx with
      | inl hpos =>
          have hle := (inRange_toInt a).2
          have hbad : (signBit : Int) ≤ maxValue := hpos ▸ hle
          simp only [maxValue] at hbad
          change (signBit : Int) ≤ (signBit : Int) - 1 at hbad
          omega
      | inr hneg =>
          simpa [minValue] using hneg
    have hb_pm : (b : Int) = 1 ∨ (b : Int) = -1 :=
      (Int.natAbs_eq_iff (a := (b : Int)) (n := 1)).1 hb1
    cases hb_pm with
    | inl hp =>
        have htd : Int.tdiv (a : Int) (b : Int) = minValue := by
          rw [ha_min, hp, Int.tdiv_one]
        rw [htd]
        refine ⟨le_rfl, ?_⟩
        have hz := toInt_in_range (0 : Int256)
        have h0 : ((0 : Int256) : Int) = 0 := val_zero
        rw [h0] at hz
        exact le_trans hz.1 hz.2
    | inr hn =>
        exact (h (Or.inr ⟨ha_min, hn⟩)).elim

theorem toInt_div_of_not_divFails (a b : Int256) (h : ¬ divFails a b) :
    ((a.div b) : Int) = Int.tdiv (a : Int) (b : Int) := by
  have hb : (b : Int) ≠ 0 := fun hz => h (Or.inl hz)
  rw [div_eq_ofInt_tdiv a b hb]
  exact toInt_ofInt (tdiv_inRange_of_not_divFails a b h)

theorem mod_eq_ofInt_tmod (a b : Int256) (hb : (b : Int) ≠ 0) :
    a.mod b = ofInt (Int.tmod (a : Int) (b : Int)) := by
  unfold Int256.mod
  have hne : ¬ ((b : Int) = 0) := hb
  simp only [hne, ↓reduceIte, signedAbsNat]
  rw [tmod_eq_sign_natAbs (a : Int) (b : Int) hb]
  split_ifs <;> rfl

private lemma tmod_inRange (a b : Int256) (hb : (b : Int) ≠ 0) :
    inRange (Int.tmod (a : Int) (b : Int)) := by
  have hAbs : (Int.tmod (a : Int) (b : Int)).natAbs =
      (a : Int).natAbs % (b : Int).natAbs := Int.natAbs_tmod _ _
  have hbpos : 0 < (b : Int).natAbs := Int.natAbs_pos.mpr hb
  have hlt : (Int.tmod (a : Int) (b : Int)).natAbs < (b : Int).natAbs := by
    rw [hAbs]
    exact Nat.mod_lt _ hbpos
  have hb_le : (b : Int).natAbs ≤ signBit :=
    natAbs_le_signBit_of_inRange (inRange_toInt b)
  exact inRange_of_natAbs_lt_signBit (Nat.lt_of_lt_of_le hlt hb_le)

theorem toInt_mod_of_ne_zero (a b : Int256) (hb : (b : Int) ≠ 0) :
    ((a.mod b) : Int) = Int.tmod (a : Int) (b : Int) := by
  rw [mod_eq_ofInt_tmod a b hb]
  exact toInt_ofInt (tmod_inRange a b hb)

theorem addPanic_success_toInt (a b : Int256)
    (h : minValue ≤ (a : Int) + (b : Int) ∧ (a : Int) + (b : Int) ≤ maxValue) :
    addPanic a b = some (a.add b) ∧ ((a.add b : Int) = (a : Int) + (b : Int)) :=
  ⟨addPanic_success a b h, toInt_add_of_inRange a b h⟩

theorem subPanic_success_toInt (a b : Int256)
    (h : minValue ≤ (a : Int) - (b : Int) ∧ (a : Int) - (b : Int) ≤ maxValue) :
    subPanic a b = some (a.sub b) ∧ ((a.sub b : Int) = (a : Int) - (b : Int)) :=
  ⟨subPanic_success a b h, toInt_sub_of_inRange a b h⟩

theorem mulPanic_success_toInt (a b : Int256)
    (h : minValue ≤ (a : Int) * (b : Int) ∧ (a : Int) * (b : Int) ≤ maxValue) :
    mulPanic a b = some (a.mul b) ∧ ((a.mul b : Int) = (a : Int) * (b : Int)) :=
  ⟨mulPanic_success a b h, toInt_mul_of_inRange a b h⟩

theorem negPanic_success_toInt (value : Int256) (h : (value : Int) ≠ minValue) :
    negPanic value = some (neg value) ∧ ((neg value : Int) = -(value : Int)) :=
  ⟨negPanic_success value h, toInt_neg_of_not_min value h⟩

theorem divPanic_success_toInt (a b : Int256) (h : ¬ divFails a b) :
    divPanic a b = some (a.div b) ∧
      ((a.div b : Int) = Int.tdiv (a : Int) (b : Int)) :=
  ⟨divPanic_success a b h, toInt_div_of_not_divFails a b h⟩

theorem modPanic_success_toInt (a b : Int256) (h : (b : Int) ≠ 0) :
    modPanic a b = some (a.mod b) ∧
      ((a.mod b : Int) = Int.tmod (a : Int) (b : Int)) :=
  ⟨modPanic_success a b h, toInt_mod_of_ne_zero a b h⟩

theorem addPanic_failure_iff (a b : Int256) :
    addPanic a b = none ↔ addOverflows a b := by
  constructor
  · intro hnone
    by_contra hov
    have hin : inRange ((a : Int) + (b : Int)) := by
      simpa [addOverflows] using hov
    have := addPanic_success a b hin
    simp [this] at hnone
  · intro hov
    exact addPanic_failure a b (by simpa [addOverflows, inRange] using hov)

theorem subPanic_failure_iff (a b : Int256) :
    subPanic a b = none ↔ subOverflows a b := by
  constructor
  · intro hnone
    by_contra hov
    have hin : inRange ((a : Int) - (b : Int)) := by
      simpa [subOverflows] using hov
    have := subPanic_success a b hin
    simp [this] at hnone
  · intro hov
    exact subPanic_failure a b (by simpa [subOverflows, inRange] using hov)

theorem mulPanic_failure_iff (a b : Int256) :
    mulPanic a b = none ↔ mulOverflows a b := by
  constructor
  · intro hnone
    by_contra hov
    have hin : inRange ((a : Int) * (b : Int)) := by
      simpa [mulOverflows] using hov
    have := mulPanic_success a b hin
    simp [this] at hnone
  · intro hov
    exact mulPanic_failure a b (by simpa [mulOverflows, inRange] using hov)

theorem negPanic_failure_iff (value : Int256) :
    negPanic value = none ↔ negOverflows value := by
  constructor
  · intro hnone
    by_contra hov
    have hne : (value : Int) ≠ minValue := by
      simpa [negOverflows] using hov
    have := negPanic_success value hne
    simp [this] at hnone
  · intro hov
    exact negPanic_failure value (by simpa [negOverflows] using hov)

theorem divPanic_failure_iff (a b : Int256) :
    divPanic a b = none ↔ divFails a b := by
  constructor
  · intro hnone
    by_contra hf
    have := divPanic_success a b hf
    simp [this] at hnone
  · exact divPanic_failure a b

theorem modPanic_failure_iff (a b : Int256) :
    modPanic a b = none ↔ (b : Int) = 0 := by
  constructor
  · intro hnone
    by_contra hb
    have := modPanic_success a b hb
    simp [this] at hnone
  · exact modPanic_failure a b

end Verity.Proofs.Stdlib.Int256
