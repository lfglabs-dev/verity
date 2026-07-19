/-
  Correctness proofs for all safe arithmetic operations in the Math stdlib.

  Covers safeAdd, safeSub, safeMul, and safeDiv: each operation returns
  the correct result when within bounds and returns none otherwise.
-/

import Verity.Core
import Verity.Stdlib.Math
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Verity.Proofs.Stdlib.Math

open Verity
open Verity.Stdlib.Math

namespace CheckedArithmetic

/-- Proof obligation for a checked `uint256` addition to avoid overflow. -/
def AddNoOverflow (a b : Uint256) : Prop :=
  (a : Nat) + (b : Nat) ≤ MAX_UINT256

/-- Proof obligation for a checked `uint256` subtraction to avoid underflow. -/
def SubNoUnderflow (a b : Uint256) : Prop :=
  (b : Nat) ≤ (a : Nat)

/-- Proof obligation for a checked `uint256` multiplication to avoid overflow. -/
def MulNoOverflow (a b : Uint256) : Prop :=
  (a : Nat) * (b : Nat) ≤ MAX_UINT256

theorem safeAdd_isSome_iff_addNoOverflow (a b : Uint256) :
    (safeAdd a b).isSome ↔ AddNoOverflow a b := by
  unfold AddNoOverflow safeAdd
  by_cases h : (a : Nat) + (b : Nat) > MAX_UINT256
  · simp [h]
  · simp [h]
    omega

theorem safeSub_isSome_iff_subNoUnderflow (a b : Uint256) :
    (safeSub a b).isSome ↔ SubNoUnderflow a b := by
  unfold SubNoUnderflow safeSub
  by_cases h : (b : Nat) > (a : Nat)
  · simp [h]
  · simp [h]
    omega

theorem safeMul_isSome_iff_mulNoOverflow (a b : Uint256) :
    (safeMul a b).isSome ↔ MulNoOverflow a b := by
  unfold MulNoOverflow safeMul
  by_cases h : (a : Nat) * (b : Nat) > MAX_UINT256
  · simp [h]
  · simp [h]
    omega

end CheckedArithmetic

/-! ## BN254 Field Helpers -/

theorem SNARK_SCALAR_FIELD_ne_zero : SNARK_SCALAR_FIELD ≠ 0 := by
  intro h
  have hVal : (SNARK_SCALAR_FIELD : Nat) = 0 := by
    simpa using congrArg (fun x : Uint256 => (x : Nat)) h
  rw [SNARK_SCALAR_FIELD_val] at hVal
  exact (by decide : (21888242871839275222246405745257275088548364400416034343698204186575808495617 : Nat) ≠ 0) hVal

theorem SNARK_SCALAR_FIELD_lt_modulus :
    (SNARK_SCALAR_FIELD : Nat) < Verity.Core.Uint256.modulus := by
  rw [SNARK_SCALAR_FIELD_val]
  decide

theorem modField_nat_eq (x : Uint256) :
    (modField x : Nat) = (x : Nat) % (SNARK_SCALAR_FIELD : Nat) := by
  have hFieldNonzero : (SNARK_SCALAR_FIELD : Nat) ≠ 0 := by
    intro h
    exact SNARK_SCALAR_FIELD_ne_zero (Verity.Core.Uint256.ext (by simpa using h.symm))
  have hModLt :
      (x : Nat) % (SNARK_SCALAR_FIELD : Nat) < Verity.Core.Uint256.modulus := by
    exact Nat.lt_trans
      (Nat.mod_lt _ (Nat.pos_of_ne_zero hFieldNonzero))
      SNARK_SCALAR_FIELD_lt_modulus
  simp only [modField, Verity.Core.Uint256.mod, hFieldNonzero, ↓reduceIte,
    Verity.Core.Uint256.val_ofNat]
  exact Nat.mod_eq_of_lt hModLt

theorem modField_lt (x : Uint256) :
    (modField x : Nat) < (SNARK_SCALAR_FIELD : Nat) := by
  rw [modField_nat_eq]
  have hFieldNonzero : (SNARK_SCALAR_FIELD : Nat) ≠ 0 := by
    intro h
    exact SNARK_SCALAR_FIELD_ne_zero (Verity.Core.Uint256.ext (by simpa using h.symm))
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero hFieldNonzero)

theorem modField_eq_self_of_lt (x : Uint256)
    (h : (x : Nat) < (SNARK_SCALAR_FIELD : Nat)) :
    modField x = x := by
  apply Verity.Core.Uint256.ext
  rw [modField_nat_eq]
  exact Nat.mod_eq_of_lt h

theorem modField_zero :
    modField 0 = 0 := by
  apply Verity.Core.Uint256.ext
  rw [modField_nat_eq]
  simp

theorem modField_SNARK_SCALAR_FIELD :
    modField SNARK_SCALAR_FIELD = 0 := by
  apply Verity.Core.Uint256.ext
  rw [modField_nat_eq]
  exact Nat.mod_self _

theorem modField_eq_zero_iff (x : Uint256) :
    modField x = 0 ↔ (x : Nat) % (SNARK_SCALAR_FIELD : Nat) = 0 := by
  constructor
  · intro h
    have hNat := congrArg (fun y : Uint256 => (y : Nat)) h
    have hNat' : (modField x : Nat) = 0 := by
      simpa using hNat
    rw [modField_nat_eq] at hNat'
    exact hNat'
  · intro h
    apply Verity.Core.Uint256.ext
    rw [modField_nat_eq]
    exact h

theorem modField_eq_of_nat_mod_eq {x y : Uint256}
    (h : (x : Nat) % (SNARK_SCALAR_FIELD : Nat) =
      (y : Nat) % (SNARK_SCALAR_FIELD : Nat)) :
    modField x = modField y := by
  apply Verity.Core.Uint256.ext
  rw [modField_nat_eq, modField_nat_eq]
  exact h

theorem modField_eq_iff_nat_mod_eq (x y : Uint256) :
    modField x = modField y ↔
      (x : Nat) % (SNARK_SCALAR_FIELD : Nat) =
        (y : Nat) % (SNARK_SCALAR_FIELD : Nat) := by
  constructor
  · intro h
    have hNat : (modField x : Nat) = (modField y : Nat) := by
      simpa using congrArg (fun z : Uint256 => (z : Nat)) h
    rw [modField_nat_eq, modField_nat_eq] at hNat
    exact hNat
  · exact modField_eq_of_nat_mod_eq

theorem modField_nat_mod_eq (x : Uint256) :
    (modField x : Nat) % (SNARK_SCALAR_FIELD : Nat) = (modField x : Nat) := by
  exact Nat.mod_eq_of_lt (modField_lt x)

theorem modField_idempotent (x : Uint256) :
    modField (modField x) = modField x := by
  exact modField_eq_self_of_lt (modField x) (modField_lt x)

/-! ## mulDiv / wad Helpers -/

private theorem modulus_eq_max_succ :
    Verity.Core.Uint256.modulus = MAX_UINT256 + 1 := by
  symm
  exact Verity.Core.Uint256.max_uint256_succ_eq_modulus

private theorem lt_modulus_of_le_max {n : Nat} (h : n ≤ MAX_UINT256) :
    n < Verity.Core.Uint256.modulus := by
  calc
    n < MAX_UINT256 + 1 := Nat.lt_succ_of_le h
    _ = Verity.Core.Uint256.modulus := by simp [modulus_eq_max_succ]

private theorem max_uint256_lt_modulus :
    MAX_UINT256 < Verity.Core.Uint256.modulus :=
  lt_modulus_of_le_max (Nat.le_refl MAX_UINT256)

/-! ## TickLib fixed-point exponential reference -/

/-- The nonnegative residual kernel used by `tickWExpReference` is monotone. -/
theorem wExpCubicKernel_mono {a b : Nat} (h : a ≤ b) :
    wExpCubicKernel a ≤ wExpCubicKernel b := by
  have hsq : a * a ≤ b * b := Nat.mul_le_mul h h
  have hsecond :
      (a * a) / (2 * WAD_NAT) ≤ (b * b) / (2 * WAD_NAT) :=
    Nat.div_le_div_right hsq
  have hthirdNum :
      ((a * a) / (2 * WAD_NAT)) * a ≤
        ((b * b) / (2 * WAD_NAT)) * b :=
    Nat.mul_le_mul hsecond h
  have hthird :
      (((a * a) / (2 * WAD_NAT)) * a) / (3 * WAD_NAT) ≤
        (((b * b) / (2 * WAD_NAT)) * b) / (3 * WAD_NAT) :=
    Nat.div_le_div_right hthirdNum
  simpa [wExpCubicKernel] using
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl WAD_NAT) h) hsecond) hthird

/-- The cubic residual kernel always contains the wad-scaled linear term. -/
theorem wExpCubicKernel_ge_linear (r : Nat) :
    WAD_NAT + r ≤ wExpCubicKernel r := by
  simp [wExpCubicKernel, Nat.add_assoc]

/-- The wad scale used by the TickLib exponential kernel is positive. -/
private theorem WAD_NAT_pos : 0 < WAD_NAT := by
  decide

/-- The cubic residual kernel never exceeds the exact rational cubic obtained by
clearing denominators by `6 * WAD_NAT^2`.

This is the upper half of the floor sandwich: both divisions in
`wExpCubicKernel` round down, so the scaled integer kernel is bounded by
`6*WAD^3 + 6*WAD^2*r + 3*WAD*r^2 + r^3`, the exact cubic numerator for
`WAD * (1 + x + x^2/2 + x^3/6)` with `x = r / WAD`. -/
theorem wExpCubicKernel_scaled_le_exact_cubic (r : Nat) :
    6 * WAD_NAT^2 * wExpCubicKernel r ≤
      6 * WAD_NAT^3 + 6 * WAD_NAT^2 * r + 3 * WAD_NAT * r^2 + r^3 := by
  let second := (r * r) / (2 * WAD_NAT)
  let third := (second * r) / (3 * WAD_NAT)
  have hsecond : second * (2 * WAD_NAT) ≤ r * r := by
    simpa [second] using Nat.div_mul_le_self (r * r) (2 * WAD_NAT)
  have hsecondScaled : 6 * WAD_NAT^2 * second ≤ 3 * WAD_NAT * r^2 := by
    nlinarith [hsecond]
  have hthird : third * (3 * WAD_NAT) ≤ second * r := by
    simpa [third] using Nat.div_mul_le_self (second * r) (3 * WAD_NAT)
  have hthirdScaled : 6 * WAD_NAT^2 * third ≤ r^3 := by
    nlinarith [hsecond, hthird]
  calc
    6 * WAD_NAT^2 * wExpCubicKernel r
        = 6 * WAD_NAT^3 + 6 * WAD_NAT^2 * r +
            6 * WAD_NAT^2 * second + 6 * WAD_NAT^2 * third := by
          simp [wExpCubicKernel, second, third]
          ring
    _ ≤ 6 * WAD_NAT^3 + 6 * WAD_NAT^2 * r +
          3 * WAD_NAT * r^2 + r^3 := by
        have htail :
            6 * WAD_NAT^2 * second + 6 * WAD_NAT^2 * third ≤
              3 * WAD_NAT * r^2 + r^3 :=
          Nat.add_le_add hsecondScaled hthirdScaled
        simpa [Nat.add_assoc] using
          Nat.add_le_add_left htail (6 * WAD_NAT^3 + 6 * WAD_NAT^2 * r)

/-- The exact rational cubic is less than the scaled kernel plus the explicit
integer slack `r / (3 * WAD_NAT) + 3`.

This is the lower half of the floor sandwich after clearing denominators by
`6 * WAD_NAT^2`. The first division can lose less than one `second` unit; that
loss is multiplied by `r` before the second division, yielding the
`r / (3 * WAD_NAT)` term. The two floor operations contribute the constant
part of the slack. -/
theorem exact_cubic_lt_wExpCubicKernel_scaled_add_error (r : Nat) :
    6 * WAD_NAT^3 + 6 * WAD_NAT^2 * r + 3 * WAD_NAT * r^2 + r^3 <
      6 * WAD_NAT^2 * (wExpCubicKernel r + (r / (3 * WAD_NAT) + 3)) := by
  let second := (r * r) / (2 * WAD_NAT)
  let third := (second * r) / (3 * WAD_NAT)
  let q := r / (3 * WAD_NAT)
  have h2W_pos : 0 < 2 * WAD_NAT := by nlinarith [WAD_NAT_pos]
  have h3W_pos : 0 < 3 * WAD_NAT := by nlinarith [WAD_NAT_pos]
  have hsecond_lt : r * r < (second + 1) * (2 * WAD_NAT) := by
    simpa [second, Nat.mul_comm] using Nat.lt_mul_div_succ (r * r) h2W_pos
  have hsecondScaled_lt : 3 * WAD_NAT * r^2 < 6 * WAD_NAT^2 * (second + 1) := by
    nlinarith [hsecond_lt]
  have hthird_lt : second * r < (third + 1) * (3 * WAD_NAT) := by
    simpa [third, Nat.mul_comm] using Nat.lt_mul_div_succ (second * r) h3W_pos
  have hr_lt : r < (q + 1) * (3 * WAD_NAT) := by
    simpa [q, Nat.mul_comm] using Nat.lt_mul_div_succ r h3W_pos
  have hthirdScaled_lt : r^3 < 6 * WAD_NAT^2 * (third + q + 2) := by
    have hsecond_mul_le :
        r * r * r ≤ ((second + 1) * (2 * WAD_NAT)) * r := by
      exact Nat.mul_le_mul_right r (Nat.le_of_lt hsecond_lt)
    have hr3_decomp : r^3 ≤ 2 * WAD_NAT * second * r + 2 * WAD_NAT * r := by
      nlinarith [hsecond_mul_le]
    have hthird_part : 2 * WAD_NAT * second * r <
        6 * WAD_NAT^2 * (third + 1) := by
      have hthird_mul_lt :
          (2 * WAD_NAT) * (second * r) <
            (2 * WAD_NAT) * ((third + 1) * (3 * WAD_NAT)) := by
        exact Nat.mul_lt_mul_of_pos_left hthird_lt h2W_pos
      nlinarith [hthird_mul_lt]
    have hr_part : 2 * WAD_NAT * r < 6 * WAD_NAT^2 * (q + 1) := by
      have hr_mul_lt :
          (2 * WAD_NAT) * r < (2 * WAD_NAT) * ((q + 1) * (3 * WAD_NAT)) := by
        exact Nat.mul_lt_mul_of_pos_left hr_lt h2W_pos
      nlinarith [hr_mul_lt]
    nlinarith
  calc
    6 * WAD_NAT^3 + 6 * WAD_NAT^2 * r + 3 * WAD_NAT * r^2 + r^3
        < 6 * WAD_NAT^3 + 6 * WAD_NAT^2 * r +
            6 * WAD_NAT^2 * (second + 1) +
            6 * WAD_NAT^2 * (third + q + 2) := by
          nlinarith
    _ = 6 * WAD_NAT^2 * (wExpCubicKernel r + (r / (3 * WAD_NAT) + 3)) := by
        simp [wExpCubicKernel, second, third, q]
        ring

/-- On the nonnegative TickLib residual interval (`r ≤ WEXP_LN2`), the
unbounded floor-propagation term vanishes, giving a constant-`3` lower sandwich
for the exact cubic numerator. -/
theorem exact_cubic_lt_wExpCubicKernel_scaled_add_three {r : Nat}
    (hr : r ≤ WEXP_LN2) :
    6 * WAD_NAT^3 + 6 * WAD_NAT^2 * r + 3 * WAD_NAT * r^2 + r^3 <
      6 * WAD_NAT^2 * (wExpCubicKernel r + 3) := by
  have hq_zero : r / (3 * WAD_NAT) = 0 := by
    apply Nat.div_eq_of_lt
    have hln2_lt : WEXP_LN2 < 3 * WAD_NAT := by decide
    exact Nat.lt_of_le_of_lt hr hln2_lt
  calc
    6 * WAD_NAT^3 + 6 * WAD_NAT^2 * r + 3 * WAD_NAT * r^2 + r^3
        < 6 * WAD_NAT^2 * (wExpCubicKernel r + (r / (3 * WAD_NAT) + 3)) :=
          exact_cubic_lt_wExpCubicKernel_scaled_add_error r
    _ = 6 * WAD_NAT^2 * (wExpCubicKernel r + 3) := by
        rw [hq_zero]

/-- The exact cubic Taylor polynomial used by the residual kernel has a
fourth-order analytic error against `Real.exp` on the TickLib residual range. -/
theorem exact_cubic_real_error {r : Nat} (hr : r ≤ WEXP_LN2) :
    |Real.exp ((r : ℝ) / WAD_NAT)
        - (1 + (r:ℝ)/WAD_NAT + ((r:ℝ)/WAD_NAT)^2 / 2 + ((r:ℝ)/WAD_NAT)^3 / 6)|
      ≤ ((r:ℝ)/WAD_NAT)^4 * (5 / 96) := by
  let x : ℝ := (r : ℝ) / WAD_NAT
  have hWpos : (0 : ℝ) < WAD_NAT := by norm_num [WAD_NAT]
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hr_real : (r : ℝ) ≤ WEXP_LN2 := by exact_mod_cast hr
  have hln2_lt_wad : (WEXP_LN2 : ℝ) < WAD_NAT := by norm_num [WEXP_LN2, WAD_NAT]
  have hr_le_wad : (r : ℝ) ≤ WAD_NAT := le_trans hr_real (le_of_lt hln2_lt_wad)
  have hx_le_one : x ≤ 1 := by
    dsimp [x]
    rw [div_le_one hWpos]
    exact hr_le_wad
  have hx_abs : |x| ≤ 1 := by
    rwa [abs_of_nonneg hx_nonneg]
  have h := Real.exp_bound (x := x) hx_abs (n := 4) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 4, x ^ m / (m.factorial : ℝ)) =
      1 + x + x^2 / 2 + x^3 / 6 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have hx_abs_pow : |x| ^ 4 = x ^ 4 := by rw [abs_of_nonneg hx_nonneg]
  rw [hx_abs_pow] at h
  norm_num [Nat.factorial] at h
  simpa [x] using h

/-- The integer residual kernel differs from the real exponential by the sum of
its floor-truncation slack and the cubic Taylor remainder on the TickLib
residual range. -/
theorem wExpCubicKernel_real_error {r : Nat} (hr : r ≤ WEXP_LN2) :
    |((wExpCubicKernel r : ℝ) / WAD_NAT) - Real.exp ((r:ℝ)/WAD_NAT)|
      ≤ 3 / (WAD_NAT : ℝ) + ((r:ℝ)/WAD_NAT)^4 * (5 / 96) := by
  let x : ℝ := (r : ℝ) / WAD_NAT
  let P : ℝ := 1 + x + x^2 / 2 + x^3 / 6
  let k : ℝ := (wExpCubicKernel r : ℝ) / WAD_NAT
  have hb2 : |Real.exp x - P| ≤ x^4 * (5 / 96) := by
    simpa [x, P] using exact_cubic_real_error (r := r) hr
  have hle : k ≤ P := by
    have h1nat := wExpCubicKernel_scaled_le_exact_cubic r
    have h1real : (6 : ℝ) * (WAD_NAT : ℝ)^2 * (wExpCubicKernel r : ℝ) ≤
        6 * (WAD_NAT : ℝ)^3 + 6 * (WAD_NAT : ℝ)^2 * r +
          3 * (WAD_NAT : ℝ) * r^2 + r^3 := by
      exact_mod_cast h1nat
    dsimp [k, P, x]
    norm_num [WAD_NAT] at h1real ⊢
    nlinarith [h1real]
  have hge : P ≤ k + 3 / (WAD_NAT : ℝ) := by
    have h2nat := exact_cubic_lt_wExpCubicKernel_scaled_add_three (r := r) hr
    have h2real : 6 * (WAD_NAT : ℝ)^3 + 6 * (WAD_NAT : ℝ)^2 * r +
        3 * (WAD_NAT : ℝ) * r^2 + r^3 <
          (6 : ℝ) * (WAD_NAT : ℝ)^2 * (wExpCubicKernel r + 3 : Nat) := by
      exact_mod_cast h2nat
    dsimp [k, P, x]
    norm_num [WAD_NAT] at h2real ⊢
    nlinarith [h2real]
  have hkP : |k - P| ≤ 3 / (WAD_NAT : ℝ) := by
    rw [abs_le]
    constructor
    · nlinarith [hge]
    · have hslack : (0 : ℝ) ≤ 3 / (WAD_NAT : ℝ) := by positivity
      nlinarith [hle, hslack]
  have hPexp : |P - Real.exp x| ≤ x^4 * (5 / 96) := by
    rw [abs_sub_comm]
    exact hb2
  calc
    |k - Real.exp x| ≤ |k - P| + |P - Real.exp x| := abs_sub_le k P (Real.exp x)
    _ ≤ 3 / (WAD_NAT : ℝ) + x^4 * (5 / 96) := add_le_add hkP hPexp

/-- The TickLib range-reduction `ln 2` constant approximates `Real.log 2`
within three tenths of a nanounit at WAD scale. -/
theorem wExpLn2_approx_error :
    |((WEXP_LN2 : ℝ) / WAD_NAT) - Real.log 2| ≤ 3 / 10 ^ 10 := by
  rw [abs_le]
  constructor
  · have hlog_lt : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
    norm_num [WEXP_LN2, WAD_NAT] at hlog_lt ⊢
    linarith
  · have hlog_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    norm_num [WEXP_LN2, WAD_NAT] at hlog_gt ⊢
    linarith

/-- `Real.exp` of the TickLib range-reduction `ln 2` constant equals `2` to
within two parts per billion: the base of the `2^q` scaling in
`tickWExpReference`. -/
theorem wExpLn2_exp_approx_two :
    |Real.exp ((WEXP_LN2 : ℝ) / WAD_NAT) - 2| ≤ 2 / 10 ^ 9 := by
  have hbound : |((WEXP_LN2 : ℝ) / WAD_NAT) - Real.log 2| ≤ 3 / 10 ^ 10 :=
    wExpLn2_approx_error
  have hle1 : |((WEXP_LN2 : ℝ) / WAD_NAT) - Real.log 2| ≤ 1 :=
    le_trans hbound (by norm_num)
  have hstep :
      |Real.exp ((WEXP_LN2 : ℝ) / WAD_NAT - Real.log 2) - 1|
        ≤ 2 * |((WEXP_LN2 : ℝ) / WAD_NAT) - Real.log 2| :=
    Real.abs_exp_sub_one_le hle1
  have hexp :
      Real.exp ((WEXP_LN2 : ℝ) / WAD_NAT) - 2
        = 2 * (Real.exp ((WEXP_LN2 : ℝ) / WAD_NAT - Real.log 2) - 1) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  rw [hexp, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
  calc 2 * |Real.exp ((WEXP_LN2 : ℝ) / WAD_NAT - Real.log 2) - 1|
        ≤ 2 * (2 * |((WEXP_LN2 : ℝ) / WAD_NAT) - Real.log 2|) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ ≤ 2 * (2 * (3 / 10 ^ 10)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbound (by norm_num)) (by norm_num)
    _ ≤ 2 / 10 ^ 9 := by norm_num

/-- Exact range-reduction identity at WAD scale: the full WAD-scaled input
decomposes as the reduced residual plus `q` copies of the `ln 2` constant.
No approximation — this is the real-cast counterpart of `wExpRangeReduction_exact`. -/
theorem wExpRangeReduction_real (xAbs : Nat) :
    (xAbs : ℝ) / (WAD_NAT : ℝ)
      = (wExpRangeR xAbs : ℝ) / (WAD_NAT : ℝ)
        + (wExpRangeQ xAbs : ℝ) * ((WEXP_LN2 : ℝ) / (WAD_NAT : ℝ)) := by
  have hcast : (xAbs : ℝ)
      = (wExpRangeR xAbs : ℝ) + (wExpRangeQ xAbs : ℝ) * (WEXP_LN2 : ℝ) := by
    simp only [wExpRangeR, Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [hcast]; ring

/-- `Real.exp` of the full WAD-scaled input factors through the reduced residual
and the `2^q` scaling base `exp (ln2 / WAD)`, by `exp` of the exact range-reduction
decomposition. Bridges the residual-kernel error bound to full `exp`. -/
theorem tickWExp_exp_decomp (xAbs : Nat) :
    Real.exp ((xAbs : ℝ) / (WAD_NAT : ℝ))
      = Real.exp ((wExpRangeR xAbs : ℝ) / (WAD_NAT : ℝ))
        * Real.exp ((WEXP_LN2 : ℝ) / (WAD_NAT : ℝ)) ^ (wExpRangeQ xAbs) := by
  rw [wExpRangeReduction_real, Real.exp_add, Real.exp_nat_mul]

/-- One-step exponent reconciliation for the power telescoping bound:
folds the `n * M^(n-1)` inductive estimate plus the trailing `M^n` term into the
`(n+1) * M^n` shape. The `cases n` split reconciles the `M^(n-1)` Nat-subtraction
exponent against `M^n` at `n = 0`. -/
private theorem pow_step_bound (M d : ℝ) (n : Nat) :
    M * ((n : ℝ) * M ^ (n - 1) * d) + d * M ^ n ≤
      ((n + 1 : Nat) : ℝ) * M ^ n * d := by
  cases n with
  | zero => simp
  | succ n =>
      have hpow :
          M * (((n + 1 : Nat) : ℝ) * M ^ ((n + 1) - 1) * d) =
            ((n + 1 : Nat) : ℝ) * M ^ (n + 1) * d := by
        simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
      rw [hpow]
      have hcast :
          (((n + 1 : Nat) : ℝ) * M ^ (n + 1) * d + d * M ^ (n + 1)) =
            ((n + 2 : Nat) : ℝ) * M ^ (n + 1) * d := by
        norm_num
        ring
      rw [hcast]

/-- Telescoping Lipschitz bound for powers over the reals.

This is the standard factorization of `c^n - b^n`, bounded termwise by the
larger absolute base. It is stated with `n * M^(n-1)` so downstream estimates
can multiply a one-step base error into an `n`-step power error. -/
theorem abs_pow_sub_pow_le (b c : ℝ) (n : Nat) :
    |c ^ n - b ^ n| ≤
      (n : ℝ) * (max |b| |c|) ^ (n - 1) * |c - b| := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let M : ℝ := max |b| |c|
      let d : ℝ := |c - b|
      have hM_nonneg : 0 ≤ M := by
        dsimp [M]
        exact le_max_of_le_left (abs_nonneg b)
      have hbM : |b| ≤ M := by
        dsimp [M]
        exact le_max_left |b| |c|
      have hcM : |c| ≤ M := by
        dsimp [M]
        exact le_max_right |b| |c|
      have hd_nonneg : 0 ≤ d := by
        dsimp [d]
        exact abs_nonneg (c - b)
      have hdecomp :
          c ^ (n + 1) - b ^ (n + 1) =
            c * (c ^ n - b ^ n) + (c - b) * b ^ n := by
        ring
      calc
        |c ^ (n + 1) - b ^ (n + 1)|
            = |c * (c ^ n - b ^ n) + (c - b) * b ^ n| := by rw [hdecomp]
        _ ≤ |c * (c ^ n - b ^ n)| + |(c - b) * b ^ n| :=
            abs_add_le _ _
        _ = |c| * |c ^ n - b ^ n| + d * |b| ^ n := by
            simp [abs_mul, abs_pow, d, mul_comm]
        _ ≤ M * ((n : ℝ) * M ^ (n - 1) * d) + d * M ^ n := by
            have hleft :
                |c| * |c ^ n - b ^ n| ≤
                  M * ((n : ℝ) * M ^ (n - 1) * d) :=
              mul_le_mul hcM ih (abs_nonneg _) hM_nonneg
            have hright : d * |b| ^ n ≤ d * M ^ n :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg b) hbM n) hd_nonneg
            exact add_le_add hleft hright
        _ ≤ ((n + 1 : Nat) : ℝ) * M ^ n * d := pow_step_bound M d n

/-- Power error for the TickLib `ln 2` range-reduction base.

We use the closed form
`q * (2001/1000)^q * (2/10^9)`: the existing `2e-9` estimate shows
`Real.exp (WEXP_LN2/WAD)` is at most `2.000000002`, hence below `2.001`.
This slightly looser base keeps the proof direct while giving a genuine
usable scaling-side bound for the downstream capstone. -/
theorem wExpLn2_pow_approx_two_pow (q : Nat) :
    |Real.exp ((WEXP_LN2 : ℝ) / WAD_NAT) ^ q - 2 ^ q| ≤
      (q : ℝ) * (2001 / 1000) ^ q * (2 / 10 ^ 9) := by
  let e : ℝ := Real.exp ((WEXP_LN2 : ℝ) / WAD_NAT)
  have herr : |e - 2| ≤ 2 / 10 ^ 9 := by
    simpa [e] using wExpLn2_exp_approx_two
  have he_nonneg : 0 ≤ e := by
    dsimp [e]
    positivity
  have he_abs_le : |e| ≤ 2001 / 1000 := by
    rw [abs_of_nonneg he_nonneg]
    have he_upper : e - 2 ≤ 2 / 10 ^ 9 := (abs_le.mp herr).2
    nlinarith
  have hmax_le : max |(2 : ℝ)| |e| ≤ 2001 / 1000 := by
    apply max_le
    · norm_num
    · exact he_abs_le
  have hbase_nonneg : 0 ≤ max |(2 : ℝ)| |e| := le_max_of_le_left (abs_nonneg (2 : ℝ))
  have htarget_nonneg : 0 ≤ (2001 / 1000 : ℝ) := by norm_num
  have hpow_le :
      (max |(2 : ℝ)| |e|) ^ (q - 1) ≤ (2001 / 1000 : ℝ) ^ q := by
    calc
      (max |(2 : ℝ)| |e|) ^ (q - 1)
          ≤ (2001 / 1000 : ℝ) ^ (q - 1) :=
            pow_le_pow_left₀ hbase_nonneg hmax_le (q - 1)
      _ ≤ (2001 / 1000 : ℝ) ^ q := by
          have hge_one : (1 : ℝ) ≤ 2001 / 1000 := by norm_num
          exact pow_le_pow_right₀ hge_one (Nat.sub_le q 1)
  have htel :
      |e ^ q - 2 ^ q| ≤
        (q : ℝ) * (max |(2 : ℝ)| |e|) ^ (q - 1) * |e - 2| :=
    abs_pow_sub_pow_le 2 e q
  calc
    |e ^ q - 2 ^ q|
        ≤ (q : ℝ) * (max |(2 : ℝ)| |e|) ^ (q - 1) * |e - 2| := htel
    _ ≤ (q : ℝ) * (2001 / 1000) ^ q * (2 / 10 ^ 9) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hpow_le (Nat.cast_nonneg q))
          herr
          (abs_nonneg (e - 2))
          (mul_nonneg (Nat.cast_nonneg q) (pow_nonneg htarget_nonneg q))

private theorem sdivTrunc_of_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 < b) :
    sdivTrunc a b = Int.ofNat (a.toNat / b.natAbs) := by
  unfold sdivTrunc
  have hb_ne : b ≠ 0 := by omega
  have hnot : ¬a < 0 := by omega
  simp [hb_ne, hnot]

private theorem sdivTrunc_ofNat_mul_WAD (a k : Nat) (hk : 0 < k) :
    sdivTrunc (Int.ofNat a) (Int.ofNat (k * WAD_NAT)) =
      Int.ofNat (a / (k * WAD_NAT)) := by
  have hden : (0 : Int) < Int.ofNat (k * WAD_NAT) := by
    exact Int.natCast_pos.mpr (Nat.mul_pos hk WAD_NAT_pos)
  have h :=
    sdivTrunc_of_nonneg (a := Int.ofNat a) (b := Int.ofNat (k * WAD_NAT))
      (Int.natCast_nonneg a) hden
  have hnum : (Int.ofNat a).toNat = a := Int.toNat_natCast a
  have hdenAbs : (Int.ofNat (k * WAD_NAT)).natAbs = k * WAD_NAT :=
    Int.natAbs_natCast (k * WAD_NAT)
  rw [hnum, hdenAbs] at h
  exact h

private theorem sdivTrunc_sq_of_nonneg {r : Int} (hr : 0 ≤ r) :
    sdivTrunc (r * r) (2 * Int.ofNat WAD_NAT) =
      Int.ofNat ((r.toNat * r.toNat) / (2 * WAD_NAT)) := by
  have hsquare : r * r = Int.ofNat (r.toNat * r.toNat) := by
    rw [← Int.toNat_of_nonneg hr]
    change ((r.toNat : Nat) : Int) * ((r.toNat : Nat) : Int) =
      ((r.toNat * r.toNat : Nat) : Int)
    exact_mod_cast rfl
  rw [hsquare]
  simpa [Int.natCast_mul] using
    sdivTrunc_ofNat_mul_WAD (r.toNat * r.toNat) 2 (by norm_num)

/-- On the non-negative residual branch, signed truncating division agrees with
the natural-number cubic kernel used by the Tier-B real-error proof. -/
theorem wExpSignedCubicKernel_eq_natKernel_of_nonneg {r : Int} (hr : 0 ≤ r) :
    wExpSignedCubicKernel r = (wExpCubicKernel r.toNat : Int) := by
  unfold wExpSignedCubicKernel wExpCubicKernel
  rw [sdivTrunc_sq_of_nonneg hr]
  have hr_cast : (Int.ofNat r.toNat : Int) = r := by
    exact Int.toNat_of_nonneg hr
  let secondNat := r.toNat * r.toNat / (2 * WAD_NAT)
  have hthird :
      sdivTrunc (Int.ofNat secondNat * r) (3 * Int.ofNat WAD_NAT) =
        Int.ofNat ((secondNat * r.toNat) / (3 * WAD_NAT)) := by
    have hleft : Int.ofNat secondNat * r = Int.ofNat (secondNat * r.toNat) := by
      rw [← hr_cast]
      change ((secondNat : Nat) : Int) * ((r.toNat : Nat) : Int) =
        ((secondNat * r.toNat : Nat) : Int)
      exact_mod_cast rfl
    rw [hleft]
    simpa [Int.natCast_mul] using
      sdivTrunc_ofNat_mul_WAD (secondNat * r.toNat) 3 (by norm_num)
  change
    Int.ofNat WAD_NAT + r + Int.ofNat secondNat +
        sdivTrunc (Int.ofNat secondNat * r) (3 * Int.ofNat WAD_NAT) =
      ↑(WAD_NAT + r.toNat + secondNat + secondNat * r.toNat / (3 * WAD_NAT))
  rw [hthird, ← hr_cast]
  simp [secondNat]

/-- Tier-B's natural cubic-kernel error bound applies directly to the signed
kernel on the non-negative residual branch. -/
theorem wExpSignedCubicKernel_real_error_nonneg {r : Int}
    (hr0 : 0 ≤ r) (hr1 : r ≤ (WEXP_LN2 : Int)) :
    |((wExpSignedCubicKernel r : ℝ) / WAD_NAT) - Real.exp ((r:ℝ)/WAD_NAT)|
      ≤ 3 / (WAD_NAT : ℝ) + ((r:ℝ)/WAD_NAT)^4 * (5 / 96) := by
  have hrNat : r.toNat ≤ WEXP_LN2 := by
    omega
  have hcastR : ((r.toNat : Nat) : ℝ) = (r : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hr0
  have hkernel := wExpSignedCubicKernel_eq_natKernel_of_nonneg (r := r) hr0
  have hnat := wExpCubicKernel_real_error (r := r.toNat) hrNat
  rw [hkernel]
  simpa [hcastR] using hnat

private theorem sdivTrunc_neg_ofNat_mul_WAD (a k : Nat) (hk : 0 < k) :
    sdivTrunc (-(Int.ofNat a)) (Int.ofNat (k * WAD_NAT)) =
      -Int.ofNat (a / (k * WAD_NAT)) := by
  unfold sdivTrunc
  have hb_ne : (Int.ofNat (k * WAD_NAT) : Int) ≠ 0 := by
    exact Int.natCast_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hk WAD_NAT_pos))
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  by_cases ha : a = 0
  · subst a
    simp [WAD_NAT, hk_ne]
  · have hneg : (-(Int.ofNat a) : Int) < 0 := by
      exact neg_neg_of_pos (Int.natCast_pos.mpr (Nat.pos_of_ne_zero ha))
    have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
    have hdenAbs : Int.natAbs ((k : Int) * (WAD_NAT : Int)) = k * WAD_NAT := by
      simpa [Int.natCast_mul] using Int.natAbs_natCast (k * WAD_NAT)
    have hdenAbsInt : ((Int.natAbs ((k : Int) * (WAD_NAT : Int)) : Nat) : Int) =
        (k : Int) * (WAD_NAT : Int) := by
      rw [hdenAbs]
      norm_num [Int.natCast_mul]
    have hdenAbsInt' :
        |(k : Int) * (1000000000000000000 : Int)| =
          (k : Int) * (1000000000000000000 : Int) := by
      rw [abs_of_nonneg]
      positivity
    simp [WAD_NAT, hk_ne, ha_pos]

private theorem sdivTrunc_sq_of_neg_nat (s : Nat) :
    sdivTrunc (-(s : Int) * -(s : Int)) (2 * Int.ofNat WAD_NAT) =
      Int.ofNat ((s * s) / (2 * WAD_NAT)) := by
  have hsquare : (-(s : Int) * -(s : Int)) = Int.ofNat (s * s) := by
    norm_num [Int.natCast_mul]
  rw [hsquare]
  simpa [Int.natCast_mul] using
    sdivTrunc_ofNat_mul_WAD (s * s) 2 (by norm_num)

private theorem sdivTrunc_neg_third_of_nat (secondNat s : Nat) :
    sdivTrunc (Int.ofNat secondNat * -(s : Int)) (3 * Int.ofNat WAD_NAT) =
      -Int.ofNat ((secondNat * s) / (3 * WAD_NAT)) := by
  have hmul : Int.ofNat secondNat * -(s : Int) = -Int.ofNat (secondNat * s) := by
    norm_num [Int.natCast_mul]
  rw [hmul]
  simpa [Int.natCast_mul] using
    sdivTrunc_neg_ofNat_mul_WAD (secondNat * s) 3 (by norm_num)

/-- On a negative residual, signed truncating division evaluates the TickLib
cubic kernel as the expected alternating floor expression. -/
theorem wExpSignedCubicKernel_neg_eq (s : Nat) :
    wExpSignedCubicKernel (-(s:Int))
      = (WAD_NAT:Int) - s + ((s*s)/(2*WAD_NAT) : Nat)
          - ((((s*s)/(2*WAD_NAT)) * s)/(3*WAD_NAT) : Nat) := by
  unfold wExpSignedCubicKernel
  rw [sdivTrunc_sq_of_neg_nat s]
  let secondNat := (s * s) / (2 * WAD_NAT)
  change
    Int.ofNat WAD_NAT + -(s : Int) + Int.ofNat secondNat +
        sdivTrunc (Int.ofNat secondNat * -(s : Int)) (3 * Int.ofNat WAD_NAT) =
      (WAD_NAT : Int) - s + (secondNat : Int) -
        (((secondNat * s) / (3 * WAD_NAT) : Nat) : Int)
  rw [sdivTrunc_neg_third_of_nat secondNat s]
  simp [sub_eq_add_neg, add_assoc, add_comm]

/-- The cubic Taylor polynomial has the same fourth-order analytic error bound
for any real argument with absolute value at most one. -/
theorem cubic_real_error_abs {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x^2 / 2 + x^3 / 6)| ≤ |x|^4 * (5 / 96) := by
  have h := Real.exp_bound (x := x) hx (n := 4) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 4, x ^ m / (m.factorial : ℝ)) =
      1 + x + x^2 / 2 + x^3 / 6 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  norm_num [Nat.factorial] at h
  exact h

private theorem nat_div_floor_real_bounds (n d : Nat) (hd : 0 < d) :
    0 ≤ (n:ℝ)/(d:ℝ) - ((n/d:Nat):ℝ) ∧
      (n:ℝ)/(d:ℝ) - ((n/d:Nat):ℝ) < 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hloNat : (n / d) * d ≤ n := Nat.div_mul_le_self n d
  have hhiNat : n < (n / d + 1) * d := by
    simpa [Nat.mul_comm] using Nat.lt_mul_div_succ n hd
  have hlo : ((n / d : Nat) : ℝ) * (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hloNat
  have hhi : (n : ℝ) < ((n / d + 1 : Nat) : ℝ) * (d : ℝ) := by exact_mod_cast hhiNat
  have hlo' : ((n / d : Nat) : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdR]
    exact hlo
  have hhi' : (n : ℝ) / (d : ℝ) < ((n / d : Nat) : ℝ) + 1 := by
    have htmp : (n : ℝ) / (d : ℝ) < ((n / d + 1 : Nat) : ℝ) := by
      rw [div_lt_iff₀ hdR]
      exact hhi
    simpa using htmp
  constructor <;> linarith

private theorem neg_second_floor_slack_bounds (s : Nat) :
    let secondNat := (s * s) / (2 * WAD_NAT)
    0 ≤ (s : ℝ)^2 / (2 * (WAD_NAT : ℝ)) - (secondNat : ℝ) ∧
      (s : ℝ)^2 / (2 * (WAD_NAT : ℝ)) - (secondNat : ℝ) < 1 := by
  intro secondNat
  have h2W : 0 < 2 * WAD_NAT := by decide
  have h := nat_div_floor_real_bounds (s * s) (2 * WAD_NAT) h2W
  constructor
  · have h0 := h.1
    norm_num [WAD_NAT, secondNat, pow_two, mul_assoc, mul_comm, mul_left_comm] at h0 ⊢
    exact h0
  · have h1 := h.2
    norm_num [WAD_NAT, secondNat, pow_two, mul_assoc, mul_comm, mul_left_comm] at h1 ⊢
    exact h1

private theorem neg_third_floor_slack_bounds (s : Nat) :
    let secondNat := (s * s) / (2 * WAD_NAT)
    let thirdNat := (secondNat * s) / (3 * WAD_NAT)
    0 ≤ (secondNat : ℝ) * (s : ℝ) / (3 * (WAD_NAT : ℝ)) - (thirdNat : ℝ) ∧
      (secondNat : ℝ) * (s : ℝ) / (3 * (WAD_NAT : ℝ)) - (thirdNat : ℝ) < 1 := by
  intro secondNat thirdNat
  have h3W : 0 < 3 * WAD_NAT := by decide
  have h := nat_div_floor_real_bounds (secondNat * s) (3 * WAD_NAT) h3W
  constructor
  · have h0 := h.1
    norm_num [WAD_NAT, thirdNat, mul_assoc, mul_comm, mul_left_comm] at h0 ⊢
    exact h0
  · have h1 := h.2
    norm_num [WAD_NAT, thirdNat, mul_assoc, mul_comm, mul_left_comm] at h1 ⊢
    exact h1

private theorem neg_third_exact_bridge_bounds {s : Nat} (hs : s ≤ WEXP_RANGE_OFFSET) :
    let secondNat := (s * s) / (2 * WAD_NAT)
    0 ≤ (s : ℝ)^3 / (6 * (WAD_NAT : ℝ)^2) -
        (secondNat : ℝ) * (s : ℝ) / (3 * (WAD_NAT : ℝ)) ∧
      (s : ℝ)^3 / (6 * (WAD_NAT : ℝ)^2) -
        (secondNat : ℝ) * (s : ℝ) / (3 * (WAD_NAT : ℝ)) < 1 := by
  intro secondNat
  have hWpos : (0 : ℝ) < (WAD_NAT : ℝ) := by norm_num [WAD_NAT]
  have hWne : (WAD_NAT : ℝ) ≠ 0 := ne_of_gt hWpos
  have hsR : (s : ℝ) ≤ WEXP_RANGE_OFFSET := by exact_mod_cast hs
  have hoff : (WEXP_RANGE_OFFSET : ℝ) < WAD_NAT := by norm_num [WEXP_RANGE_OFFSET, WAD_NAT]
  have hs_lt_W : (s : ℝ) < WAD_NAT := lt_of_le_of_lt hsR hoff
  have hs_over_lt_one : (s : ℝ) / (3 * (WAD_NAT : ℝ)) < 1 := by
    have h3Wreal : (0 : ℝ) < 3 * (WAD_NAT : ℝ) := by positivity
    rw [div_lt_iff₀ h3Wreal]
    nlinarith [hs_lt_W, hWpos]
  have hA := neg_second_floor_slack_bounds s
  have hCeq : (s : ℝ)^3 / (6 * (WAD_NAT : ℝ)^2) -
        (secondNat : ℝ) * (s : ℝ) / (3 * (WAD_NAT : ℝ)) =
      ((s : ℝ)^2 / (2 * (WAD_NAT : ℝ)) - (secondNat : ℝ)) *
        ((s : ℝ) / (3 * (WAD_NAT : ℝ))) := by
    field_simp [hWne]
    ring
  constructor
  · rw [hCeq]
    have hs_nonneg : (0 : ℝ) ≤ s := by positivity
    exact mul_nonneg hA.1 (div_nonneg hs_nonneg (by positivity))
  · rw [hCeq]
    have hs_nonneg : (0 : ℝ) ≤ s := by positivity
    nlinarith [hA.1, hA.2, hs_over_lt_one, hs_nonneg, hWpos]

private theorem neg_kernel_inner_floor_slack {s : Nat} (hs : s ≤ WEXP_RANGE_OFFSET) :
    let secondNat := (s * s) / (2 * WAD_NAT)
    let thirdNat := (secondNat * s) / (3 * WAD_NAT)
    |((secondNat : ℝ) - (s : ℝ)^2 / (2 * (WAD_NAT : ℝ)) -
        ((thirdNat : ℝ) - (s : ℝ)^3 / (6 * (WAD_NAT : ℝ)^2)))| ≤ 4 := by
  intro secondNat thirdNat
  have hA := neg_second_floor_slack_bounds s
  have hB := neg_third_floor_slack_bounds s
  have hC := neg_third_exact_bridge_bounds hs
  rw [abs_le]
  constructor <;> nlinarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2]

private theorem neg_kernel_floor_slack {s : Nat} (hs : s ≤ WEXP_RANGE_OFFSET) :
    let secondNat := (s * s) / (2 * WAD_NAT)
    let thirdNat := (secondNat * s) / (3 * WAD_NAT)
    let x : ℝ := -(s : ℝ) / WAD_NAT
    let P : ℝ := 1 + x + x^2 / 2 + x^3 / 6
    let k : ℝ := (((WAD_NAT : Int) - s + (secondNat : Int) - (thirdNat : Int) : Int) : ℝ) / WAD_NAT
    |k - P| ≤ 4 / (WAD_NAT : ℝ) := by
  intro secondNat thirdNat x P k
  have hWpos : (0 : ℝ) < (WAD_NAT : ℝ) := by norm_num [WAD_NAT]
  have hWne : (WAD_NAT : ℝ) ≠ 0 := ne_of_gt hWpos
  have hinner := neg_kernel_inner_floor_slack (s := s) hs
  have hdiff : k - P = (((secondNat : ℝ) - (s : ℝ)^2 / (2 * (WAD_NAT : ℝ)) -
        ((thirdNat : ℝ) - (s : ℝ)^3 / (6 * (WAD_NAT : ℝ)^2))) / (WAD_NAT : ℝ)) := by
    dsimp [k, P, x]
    norm_num [Int.cast_sub, Int.cast_add, Int.cast_natCast]
    field_simp [hWne]
    ring
  rw [hdiff, abs_div, abs_of_pos hWpos]
  exact div_le_div_of_nonneg_right hinner (le_of_lt hWpos)

private theorem wExpSignedCubicKernel_real_error_neg_nat {s : Nat}
    (hs : s ≤ WEXP_RANGE_OFFSET) :
    |((wExpSignedCubicKernel (-(s : Int)) : ℝ) / WAD_NAT) -
        Real.exp (((-(s : Int) : Int) : ℝ) / WAD_NAT)|
      ≤ 4 / (WAD_NAT : ℝ) + (((-(s : Int) : Int) : ℝ) / WAD_NAT)^4 * (5 / 96) := by
  let secondNat := (s * s) / (2 * WAD_NAT)
  let thirdNat := (secondNat * s) / (3 * WAD_NAT)
  let x : ℝ := -(s : ℝ) / WAD_NAT
  let P : ℝ := 1 + x + x^2 / 2 + x^3 / 6
  let k : ℝ := (((WAD_NAT : Int) - s + (secondNat : Int) - (thirdNat : Int) : Int) : ℝ) / WAD_NAT
  have hkernel : wExpSignedCubicKernel (-(s : Int)) =
      (WAD_NAT : Int) - s + (secondNat : Int) - (thirdNat : Int) := by
    simpa [secondNat, thirdNat] using wExpSignedCubicKernel_neg_eq s
  have hfloor : |k - P| ≤ 4 / (WAD_NAT : ℝ) := by
    simpa [secondNat, thirdNat, x, P, k] using neg_kernel_floor_slack (s := s) hs
  have hWpos : (0 : ℝ) < (WAD_NAT : ℝ) := by norm_num [WAD_NAT]
  have hsR : (s : ℝ) ≤ WEXP_RANGE_OFFSET := by exact_mod_cast hs
  have hoff : (WEXP_RANGE_OFFSET : ℝ) < WAD_NAT := by norm_num [WEXP_RANGE_OFFSET, WAD_NAT]
  have hx_abs_le : |x| ≤ 1 := by
    have hs_nonneg : (0 : ℝ) ≤ s := by positivity
    have hs_le_W : (s : ℝ) ≤ WAD_NAT := le_trans hsR (le_of_lt hoff)
    dsimp [x]
    rw [abs_div, abs_neg, abs_of_nonneg hs_nonneg, abs_of_pos hWpos]
    rw [div_le_one hWpos]
    exact hs_le_W
  have hx_nonpos : x ≤ 0 := by
    dsimp [x]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (le_of_lt hWpos)
  have hx_abs_pow : |x|^4 = x^4 := by
    rw [abs_of_nonpos hx_nonpos]
    ring
  have han : |P - Real.exp x| ≤ x^4 * (5 / 96) := by
    have h := cubic_real_error_abs (x := x) hx_abs_le
    rw [hx_abs_pow] at h
    rw [abs_sub_comm]
    simpa [P] using h
  have htri : |k - Real.exp x| ≤ 4 / (WAD_NAT : ℝ) + x^4 * (5 / 96) := by
    calc
      |k - Real.exp x| ≤ |k - P| + |P - Real.exp x| := abs_sub_le k P (Real.exp x)
      _ ≤ 4 / (WAD_NAT : ℝ) + x^4 * (5 / 96) := add_le_add hfloor han
  rw [hkernel]
  simpa [k, x, secondNat, thirdNat] using htri

theorem wExpSignedCubicKernel_real_error_neg {r : Int}
    (hr0 : -(WEXP_RANGE_OFFSET : Int) ≤ r) (hr1 : r ≤ 0) :
    |((wExpSignedCubicKernel r : ℝ) / WAD_NAT) - Real.exp ((r:ℝ)/WAD_NAT)|
      ≤ 4 / (WAD_NAT : ℝ) + ((r:ℝ)/WAD_NAT)^4 * (5 / 96) := by
  let s := (-r).toNat
  have hs_cast : (s : Int) = -r := by
    exact Int.toNat_of_nonneg (neg_nonneg.mpr hr1)
  have hr_eq : r = -(s : Int) := by omega
  have hs_le : s ≤ WEXP_RANGE_OFFSET := by omega
  rw [hr_eq]
  exact wExpSignedCubicKernel_real_error_neg_nat (s := s) hs_le

/-- Combined `Real.exp` error bound for the signed cubic kernel across the full
range-reduction residual interval `-WEXP_RANGE_OFFSET ≤ r ≤ WEXP_LN2`. -/
theorem wExpSignedCubicKernel_real_error {r : Int}
    (hr0 : -(WEXP_RANGE_OFFSET : Int) ≤ r) (hr1 : r ≤ (WEXP_LN2 : Int)) :
    |((wExpSignedCubicKernel r : ℝ) / WAD_NAT) - Real.exp ((r:ℝ)/WAD_NAT)|
      ≤ 4 / (WAD_NAT : ℝ) + ((r:ℝ)/WAD_NAT)^4 * (5 / 96) := by
  rcases le_or_gt 0 r with h | h
  · have hnonneg := wExpSignedCubicKernel_real_error_nonneg (r := r) h hr1
    calc
      |((wExpSignedCubicKernel r : ℝ) / WAD_NAT) - Real.exp ((r:ℝ)/WAD_NAT)|
          ≤ 3 / (WAD_NAT : ℝ) + ((r:ℝ)/WAD_NAT)^4 * (5 / 96) := hnonneg
      _ ≤ 4 / (WAD_NAT : ℝ) + ((r:ℝ)/WAD_NAT)^4 * (5 / 96) := by
        have hWpos : (0 : ℝ) < (WAD_NAT : ℝ) := by norm_num [WAD_NAT]
        have hconst : (3 : ℝ) / WAD_NAT ≤ 4 / WAD_NAT := by
          exact div_le_div_of_nonneg_right (by norm_num) (le_of_lt hWpos)
        exact add_le_add_right hconst (((r:ℝ)/WAD_NAT)^4 * (5 / 96))
  · exact wExpSignedCubicKernel_real_error_neg hr0 (le_of_lt h)

/-- `wExpRangeR` is exactly the signed residual left by `wExpRangeQ`. -/
theorem wExpRangeReduction_exact (xAbs : Nat) :
    Int.ofNat (wExpRangeQ xAbs * WEXP_LN2) + wExpRangeR xAbs =
      Int.ofNat xAbs := by
  simp [wExpRangeR]

private theorem WEXP_LN2_pos : 0 < WEXP_LN2 := by
  decide

private theorem WEXP_RANGE_OFFSET_lt_LN2 : WEXP_RANGE_OFFSET < WEXP_LN2 := by
  decide

/-- `wExpRangeR` is the Euclidean remainder of the offset input, shifted back
by the range-reduction offset. -/
theorem wExpRangeR_eq_mod_sub_offset (xAbs : Nat) :
    wExpRangeR xAbs =
      Int.ofNat ((xAbs + WEXP_RANGE_OFFSET) % WEXP_LN2) -
        Int.ofNat WEXP_RANGE_OFFSET := by
  have hdivmodNat :
      ((xAbs + WEXP_RANGE_OFFSET) / WEXP_LN2) * WEXP_LN2 +
          (xAbs + WEXP_RANGE_OFFSET) % WEXP_LN2 =
        xAbs + WEXP_RANGE_OFFSET := by
    exact Nat.div_add_mod' (xAbs + WEXP_RANGE_OFFSET) WEXP_LN2
  have hdivmodInt :
      ((((xAbs + WEXP_RANGE_OFFSET) / WEXP_LN2) * WEXP_LN2 : Nat) : Int) +
          (((xAbs + WEXP_RANGE_OFFSET) % WEXP_LN2 : Nat) : Int) =
        (xAbs : Int) + (WEXP_RANGE_OFFSET : Int) := by
    rw [← Int.natCast_add, hdivmodNat, Int.natCast_add]
  unfold wExpRangeR wExpRangeQ
  change (xAbs : Int) -
      ((((xAbs + WEXP_RANGE_OFFSET) / WEXP_LN2) * WEXP_LN2 : Nat) : Int) =
    (((xAbs + WEXP_RANGE_OFFSET) % WEXP_LN2 : Nat) : Int) -
      ((WEXP_RANGE_OFFSET : Nat) : Int)
  omega

/-- Lower bound for the TickLib range-reduction residual. -/
theorem wExpRangeR_lower_bound (xAbs : Nat) :
    -Int.ofNat WEXP_RANGE_OFFSET ≤ wExpRangeR xAbs := by
  rw [wExpRangeR_eq_mod_sub_offset]
  have hnonneg : (0 : Int) ≤ Int.ofNat ((xAbs + WEXP_RANGE_OFFSET) % WEXP_LN2) := by
    exact Int.natCast_nonneg _
  omega

/-- Upper bound for the TickLib range-reduction residual. -/
theorem wExpRangeR_upper_bound (xAbs : Nat) :
    wExpRangeR xAbs < Int.ofNat (WEXP_LN2 - WEXP_RANGE_OFFSET) := by
  rw [wExpRangeR_eq_mod_sub_offset]
  change (((xAbs + WEXP_RANGE_OFFSET) % WEXP_LN2 : Nat) : Int) -
      ((WEXP_RANGE_OFFSET : Nat) : Int) <
    ((WEXP_LN2 - WEXP_RANGE_OFFSET : Nat) : Int)
  have hmod_lt_nat : (xAbs + WEXP_RANGE_OFFSET) % WEXP_LN2 < WEXP_LN2 :=
    Nat.mod_lt _ WEXP_LN2_pos
  have hmod_lt_int :
      (((xAbs + WEXP_RANGE_OFFSET) % WEXP_LN2 : Nat) : Int) <
        ((WEXP_LN2 : Nat) : Int) := by
    exact Int.ofNat_lt.mpr hmod_lt_nat
  have hoff_le : WEXP_RANGE_OFFSET ≤ WEXP_LN2 := Nat.le_of_lt WEXP_RANGE_OFFSET_lt_LN2
  rw [Int.natCast_sub hoff_le]
  omega

/-- Tight interval for the TickLib range-reduction residual. -/
theorem wExpRangeR_bounds (xAbs : Nat) :
    -Int.ofNat WEXP_RANGE_OFFSET ≤ wExpRangeR xAbs ∧
      wExpRangeR xAbs < Int.ofNat (WEXP_LN2 - WEXP_RANGE_OFFSET) :=
  ⟨wExpRangeR_lower_bound xAbs, wExpRangeR_upper_bound xAbs⟩

private theorem WEXP_RANGE_OFFSET_le_WAD : WEXP_RANGE_OFFSET ≤ WAD_NAT := by
  norm_num [WEXP_RANGE_OFFSET, WAD_NAT]

private theorem WEXP_RANGE_OFFSET_lt_WAD : WEXP_RANGE_OFFSET < WAD_NAT := by
  norm_num [WEXP_RANGE_OFFSET, WAD_NAT]

private theorem WEXP_RANGE_OFFSET_le_three_WAD : WEXP_RANGE_OFFSET ≤ 3 * WAD_NAT := by
  exact Nat.le_trans WEXP_RANGE_OFFSET_le_WAD (Nat.le_mul_of_pos_left WAD_NAT (by decide))

set_option maxRecDepth 100000

private theorem wExpSignedCubicKernel_neg_nonneg_of_le_offset {s : Nat}
    (hs_le : s ≤ WEXP_RANGE_OFFSET) :
    0 ≤ wExpSignedCubicKernel (-(s : Int)) := by
  have hs_le_WAD : s ≤ WAD_NAT :=
    Nat.le_trans hs_le WEXP_RANGE_OFFSET_le_WAD
  have hs_le_3WAD : s ≤ 3 * WAD_NAT :=
    Nat.le_trans hs_le WEXP_RANGE_OFFSET_le_three_WAD
  let secondNat := (s * s) / (2 * WAD_NAT)
  let thirdNat := (secondNat * s) / (3 * WAD_NAT)
  have hthird_le_second : thirdNat ≤ secondNat := by
    dsimp [thirdNat]
    have hmul : secondNat * s ≤ (3 * WAD_NAT) * secondNat := by
      calc
        secondNat * s ≤ secondNat * (3 * WAD_NAT) :=
          Nat.mul_le_mul_left secondNat hs_le_3WAD
        _ = (3 * WAD_NAT) * secondNat := Nat.mul_comm secondNat (3 * WAD_NAT)
    exact Nat.div_le_of_le_mul hmul
  have hkernel := wExpSignedCubicKernel_neg_eq s
  rw [hkernel]
  change 0 ≤ (WAD_NAT : Int) - (s : Int) + (secondNat : Int) - (thirdNat : Int)
  have hbase : 0 ≤ (WAD_NAT : Int) - (s : Int) := by
    exact sub_nonneg.mpr (by exact_mod_cast hs_le_WAD)
  have htail : 0 ≤ (secondNat : Int) - (thirdNat : Int) := by
    exact sub_nonneg.mpr (by exact_mod_cast hthird_le_second)
  have hsum : 0 ≤ ((WAD_NAT : Int) - (s : Int)) +
      ((secondNat : Int) - (thirdNat : Int)) :=
    add_nonneg hbase htail
  simpa [sub_eq_add_neg, add_assoc] using hsum

/-- The signed cubic kernel is non-negative throughout the TickLib
range-reduction residual interval. -/
theorem wExpSignedCubicKernel_nonneg_of_range {r : Int}
    (hr0 : -(WEXP_RANGE_OFFSET : Int) ≤ r) (_hr1 : r ≤ (WEXP_LN2 : Int)) :
    0 ≤ wExpSignedCubicKernel r := by
  rcases le_or_gt 0 r with hnonneg | hneg
  · rw [wExpSignedCubicKernel_eq_natKernel_of_nonneg (r := r) hnonneg]
    exact Int.natCast_nonneg _
  · let s := (-r).toNat
    have hs_cast : (s : Int) = -r := by
      exact Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hneg))
    have hr_eq : r = -(s : Int) := by omega
    have hs_le : s ≤ WEXP_RANGE_OFFSET := by omega
    rw [hr_eq]
    exact wExpSignedCubicKernel_neg_nonneg_of_le_offset (s := s) hs_le

private theorem wExpSignedCubicKernel_neg_pos_of_le_offset {s : Nat}
    (hs_le : s ≤ WEXP_RANGE_OFFSET) :
    0 < wExpSignedCubicKernel (-(s : Int)) := by
  have hs_lt_WAD : s < WAD_NAT :=
    Nat.lt_of_le_of_lt hs_le WEXP_RANGE_OFFSET_lt_WAD
  have hs_le_3WAD : s ≤ 3 * WAD_NAT :=
    Nat.le_trans hs_le WEXP_RANGE_OFFSET_le_three_WAD
  let secondNat := (s * s) / (2 * WAD_NAT)
  let thirdNat := (secondNat * s) / (3 * WAD_NAT)
  have hthird_le_second : thirdNat ≤ secondNat := by
    dsimp [thirdNat]
    have hmul : secondNat * s ≤ (3 * WAD_NAT) * secondNat := by
      calc
        secondNat * s ≤ secondNat * (3 * WAD_NAT) :=
          Nat.mul_le_mul_left secondNat hs_le_3WAD
        _ = (3 * WAD_NAT) * secondNat := Nat.mul_comm secondNat (3 * WAD_NAT)
    exact Nat.div_le_of_le_mul hmul
  have hkernel := wExpSignedCubicKernel_neg_eq s
  rw [hkernel]
  change 0 < (WAD_NAT : Int) - (s : Int) + (secondNat : Int) - (thirdNat : Int)
  have hbase : 0 < (WAD_NAT : Int) - (s : Int) := by
    exact sub_pos.mpr (by exact_mod_cast hs_lt_WAD)
  have htail : 0 ≤ (secondNat : Int) - (thirdNat : Int) := by
    exact sub_nonneg.mpr (by exact_mod_cast hthird_le_second)
  have hsum : 0 < ((WAD_NAT : Int) - (s : Int)) +
      ((secondNat : Int) - (thirdNat : Int)) :=
    add_pos_of_pos_of_nonneg hbase htail
  simpa [sub_eq_add_neg, add_assoc] using hsum

/-- The signed cubic kernel is strictly positive throughout the TickLib
range-reduction residual interval. -/
theorem wExpSignedCubicKernel_pos_of_range {r : Int}
    (hr0 : -(WEXP_RANGE_OFFSET : Int) ≤ r) (_hr1 : r ≤ (WEXP_LN2 : Int)) :
    0 < wExpSignedCubicKernel r := by
  rcases le_or_gt 0 r with hnonneg | hneg
  · rw [wExpSignedCubicKernel_eq_natKernel_of_nonneg (r := r) hnonneg]
    unfold wExpCubicKernel
    let secondNat := (r.toNat * r.toNat) / (2 * WAD_NAT)
    let thirdNat := (secondNat * r.toNat) / (3 * WAD_NAT)
    have hbase : 0 < WAD_NAT + r.toNat := Nat.add_pos_left WAD_NAT_pos _
    have hbase_second : 0 < WAD_NAT + r.toNat + secondNat :=
      Nat.lt_of_lt_of_le hbase (Nat.le_add_right _ _)
    have hkernel_nat : 0 < WAD_NAT + r.toNat + secondNat + thirdNat :=
      Nat.lt_of_lt_of_le hbase_second (Nat.le_add_right _ _)
    exact_mod_cast hkernel_nat
  · let s := (-r).toNat
    have hs_cast : (s : Int) = -r := by
      exact Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hneg))
    have hr_eq : r = -(s : Int) := by omega
    have hs_le : s ≤ WEXP_RANGE_OFFSET := by omega
    rw [hr_eq]
    exact wExpSignedCubicKernel_neg_pos_of_le_offset (s := s) hs_le

/-- The scaled denominator used by the negative `tickWExpReference` branch is
strictly positive. -/
theorem tickWExpReference_neg_scaled_pos {x : Int} (_hx : x < 0) :
    0 <
      Int.toNat (wExpSignedCubicKernel (wExpRangeR (wExpAbsInput x))) *
        2 ^ wExpRangeQ (wExpAbsInput x) := by
  let xAbs := wExpAbsInput x
  let q := wExpRangeQ xAbs
  let r := wExpRangeR xAbs
  have hrange := wExpRangeR_bounds xAbs
  have hr0 : -(WEXP_RANGE_OFFSET : Int) ≤ r := by
    simpa [r] using hrange.1
  have hr_upper_le : Int.ofNat (WEXP_LN2 - WEXP_RANGE_OFFSET) ≤ (WEXP_LN2 : Int) := by
    exact Int.ofNat_le.mpr (Nat.sub_le WEXP_LN2 WEXP_RANGE_OFFSET)
  have hr1 : r ≤ (WEXP_LN2 : Int) :=
    le_trans (le_of_lt (by simpa [r] using hrange.2)) hr_upper_le
  have hkernel_pos : 0 < wExpSignedCubicKernel r :=
    wExpSignedCubicKernel_pos_of_range (r := r) hr0 hr1
  have hkernel_toNat_pos : 0 < Int.toNat (wExpSignedCubicKernel r) := by
    have hcast : ((Int.toNat (wExpSignedCubicKernel r) : Nat) : Int) =
        wExpSignedCubicKernel r :=
      Int.toNat_of_nonneg (le_of_lt hkernel_pos)
    by_contra hzero
    have hnat_zero : Int.toNat (wExpSignedCubicKernel r) = 0 := Nat.eq_zero_of_not_pos hzero
    have : (wExpSignedCubicKernel r : Int) = 0 := by
      simpa [hnat_zero] using hcast.symm
    omega
  have hpow_pos : 0 < 2 ^ q := pow_pos (by decide) q
  simpa [xAbs, q, r] using Nat.mul_pos hkernel_toNat_pos hpow_pos

private theorem tickWExpReference_real_nonneg_eq_kernel_mul_two_pow {x : Int} (hx : 0 ≤ x) :
    ((tickWExpReference x : ℝ) / (WAD_NAT : ℝ)) =
      ((wExpSignedCubicKernel (wExpRangeR (wExpAbsInput x)) : ℝ) / (WAD_NAT : ℝ)) *
        (2 : ℝ) ^ wExpRangeQ (wExpAbsInput x) := by
  let xAbs := wExpAbsInput x
  let q := wExpRangeQ xAbs
  let r := wExpRangeR xAbs
  have hx_not_neg : ¬ x < 0 := by omega
  have hrange := wExpRangeR_bounds xAbs
  have hr0 : -(WEXP_RANGE_OFFSET : Int) ≤ r := by
    simpa [r] using hrange.1
  have hr_upper_le : Int.ofNat (WEXP_LN2 - WEXP_RANGE_OFFSET) ≤ (WEXP_LN2 : Int) := by
    exact Int.ofNat_le.mpr (Nat.sub_le WEXP_LN2 WEXP_RANGE_OFFSET)
  have hr1 : r ≤ (WEXP_LN2 : Int) :=
    le_trans (le_of_lt (by simpa [r] using hrange.2)) hr_upper_le
  have hkernel_nonneg : 0 ≤ wExpSignedCubicKernel r :=
    wExpSignedCubicKernel_nonneg_of_range (r := r) hr0 hr1
  have hkernel_cast :
      ((Int.toNat (wExpSignedCubicKernel r) : Nat) : ℝ) =
        (wExpSignedCubicKernel r : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hkernel_nonneg
  dsimp [tickWExpReference]
  rw [if_neg hx_not_neg]
  change (((Int.toNat (wExpSignedCubicKernel r) * 2 ^ q : Nat) : ℝ) /
      (WAD_NAT : ℝ)) =
    ((wExpSignedCubicKernel r : ℝ) / (WAD_NAT : ℝ)) * (2 : ℝ) ^ q
  rw [Nat.cast_mul, Nat.cast_pow, hkernel_cast]
  ring

private theorem real_abs_mul_sub_mul_le
    {A Ahat B Bhat epsA epsB : ℝ}
    (hB : 0 ≤ B) (hAhat : 0 ≤ Ahat)
    (hEA : |A - Ahat| ≤ epsA) (hEB : |Bhat - B| ≤ epsB) :
    |A * B - Ahat * Bhat| ≤ B * epsA + Ahat * epsB := by
  have hEB' : |B - Bhat| ≤ epsB := by
    simpa [abs_sub_comm] using hEB
  calc
    |A * B - Ahat * Bhat|
        = |(A - Ahat) * B + Ahat * (B - Bhat)| := by ring_nf
    _ ≤ |(A - Ahat) * B| + |Ahat * (B - Bhat)| := abs_add_le _ _
    _ = |A - Ahat| * B + Ahat * |B - Bhat| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hB, abs_of_nonneg hAhat]
    _ ≤ epsA * B + Ahat * epsB :=
      add_le_add
        (mul_le_mul_of_nonneg_right hEA hB)
        (mul_le_mul_of_nonneg_left hEB' hAhat)
    _ = B * epsA + Ahat * epsB := by ring

/-- Capstone real-error bound for `tickWExpReference` on the non-negative input
branch. This composes the residual cubic-kernel error with the `ln 2`
power approximation after TickLib's exact range decomposition. -/
theorem tickWExpReference_real_error_nonneg {x : Int} (hx : 0 ≤ x) :
    |((tickWExpReference x : ℝ) / (WAD_NAT : ℝ))
        - Real.exp ((wExpAbsInput x : ℝ) / (WAD_NAT : ℝ))|
      ≤ (2 : ℝ) ^ wExpRangeQ (wExpAbsInput x)
          * (4 / (WAD_NAT : ℝ)
              + ((wExpRangeR (wExpAbsInput x) : ℝ) / (WAD_NAT : ℝ)) ^ 4 * (5 / 96))
        + Real.exp ((wExpRangeR (wExpAbsInput x) : ℝ) / (WAD_NAT : ℝ))
          * ((wExpRangeQ (wExpAbsInput x) : ℝ)
              * (2001 / 1000) ^ wExpRangeQ (wExpAbsInput x) * (2 / 10 ^ 9)) := by
  let xAbs := wExpAbsInput x
  let q := wExpRangeQ xAbs
  let r := wExpRangeR xAbs
  let A : ℝ := (wExpSignedCubicKernel r : ℝ) / (WAD_NAT : ℝ)
  let Ahat : ℝ := Real.exp ((r : ℝ) / (WAD_NAT : ℝ))
  let B : ℝ := (2 : ℝ) ^ q
  let Bhat : ℝ := Real.exp ((WEXP_LN2 : ℝ) / (WAD_NAT : ℝ)) ^ q
  let epsK : ℝ := 4 / (WAD_NAT : ℝ) + ((r : ℝ) / (WAD_NAT : ℝ)) ^ 4 * (5 / 96)
  let epsPow : ℝ := (q : ℝ) * (2001 / 1000) ^ q * (2 / 10 ^ 9)
  have hrange := wExpRangeR_bounds xAbs
  have hr0 : -(WEXP_RANGE_OFFSET : Int) ≤ r := by
    simpa [r] using hrange.1
  have hr_upper_le : Int.ofNat (WEXP_LN2 - WEXP_RANGE_OFFSET) ≤ (WEXP_LN2 : Int) := by
    exact Int.ofNat_le.mpr (Nat.sub_le WEXP_LN2 WEXP_RANGE_OFFSET)
  have hr1 : r ≤ (WEXP_LN2 : Int) :=
    le_trans (le_of_lt (by simpa [r] using hrange.2)) hr_upper_le
  have hRef :
      ((tickWExpReference x : ℝ) / (WAD_NAT : ℝ)) = A * B := by
    simpa [A, B, r, q, xAbs] using tickWExpReference_real_nonneg_eq_kernel_mul_two_pow hx
  have hExp :
      Real.exp ((xAbs : ℝ) / (WAD_NAT : ℝ)) = Ahat * Bhat := by
    simpa [Ahat, Bhat, r, q, xAbs] using tickWExp_exp_decomp xAbs
  have hKernelErr : |A - Ahat| ≤ epsK := by
    simpa [A, Ahat, epsK, r] using
      wExpSignedCubicKernel_real_error (r := r) hr0 hr1
  have hPowErr : |Bhat - B| ≤ epsPow := by
    simpa [Bhat, B, epsPow, q] using wExpLn2_pow_approx_two_pow q
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact pow_nonneg (by norm_num) q
  have hAhat_nonneg : 0 ≤ Ahat := by
    dsimp [Ahat]
    exact Real.exp_nonneg _
  have hprod :
      |A * B - Ahat * Bhat| ≤ B * epsK + Ahat * epsPow :=
    real_abs_mul_sub_mul_le hB_nonneg hAhat_nonneg hKernelErr hPowErr
  rw [hRef, hExp]
  simpa [A, Ahat, B, Bhat, epsK, epsPow, q, r, xAbs] using hprod

private theorem WEXP_ONE_E36_eq_WAD_mul_WAD :
    WEXP_ONE_E36 = WAD_NAT * WAD_NAT := by
  norm_num [WEXP_ONE_E36, WAD_NAT]

private theorem real_abs_inv_sub_inv_le {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    |1 / u - 1 / v| ≤ |u - v| / (u * v) := by
  have hune : u ≠ 0 := ne_of_gt hu
  have hvne : v ≠ 0 := ne_of_gt hv
  have huv : 0 < u * v := mul_pos hu hv
  calc
    |1 / u - 1 / v| = |(v - u) / (u * v)| := by
      field_simp [hune, hvne]
    _ = |v - u| / |u * v| := by rw [abs_div]
    _ = |u - v| / (u * v) := by rw [abs_sub_comm, abs_of_pos huv]
    _ ≤ |u - v| / (u * v) := le_rfl

private theorem real_nat_div_floor_abs_error_div_wad (n d : Nat) (hd : 0 < d) :
    |(((n / d : Nat) : ℝ) / (WAD_NAT : ℝ) -
        ((n : ℝ) / (d : ℝ)) / (WAD_NAT : ℝ))|
      ≤ 1 / (WAD_NAT : ℝ) := by
  let a : ℝ := ((n / d : Nat) : ℝ)
  let b : ℝ := (n : ℝ) / (d : ℝ)
  let w : ℝ := (WAD_NAT : ℝ)
  have hw_pos : 0 < w := by norm_num [w, WAD_NAT]
  have hd_real_pos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hfloor_le : a ≤ b := by
    dsimp [a, b]
    exact Nat.cast_div_le
  have hlt_nat : n < d * (n / d + 1) := Nat.lt_mul_div_succ n hd
  have hlt_real : (n : ℝ) < (d : ℝ) * (((n / d : Nat) : ℝ) + 1) := by
    exact_mod_cast hlt_nat
  have hfloor_lt_add_one : b < a + 1 := by
    dsimp [a, b]
    rw [div_lt_iff₀ hd_real_pos]
    simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using hlt_real
  have hdiff_le_one : b - a ≤ 1 := by linarith
  calc
    |a / w - b / w| = |(a - b) / w| := by ring_nf
    _ = |a - b| / |w| := by rw [abs_div]
    _ = (b - a) / w := by
      rw [abs_of_nonpos (sub_nonpos.mpr hfloor_le), abs_of_pos hw_pos]
      ring
    _ ≤ 1 / w := div_le_div_of_nonneg_right hdiff_le_one (le_of_lt hw_pos)

private theorem wExpAbsInput_ofNat (n : Nat) :
    wExpAbsInput (n : Int) = n := by
  simp [wExpAbsInput]

private theorem tickWExpReference_ofNat_eq_scaled (n : Nat) :
    tickWExpReference (n : Int) =
      Int.toNat (wExpSignedCubicKernel (wExpRangeR n)) * 2 ^ wExpRangeQ n := by
  simp [tickWExpReference, wExpAbsInput]

private theorem WEXP_ONE_E36_real_div_scaled_div_WAD_eq_inv
    {scaled : Nat} (hscaled_pos : 0 < scaled) :
    ((WEXP_ONE_E36 : ℝ) / (scaled : ℝ)) / (WAD_NAT : ℝ) =
      1 / (((scaled : ℝ) / (WAD_NAT : ℝ))) := by
  have hscaled_ne : (scaled : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hscaled_pos)
  have hwad_ne : (WAD_NAT : ℝ) ≠ 0 := by norm_num [WAD_NAT]
  have hconst : (WEXP_ONE_E36 : ℝ) = (WAD_NAT : ℝ) * (WAD_NAT : ℝ) := by
    exact_mod_cast WEXP_ONE_E36_eq_WAD_mul_WAD
  rw [hconst]
  field_simp [hscaled_ne, hwad_ne]

 private theorem tickWExpReference_neg_nonneg_error {x : Int} (_hx : x < 0) :
    |((((Int.toNat (wExpSignedCubicKernel (wExpRangeR (wExpAbsInput x))) *
        2 ^ wExpRangeQ (wExpAbsInput x) : Nat) : ℝ) / (WAD_NAT : ℝ))
        - Real.exp ((wExpAbsInput x : ℝ) / (WAD_NAT : ℝ)))|
      ≤ (2 : ℝ) ^ wExpRangeQ (wExpAbsInput x)
          * (4 / (WAD_NAT : ℝ)
              + ((wExpRangeR (wExpAbsInput x) : ℝ) / (WAD_NAT : ℝ)) ^ 4 * (5 / 96))
        + Real.exp ((wExpRangeR (wExpAbsInput x) : ℝ) / (WAD_NAT : ℝ))
          * ((wExpRangeQ (wExpAbsInput x) : ℝ)
              * (2001 / 1000) ^ wExpRangeQ (wExpAbsInput x) * (2 / 10 ^ 9)) := by
  let xAbs := wExpAbsInput x
  have hnonneg : 0 ≤ (xAbs : Int) := Int.natCast_nonneg _
  have h := tickWExpReference_real_error_nonneg (x := (xAbs : Int)) hnonneg
  simpa [xAbs, wExpAbsInput_ofNat, tickWExpReference_ofNat_eq_scaled] using h

private theorem tickWExpReference_neg_floor_error {x : Int} (hx : x < 0) :
    |((tickWExpReference x : ℝ) / (WAD_NAT : ℝ)) -
        (1 / (((Int.toNat (wExpSignedCubicKernel (wExpRangeR (wExpAbsInput x))) *
          2 ^ wExpRangeQ (wExpAbsInput x) : Nat) : ℝ) / (WAD_NAT : ℝ)))|
      ≤ 1 / (WAD_NAT : ℝ) := by
  let scaled : Nat :=
    Int.toNat (wExpSignedCubicKernel (wExpRangeR (wExpAbsInput x))) *
      2 ^ wExpRangeQ (wExpAbsInput x)
  have hscaled_pos : 0 < scaled := by
    simpa [scaled] using tickWExpReference_neg_scaled_pos (x := x) hx
  have hfloor' := real_nat_div_floor_abs_error_div_wad WEXP_ONE_E36 scaled hscaled_pos
  have hrecip := WEXP_ONE_E36_real_div_scaled_div_WAD_eq_inv hscaled_pos
  have hx_branch : tickWExpReference x = WEXP_ONE_E36 / scaled := by
    dsimp [tickWExpReference]
    rw [if_pos hx]
  rw [hx_branch, ← hrecip]
  simpa [scaled] using hfloor'

private theorem tickWExpReference_neg_recip_error {x : Int} (hx : x < 0) :
    |(1 / (((Int.toNat (wExpSignedCubicKernel (wExpRangeR (wExpAbsInput x))) *
          2 ^ wExpRangeQ (wExpAbsInput x) : Nat) : ℝ) / (WAD_NAT : ℝ)))
        - Real.exp (-((wExpAbsInput x : ℝ) / (WAD_NAT : ℝ)))|
      ≤ ((2 : ℝ) ^ wExpRangeQ (wExpAbsInput x)
            * (4 / (WAD_NAT : ℝ)
                + ((wExpRangeR (wExpAbsInput x) : ℝ) / (WAD_NAT : ℝ)) ^ 4 * (5 / 96))
          + Real.exp ((wExpRangeR (wExpAbsInput x) : ℝ) / (WAD_NAT : ℝ))
            * ((wExpRangeQ (wExpAbsInput x) : ℝ)
                * (2001 / 1000) ^ wExpRangeQ (wExpAbsInput x) * (2 / 10 ^ 9)))
          /
          ((((Int.toNat (wExpSignedCubicKernel (wExpRangeR (wExpAbsInput x))) *
              2 ^ wExpRangeQ (wExpAbsInput x) : Nat) : ℝ) / (WAD_NAT : ℝ))
            * Real.exp ((wExpAbsInput x : ℝ) / (WAD_NAT : ℝ))) := by
  let scaled : Nat :=
    Int.toNat (wExpSignedCubicKernel (wExpRangeR (wExpAbsInput x))) *
      2 ^ wExpRangeQ (wExpAbsInput x)
  let u : ℝ := (scaled : ℝ) / (WAD_NAT : ℝ)
  let v : ℝ := Real.exp ((wExpAbsInput x : ℝ) / (WAD_NAT : ℝ))
  have hscaled_pos : 0 < scaled := by
    simpa [scaled] using tickWExpReference_neg_scaled_pos (x := x) hx
  have hu_pos : 0 < u := div_pos (by exact_mod_cast hscaled_pos) (by norm_num [WAD_NAT])
  have hv_pos : 0 < v := by dsimp [v]; exact Real.exp_pos _
  have hbrick := tickWExpReference_neg_nonneg_error (x := x) hx
  have hExpNeg : Real.exp (-((wExpAbsInput x : ℝ) / (WAD_NAT : ℝ))) = 1 / v := by
    dsimp [v]
    rw [Real.exp_neg]
    simp [one_div]
  rw [hExpNeg]
  simpa [u, v, scaled] using
    le_trans (real_abs_inv_sub_inv_le hu_pos hv_pos)
      (div_le_div_of_nonneg_right (by simpa [u, v, scaled] using hbrick)
        (le_of_lt (mul_pos hu_pos hv_pos)))

/-- Capstone real-error bound for `tickWExpReference` on the negative input
branch. The reciprocal branch contributes one wad-scaled floor unit plus the
nonnegative-branch approximation error propagated through the reciprocal. -/
theorem tickWExpReference_real_error_neg {x : Int} (hx : x < 0) :
    |((tickWExpReference x : ℝ) / (WAD_NAT : ℝ))
        - Real.exp (-((wExpAbsInput x : ℝ) / (WAD_NAT : ℝ)))|
      ≤ 1 / (WAD_NAT : ℝ)
        + ((2 : ℝ) ^ wExpRangeQ (wExpAbsInput x)
            * (4 / (WAD_NAT : ℝ)
                + ((wExpRangeR (wExpAbsInput x) : ℝ) / (WAD_NAT : ℝ)) ^ 4 * (5 / 96))
          + Real.exp ((wExpRangeR (wExpAbsInput x) : ℝ) / (WAD_NAT : ℝ))
            * ((wExpRangeQ (wExpAbsInput x) : ℝ)
                * (2001 / 1000) ^ wExpRangeQ (wExpAbsInput x) * (2 / 10 ^ 9)))
          /
          ((((Int.toNat (wExpSignedCubicKernel (wExpRangeR (wExpAbsInput x))) *
              2 ^ wExpRangeQ (wExpAbsInput x) : Nat) : ℝ) / (WAD_NAT : ℝ))
            * Real.exp ((wExpAbsInput x : ℝ) / (WAD_NAT : ℝ))) := by
  let invScaled : ℝ :=
    1 / (((Int.toNat (wExpSignedCubicKernel (wExpRangeR (wExpAbsInput x))) *
      2 ^ wExpRangeQ (wExpAbsInput x) : Nat) : ℝ) / (WAD_NAT : ℝ))
  have hfloor := tickWExpReference_neg_floor_error (x := x) hx
  have hrecip := tickWExpReference_neg_recip_error (x := x) hx
  calc
    |((tickWExpReference x : ℝ) / (WAD_NAT : ℝ))
        - Real.exp (-((wExpAbsInput x : ℝ) / (WAD_NAT : ℝ)))|
        ≤ |((tickWExpReference x : ℝ) / (WAD_NAT : ℝ)) - invScaled|
          + |invScaled - Real.exp (-((wExpAbsInput x : ℝ) / (WAD_NAT : ℝ)))| := by
      simpa [sub_eq_add_neg, add_assoc] using
        abs_add_le (((tickWExpReference x : ℝ) / (WAD_NAT : ℝ)) - invScaled)
          (invScaled - Real.exp (-((wExpAbsInput x : ℝ) / (WAD_NAT : ℝ))))
    _ ≤ 1 / (WAD_NAT : ℝ)
        + ((2 : ℝ) ^ wExpRangeQ (wExpAbsInput x)
            * (4 / (WAD_NAT : ℝ)
                + ((wExpRangeR (wExpAbsInput x) : ℝ) / (WAD_NAT : ℝ)) ^ 4 * (5 / 96))
          + Real.exp ((wExpRangeR (wExpAbsInput x) : ℝ) / (WAD_NAT : ℝ))
            * ((wExpRangeQ (wExpAbsInput x) : ℝ)
                * (2001 / 1000) ^ wExpRangeQ (wExpAbsInput x) * (2 / 10 ^ 9)))
          /
          ((((Int.toNat (wExpSignedCubicKernel (wExpRangeR (wExpAbsInput x))) *
              2 ^ wExpRangeQ (wExpAbsInput x) : Nat) : ℝ) / (WAD_NAT : ℝ))
            * Real.exp ((wExpAbsInput x : ℝ) / (WAD_NAT : ℝ))) := by
      exact add_le_add (by simpa [invScaled] using hfloor) (by simpa [invScaled] using hrecip)

/-! ## Full-precision mulDiv512 helpers -/

private theorem ceil_mul_div_ge (n d : Nat) (hd : 0 < d) :
    n ≤ ((n + (d - 1)) / d) * d := by
  have hdiv : (n + (d - 1)) / d ≤ (n + (d - 1)) / d := Nat.le_refl _
  have hle := (Nat.div_le_iff_le_mul_add_pred (b := d) (a := n + (d - 1))
    (c := (n + (d - 1)) / d) hd).mp hdiv
  have h : n ≤ d * ((n + (d - 1)) / d) := Nat.le_of_add_le_add_right hle
  simpa [Nat.mul_comm] using h

private theorem ceil_mul_div_le_add_pred (n d : Nat) :
    ((n + (d - 1)) / d) * d ≤ n + (d - 1) := by
  simpa [Nat.mul_comm] using Nat.mul_div_le (n + (d - 1)) d

private theorem nat_ceil_div_antitone_divisor (n c₁ c₂ : Nat)
    (hC : c₁ ≤ c₂)
    (hC₁ : c₁ ≠ 0)
    (hC₂ : c₂ ≠ 0) :
    (n + (c₂ - 1)) / c₂ ≤ (n + (c₁ - 1)) / c₁ := by
  have hC₂Pos : 0 < c₂ := Nat.pos_of_ne_zero hC₂
  have hUpper :
      ((n + (c₂ - 1)) / c₂) * c₂ < n + c₂ := by
    calc
      ((n + (c₂ - 1)) / c₂) * c₂ ≤ n + (c₂ - 1) :=
        ceil_mul_div_le_add_pred n c₂
      _ < n + c₂ := Nat.add_lt_add_left (Nat.sub_lt hC₂Pos (by decide)) _
  have hLower :
      n ≤ ((n + (c₁ - 1)) / c₁) * c₂ := by
    exact Nat.le_trans
      (ceil_mul_div_ge n c₁ (Nat.pos_of_ne_zero hC₁))
      (Nat.mul_le_mul_left _ hC)
  have hLt :
      ((n + (c₂ - 1)) / c₂) * c₂ <
        (((n + (c₁ - 1)) / c₁) + 1) * c₂ := by
    calc
      ((n + (c₂ - 1)) / c₂) * c₂ < n + c₂ := hUpper
      _ ≤ ((n + (c₁ - 1)) / c₁) * c₂ + c₂ := Nat.add_le_add_right hLower _
      _ = (((n + (c₁ - 1)) / c₁) + 1) * c₂ := by
            simp [Nat.right_distrib]
  have hLt' :
      c₂ * ((n + (c₂ - 1)) / c₂) <
        c₂ * (((n + (c₁ - 1)) / c₁) + 1) := by
    simpa [Nat.mul_comm] using hLt
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left hLt')

/-- `mulDiv512Down?` returns the exact full-precision floor quotient when it fits. -/
theorem mulDiv512Down?_some (a b c : Uint256)
    (hC : (c : Nat) ≠ 0)
    (hFit : ((a : Nat) * (b : Nat)) / (c : Nat) ≤ MAX_UINT256) :
    mulDiv512Down? a b c =
      some (Verity.Core.Uint256.ofNat (((a : Nat) * (b : Nat)) / (c : Nat))) := by
  simp [Verity.Stdlib.Math.mulDiv512Down?, hC, Nat.not_lt.mpr hFit]

/-- `mulDiv512Down?` rejects a zero divisor. -/
theorem mulDiv512Down?_none_of_zero_divisor (a b c : Uint256)
    (hC : (c : Nat) = 0) :
    mulDiv512Down? a b c = none := by
  simp [Verity.Stdlib.Math.mulDiv512Down?, hC]

/-- `mulDiv512Down?` rejects a quotient that does not fit in `uint256`. -/
theorem mulDiv512Down?_none_of_overflow (a b c : Uint256)
    (hC : (c : Nat) ≠ 0)
    (hOverflow : MAX_UINT256 < ((a : Nat) * (b : Nat)) / (c : Nat)) :
    mulDiv512Down? a b c = none := by
  simp [Verity.Stdlib.Math.mulDiv512Down?, hC, hOverflow]

/-- The quotient returned by `mulDiv512Down?` is the full-precision natural quotient. -/
theorem mulDiv512Down?_eq_some_iff (a b c out : Uint256) :
    mulDiv512Down? a b c = some out ↔
      (c : Nat) ≠ 0 ∧
      ((a : Nat) * (b : Nat)) / (c : Nat) ≤ MAX_UINT256 ∧
      Verity.Core.Uint256.ofNat (((a : Nat) * (b : Nat)) / (c : Nat)) = out := by
  by_cases hC : (c : Nat) = 0
  · simp [Verity.Stdlib.Math.mulDiv512Down?, hC]
  · by_cases hOverflow : ((a : Nat) * (b : Nat)) / (c : Nat) > MAX_UINT256
    · have hNotFit : ¬((a : Nat) * (b : Nat)) / (c : Nat) ≤ MAX_UINT256 := by
        exact Nat.not_le_of_gt hOverflow
      simp [Verity.Stdlib.Math.mulDiv512Down?, hC, hOverflow, hNotFit]
    · have hFit : ((a : Nat) * (b : Nat)) / (c : Nat) ≤ MAX_UINT256 := Nat.le_of_not_gt hOverflow
      simp [Verity.Stdlib.Math.mulDiv512Down?, hC, hOverflow, hFit]

/-- `mulDiv512Down?` succeeds exactly when the divisor is nonzero and the
full-precision floor quotient fits in `uint256`. -/
theorem mulDiv512Down?_isSome_iff (a b c : Uint256) :
    (mulDiv512Down? a b c).isSome ↔
      (c : Nat) ≠ 0 ∧
      ((a : Nat) * (b : Nat)) / (c : Nat) ≤ MAX_UINT256 := by
  by_cases hC : (c : Nat) = 0
  · simp [Verity.Stdlib.Math.mulDiv512Down?, hC]
  · by_cases hOverflow : ((a : Nat) * (b : Nat)) / (c : Nat) > MAX_UINT256
    · have hNotFit : ¬((a : Nat) * (b : Nat)) / (c : Nat) ≤ MAX_UINT256 := by
        exact Nat.not_le_of_gt hOverflow
      simp [Verity.Stdlib.Math.mulDiv512Down?, hC, hOverflow, hNotFit]
    · have hFit : ((a : Nat) * (b : Nat)) / (c : Nat) ≤ MAX_UINT256 := Nat.le_of_not_gt hOverflow
      simp [Verity.Stdlib.Math.mulDiv512Down?, hC, hOverflow, hFit]

/-- A successful full-precision floor result is below the exact product. -/
theorem mulDiv512Down?_mul_le (a b c out : Uint256)
    (h : mulDiv512Down? a b c = some out) :
    (out : Nat) * (c : Nat) ≤ (a : Nat) * (b : Nat) := by
  rcases (mulDiv512Down?_eq_some_iff a b c out).mp h with ⟨_hC, hFit, hOut⟩
  rw [← hOut]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit)]
  exact Nat.div_mul_le_self ((a : Nat) * (b : Nat)) (c : Nat)

/-- A successful full-precision floor result is the greatest quotient below
the exact product. -/
theorem mulDiv512Down?_lt_succ_mul (a b c out : Uint256)
    (h : mulDiv512Down? a b c = some out) :
    (a : Nat) * (b : Nat) < ((out : Nat) + 1) * (c : Nat) := by
  rcases (mulDiv512Down?_eq_some_iff a b c out).mp h with ⟨hC, hFit, hOut⟩
  rw [← hOut]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit)]
  simpa [Nat.mul_comm] using
    Nat.lt_mul_div_succ ((b : Nat) * (a : Nat)) (Nat.pos_of_ne_zero hC)

/-- A successful full-precision floor result undershoots the exact product by
less than one divisor-width. -/
theorem mulDiv512Down?_mul_lt_add (a b c out : Uint256)
    (h : mulDiv512Down? a b c = some out) :
    (a : Nat) * (b : Nat) < (out : Nat) * (c : Nat) + (c : Nat) := by
  simpa [Nat.right_distrib] using mulDiv512Down?_lt_succ_mul a b c out h

/-- `mulDiv512Down?` rejects exactly zero divisors or overflowing floor quotients. -/
theorem mulDiv512Down?_isNone_iff (a b c : Uint256) :
    (mulDiv512Down? a b c).isNone ↔
      (c : Nat) = 0 ∨
      MAX_UINT256 < ((a : Nat) * (b : Nat)) / (c : Nat) := by
  by_cases hC : (c : Nat) = 0
  · simp [Verity.Stdlib.Math.mulDiv512Down?, hC]
  · by_cases hOverflow : ((a : Nat) * (b : Nat)) / (c : Nat) > MAX_UINT256
    · simp [Verity.Stdlib.Math.mulDiv512Down?, hC, hOverflow]
    · simp [Verity.Stdlib.Math.mulDiv512Down?, hC, hOverflow]

/-- Full-precision floor multiplication is commutative in its numerator operands. -/
theorem mulDiv512Down?_comm (a b c : Uint256) :
    mulDiv512Down? a b c = mulDiv512Down? b a c := by
  simp [Verity.Stdlib.Math.mulDiv512Down?, Nat.mul_comm]

/-- A zero left numerator collapses full-precision floor multiplication to zero. -/
theorem mulDiv512Down?_zero_left (b c : Uint256)
    (hC : (c : Nat) ≠ 0) :
    mulDiv512Down? 0 b c = some 0 := by
  simp [Verity.Stdlib.Math.mulDiv512Down?, hC]

/-- A zero right numerator collapses full-precision floor multiplication to zero. -/
theorem mulDiv512Down?_zero_right (a c : Uint256)
    (hC : (c : Nat) ≠ 0) :
    mulDiv512Down? a 0 c = some 0 := by
  simpa [mulDiv512Down?_comm] using mulDiv512Down?_zero_left a c hC

/-- A successful full-precision floor result is positive once the exact product
reaches at least one divisor-width. -/
theorem mulDiv512Down?_pos (a b c out : Uint256)
    (hLower : (c : Nat) ≤ (a : Nat) * (b : Nat))
    (h : mulDiv512Down? a b c = some out) :
    0 < (out : Nat) := by
  rcases (mulDiv512Down?_eq_some_iff a b c out).mp h with ⟨hC, hFit, hOut⟩
  have hCPos : 0 < (c : Nat) := Nat.pos_of_ne_zero hC
  rw [← hOut]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit)]
  simpa [Nat.div_pos_iff, hCPos] using hLower

/-- Exact full-precision floor cancellation by the right numerator operand. -/
theorem mulDiv512Down?_cancel_right (a c : Uint256)
    (hC : (c : Nat) ≠ 0) :
    mulDiv512Down? a c c = some a := by
  have hCPos : 0 < (c : Nat) := Nat.pos_of_ne_zero hC
  have hQuot : (a : Nat) * (c : Nat) / (c : Nat) = (a : Nat) := by
    simpa [Nat.mul_comm] using Nat.mul_div_right (a : Nat) hCPos
  have hFit : (a : Nat) ≤ MAX_UINT256 := Verity.Core.Uint256.val_le_max a
  rw [mulDiv512Down?_some (a := a) (b := c) (c := c) hC]
  · congr
    apply Verity.Core.Uint256.ext
    rw [hQuot]
    exact Nat.mod_eq_of_lt a.isLt
  · simpa [hQuot] using hFit

/-- Exact full-precision floor cancellation by the left numerator operand. -/
theorem mulDiv512Down?_cancel_left (a c : Uint256)
    (hC : (c : Nat) ≠ 0) :
    mulDiv512Down? c a c = some a := by
  rw [mulDiv512Down?_comm c a c]
  exact mulDiv512Down?_cancel_right a c hC

/-- Full-precision floor multiplication is monotone in its left numerator
operand for successful results. -/
theorem mulDiv512Down?_monotone_left (a₁ a₂ b c out₁ out₂ : Uint256)
    (hA : (a₁ : Nat) ≤ (a₂ : Nat))
    (h₁ : mulDiv512Down? a₁ b c = some out₁)
    (h₂ : mulDiv512Down? a₂ b c = some out₂) :
    (out₁ : Nat) ≤ (out₂ : Nat) := by
  rcases (mulDiv512Down?_eq_some_iff a₁ b c out₁).mp h₁ with ⟨_hC₁, hFit₁, hOut₁⟩
  rcases (mulDiv512Down?_eq_some_iff a₂ b c out₂).mp h₂ with ⟨_hC₂, hFit₂, hOut₂⟩
  rw [← hOut₁, ← hOut₂]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit₁),
    Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit₂)]
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ hA)

/-- Full-precision floor multiplication is monotone in its right numerator
operand for successful results. -/
theorem mulDiv512Down?_monotone_right (a b₁ b₂ c out₁ out₂ : Uint256)
    (hB : (b₁ : Nat) ≤ (b₂ : Nat))
    (h₁ : mulDiv512Down? a b₁ c = some out₁)
    (h₂ : mulDiv512Down? a b₂ c = some out₂) :
    (out₁ : Nat) ≤ (out₂ : Nat) := by
  rcases (mulDiv512Down?_eq_some_iff a b₁ c out₁).mp h₁ with ⟨_hC₁, hFit₁, hOut₁⟩
  rcases (mulDiv512Down?_eq_some_iff a b₂ c out₂).mp h₂ with ⟨_hC₂, hFit₂, hOut₂⟩
  rw [← hOut₁, ← hOut₂]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit₁),
    Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit₂)]
  exact Nat.div_le_div_right (Nat.mul_le_mul_left _ hB)

/-- Full-precision floor multiplication is antitone in the divisor for
successful results. -/
theorem mulDiv512Down?_antitone_divisor (a b c₁ c₂ out₁ out₂ : Uint256)
    (hC : (c₁ : Nat) ≤ (c₂ : Nat))
    (h₁ : mulDiv512Down? a b c₁ = some out₁)
    (h₂ : mulDiv512Down? a b c₂ = some out₂) :
    (out₂ : Nat) ≤ (out₁ : Nat) := by
  rcases (mulDiv512Down?_eq_some_iff a b c₁ out₁).mp h₁ with ⟨hC₁, hFit₁, hOut₁⟩
  rcases (mulDiv512Down?_eq_some_iff a b c₂ out₂).mp h₂ with ⟨_hC₂Some, hFit₂, hOut₂⟩
  rw [← hOut₁, ← hOut₂]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit₁),
    Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit₂)]
  exact Nat.div_le_div_left hC (Nat.pos_of_ne_zero hC₁)

/-- Regression: full-precision floor `mulDiv512` permits a 256-bit-overflowing
intermediate product when the final quotient fits. -/
theorem mulDiv512Down?_wide_product_regression :
    mulDiv512Down?
        (Verity.Core.Uint256.ofNat MAX_UINT256)
        (Verity.Core.Uint256.ofNat 2)
        (Verity.Core.Uint256.ofNat 2) =
      some (Verity.Core.Uint256.ofNat MAX_UINT256) := by
  have hMaxMod :
      MAX_UINT256 % Verity.Core.Uint256.modulus = MAX_UINT256 :=
    Nat.mod_eq_of_lt max_uint256_lt_modulus
  have hTwoMod : (2 : Nat) % Verity.Core.Uint256.modulus = 2 :=
    Nat.mod_eq_of_lt (by
      dsimp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
      decide)
  have hQuot : MAX_UINT256 * 2 / 2 = MAX_UINT256 := by
    simp
  simp [Verity.Stdlib.Math.mulDiv512Down?, hMaxMod, hTwoMod, hQuot]

/-- Regression: full-precision floor `mulDiv512` rejects when the 512-bit
product is valid but the final quotient does not fit in `uint256`. -/
theorem mulDiv512Down?_final_overflow_regression :
    mulDiv512Down?
        (Verity.Core.Uint256.ofNat MAX_UINT256)
        (Verity.Core.Uint256.ofNat 2)
        (Verity.Core.Uint256.ofNat 1) =
      none := by
  have hMaxMod :
      MAX_UINT256 % Verity.Core.Uint256.modulus = MAX_UINT256 :=
    Nat.mod_eq_of_lt max_uint256_lt_modulus
  have hTwoMod : (2 : Nat) % Verity.Core.Uint256.modulus = 2 :=
    Nat.mod_eq_of_lt (by
      dsimp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
      decide)
  have hQuot : MAX_UINT256 * 2 / 1 = MAX_UINT256 * 2 := by
    simp
  have hOverflow : MAX_UINT256 < MAX_UINT256 * 2 := by
    have hMaxPos : 0 < MAX_UINT256 := by
      dsimp [MAX_UINT256, Verity.Core.MAX_UINT256]
      decide
    simpa [Nat.mul_two] using Nat.lt_add_of_pos_right (n := MAX_UINT256) hMaxPos
  simp [Verity.Stdlib.Math.mulDiv512Down?, hMaxMod, hTwoMod, hQuot, hOverflow]

/-- `mulDiv512Up?` returns the exact full-precision ceil quotient when it fits. -/
theorem mulDiv512Up?_some (a b c : Uint256)
    (hC : (c : Nat) ≠ 0)
    (hFit : (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) ≤ MAX_UINT256) :
    mulDiv512Up? a b c =
      some (Verity.Core.Uint256.ofNat ((((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat))) := by
  simp [Verity.Stdlib.Math.mulDiv512Up?, hC, Nat.not_lt.mpr hFit]

/-- `mulDiv512Up?` rejects a zero divisor. -/
theorem mulDiv512Up?_none_of_zero_divisor (a b c : Uint256)
    (hC : (c : Nat) = 0) :
    mulDiv512Up? a b c = none := by
  simp [Verity.Stdlib.Math.mulDiv512Up?, hC]

/-- `mulDiv512Up?` rejects a rounded-up quotient that does not fit in `uint256`. -/
theorem mulDiv512Up?_none_of_overflow (a b c : Uint256)
    (hC : (c : Nat) ≠ 0)
    (hOverflow : MAX_UINT256 <
      (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat)) :
    mulDiv512Up? a b c = none := by
  simp [Verity.Stdlib.Math.mulDiv512Up?, hC, hOverflow]

/-- The quotient returned by `mulDiv512Up?` is the full-precision rounded-up quotient. -/
theorem mulDiv512Up?_eq_some_iff (a b c out : Uint256) :
    mulDiv512Up? a b c = some out ↔
      (c : Nat) ≠ 0 ∧
      (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) ≤ MAX_UINT256 ∧
      Verity.Core.Uint256.ofNat ((((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat)) = out := by
  by_cases hC : (c : Nat) = 0
  · simp [Verity.Stdlib.Math.mulDiv512Up?, hC]
  · by_cases hOverflow :
        (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) > MAX_UINT256
    · have hNotFit :
          ¬((((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) ≤ MAX_UINT256) := by
        exact Nat.not_le_of_gt hOverflow
      simp [Verity.Stdlib.Math.mulDiv512Up?, hC, hOverflow, hNotFit]
    · have hFit :
          (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) ≤ MAX_UINT256 :=
        Nat.le_of_not_gt hOverflow
      simp [Verity.Stdlib.Math.mulDiv512Up?, hC, hOverflow, hFit]

/-- `mulDiv512Up?` succeeds exactly when the divisor is nonzero and the
full-precision rounded-up quotient fits in `uint256`. -/
theorem mulDiv512Up?_isSome_iff (a b c : Uint256) :
    (mulDiv512Up? a b c).isSome ↔
      (c : Nat) ≠ 0 ∧
      (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) ≤ MAX_UINT256 := by
  by_cases hC : (c : Nat) = 0
  · simp [Verity.Stdlib.Math.mulDiv512Up?, hC]
  · by_cases hOverflow :
        (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) > MAX_UINT256
    · have hNotFit :
          ¬((((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) ≤ MAX_UINT256) := by
        exact Nat.not_le_of_gt hOverflow
      simp [Verity.Stdlib.Math.mulDiv512Up?, hC, hOverflow, hNotFit]
    · have hFit :
          (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) ≤ MAX_UINT256 :=
        Nat.le_of_not_gt hOverflow
      simp [Verity.Stdlib.Math.mulDiv512Up?, hC, hOverflow, hFit]

/-- A successful full-precision ceil result is above the exact product. -/
theorem mulDiv512Up?_mul_ge (a b c out : Uint256)
    (h : mulDiv512Up? a b c = some out) :
    (a : Nat) * (b : Nat) ≤ (out : Nat) * (c : Nat) := by
  rcases (mulDiv512Up?_eq_some_iff a b c out).mp h with ⟨hC, hFit, hOut⟩
  rw [← hOut]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit)]
  exact ceil_mul_div_ge ((a : Nat) * (b : Nat)) (c : Nat) (Nat.pos_of_ne_zero hC)

/-- A successful full-precision ceil result exceeds the exact product by less
than one divisor. -/
theorem mulDiv512Up?_mul_le_add_pred (a b c out : Uint256)
    (h : mulDiv512Up? a b c = some out) :
    (out : Nat) * (c : Nat) ≤ (a : Nat) * (b : Nat) + ((c : Nat) - 1) := by
  rcases (mulDiv512Up?_eq_some_iff a b c out).mp h with ⟨_hC, hFit, hOut⟩
  rw [← hOut]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit)]
  exact ceil_mul_div_le_add_pred ((a : Nat) * (b : Nat)) (c : Nat)

/-- A successful full-precision ceil result overshoots the exact product by
less than one divisor-width. -/
theorem mulDiv512Up?_mul_lt_add (a b c out : Uint256)
    (h : mulDiv512Up? a b c = some out) :
    (out : Nat) * (c : Nat) < (a : Nat) * (b : Nat) + (c : Nat) := by
  rcases (mulDiv512Up?_eq_some_iff a b c out).mp h with ⟨hC, _hFit, _hOut⟩
  exact Nat.lt_of_le_of_lt
    (mulDiv512Up?_mul_le_add_pred a b c out h)
    (Nat.add_lt_add_left (Nat.sub_lt (Nat.pos_of_ne_zero hC) (by decide)) _)

/-- `mulDiv512Up?` rejects exactly zero divisors or overflowing rounded-up quotients. -/
theorem mulDiv512Up?_isNone_iff (a b c : Uint256) :
    (mulDiv512Up? a b c).isNone ↔
      (c : Nat) = 0 ∨
      MAX_UINT256 <
        (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) := by
  by_cases hC : (c : Nat) = 0
  · simp [Verity.Stdlib.Math.mulDiv512Up?, hC]
  · by_cases hOverflow :
        (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) > MAX_UINT256
    · simp [Verity.Stdlib.Math.mulDiv512Up?, hC, hOverflow]
    · simp [Verity.Stdlib.Math.mulDiv512Up?, hC, hOverflow]

/-- If the rounded-up full-precision quotient fits, the matching floor
quotient also fits. -/
theorem mulDiv512Down?_isSome_of_up_isSome (a b c : Uint256)
    (h : (mulDiv512Up? a b c).isSome) :
    (mulDiv512Down? a b c).isSome := by
  rw [mulDiv512Up?_isSome_iff] at h
  rw [mulDiv512Down?_isSome_iff]
  rcases h with ⟨hC, hFit⟩
  refine ⟨hC, ?_⟩
  exact Nat.le_trans
    (Nat.div_le_div_right (Nat.le_add_right ((a : Nat) * (b : Nat)) ((c : Nat) - 1)))
    hFit

/-- If the full-precision floor quotient is rejected, the matching rounded-up
quotient is rejected too. -/
theorem mulDiv512Up?_isNone_of_down_isNone (a b c : Uint256)
    (h : (mulDiv512Down? a b c).isNone) :
    (mulDiv512Up? a b c).isNone := by
  rw [mulDiv512Down?_isNone_iff] at h
  rw [mulDiv512Up?_isNone_iff]
  rcases h with hZero | hOverflow
  · exact Or.inl hZero
  · exact Or.inr (Nat.lt_of_lt_of_le hOverflow
      (Nat.div_le_div_right
        (Nat.le_add_right ((a : Nat) * (b : Nat)) ((c : Nat) - 1))))

/-- Full-precision ceil multiplication is commutative in its numerator operands. -/
theorem mulDiv512Up?_comm (a b c : Uint256) :
    mulDiv512Up? a b c = mulDiv512Up? b a c := by
  simp [Verity.Stdlib.Math.mulDiv512Up?, Nat.mul_comm]

/-- A zero left numerator collapses full-precision ceil multiplication to zero. -/
theorem mulDiv512Up?_zero_left (b c : Uint256)
    (hC : (c : Nat) ≠ 0) :
    mulDiv512Up? 0 b c = some 0 := by
  have hCeilZero : (((0 : Uint256) : Nat) * (b : Nat) + ((c : Nat) - 1)) / (c : Nat) = 0 := by
    simpa using Nat.div_eq_of_lt (Nat.pred_lt hC)
  rw [mulDiv512Up?_some (a := 0) (b := b) (c := c) hC]
  · congr
  · rw [hCeilZero]
    exact Nat.zero_le _

/-- A zero right numerator collapses full-precision ceil multiplication to zero. -/
theorem mulDiv512Up?_zero_right (a c : Uint256)
    (hC : (c : Nat) ≠ 0) :
    mulDiv512Up? a 0 c = some 0 := by
  simpa [mulDiv512Up?_comm] using mulDiv512Up?_zero_left a c hC

/-- A successful full-precision ceil result is positive whenever both numerator
factors are positive. -/
theorem mulDiv512Up?_pos (a b c out : Uint256)
    (hA : 0 < (a : Nat))
    (hB : 0 < (b : Nat))
    (h : mulDiv512Up? a b c = some out) :
    0 < (out : Nat) := by
  rcases (mulDiv512Up?_eq_some_iff a b c out).mp h with ⟨hC, hFit, hOut⟩
  have hCPos : 0 < (c : Nat) := Nat.pos_of_ne_zero hC
  have hProdPos : 0 < (a : Nat) * (b : Nat) := Nat.mul_pos hA hB
  have hDivisorLe :
      (c : Nat) ≤ (a : Nat) * (b : Nat) + ((c : Nat) - 1) := by
    omega
  rw [← hOut]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit)]
  simpa [Nat.div_pos_iff, hCPos] using hDivisorLe

/-- Exact full-precision ceil cancellation by the right numerator operand. -/
theorem mulDiv512Up?_cancel_right (a c : Uint256)
    (hC : (c : Nat) ≠ 0) :
    mulDiv512Up? a c c = some a := by
  have hCPos : 0 < (c : Nat) := Nat.pos_of_ne_zero hC
  have hQuot :
      (((a : Nat) * (c : Nat)) + ((c : Nat) - 1)) / (c : Nat) = (a : Nat) := by
    calc
      (((a : Nat) * (c : Nat)) + ((c : Nat) - 1)) / (c : Nat)
          = (((c : Nat) - 1) + (c : Nat) * (a : Nat)) / (c : Nat) := by
              rw [Nat.mul_comm, Nat.add_comm]
      _ = ((c : Nat) - 1) / (c : Nat) + (a : Nat) :=
              Nat.add_mul_div_left ((c : Nat) - 1) (a : Nat) hCPos
      _ = (a : Nat) := by
              have hPredDiv : ((c : Nat) - 1) / (c : Nat) = 0 :=
                Nat.div_eq_of_lt (Nat.pred_lt hC)
              omega
  have hFit : (a : Nat) ≤ MAX_UINT256 := Verity.Core.Uint256.val_le_max a
  rw [mulDiv512Up?_some (a := a) (b := c) (c := c) hC]
  · congr
    apply Verity.Core.Uint256.ext
    rw [hQuot]
    exact Nat.mod_eq_of_lt a.isLt
  · simpa [hQuot] using hFit

/-- Exact full-precision ceil cancellation by the left numerator operand. -/
theorem mulDiv512Up?_cancel_left (a c : Uint256)
    (hC : (c : Nat) ≠ 0) :
    mulDiv512Up? c a c = some a := by
  rw [mulDiv512Up?_comm c a c]
  exact mulDiv512Up?_cancel_right a c hC

/-- Full-precision ceil multiplication is monotone in its left numerator
operand for successful results. -/
theorem mulDiv512Up?_monotone_left (a₁ a₂ b c out₁ out₂ : Uint256)
    (hA : (a₁ : Nat) ≤ (a₂ : Nat))
    (h₁ : mulDiv512Up? a₁ b c = some out₁)
    (h₂ : mulDiv512Up? a₂ b c = some out₂) :
    (out₁ : Nat) ≤ (out₂ : Nat) := by
  rcases (mulDiv512Up?_eq_some_iff a₁ b c out₁).mp h₁ with ⟨_hC₁, hFit₁, hOut₁⟩
  rcases (mulDiv512Up?_eq_some_iff a₂ b c out₂).mp h₂ with ⟨_hC₂, hFit₂, hOut₂⟩
  rw [← hOut₁, ← hOut₂]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit₁),
    Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit₂)]
  exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hA) _)

/-- Full-precision ceil multiplication is monotone in its right numerator
operand for successful results. -/
theorem mulDiv512Up?_monotone_right (a b₁ b₂ c out₁ out₂ : Uint256)
    (hB : (b₁ : Nat) ≤ (b₂ : Nat))
    (h₁ : mulDiv512Up? a b₁ c = some out₁)
    (h₂ : mulDiv512Up? a b₂ c = some out₂) :
    (out₁ : Nat) ≤ (out₂ : Nat) := by
  rcases (mulDiv512Up?_eq_some_iff a b₁ c out₁).mp h₁ with ⟨_hC₁, hFit₁, hOut₁⟩
  rcases (mulDiv512Up?_eq_some_iff a b₂ c out₂).mp h₂ with ⟨_hC₂, hFit₂, hOut₂⟩
  rw [← hOut₁, ← hOut₂]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit₁),
    Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit₂)]
  exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ hB) _)

/-- Full-precision ceil multiplication is antitone in the divisor for
successful results. -/
theorem mulDiv512Up?_antitone_divisor (a b c₁ c₂ out₁ out₂ : Uint256)
    (hC : (c₁ : Nat) ≤ (c₂ : Nat))
    (h₁ : mulDiv512Up? a b c₁ = some out₁)
    (h₂ : mulDiv512Up? a b c₂ = some out₂) :
    (out₂ : Nat) ≤ (out₁ : Nat) := by
  rcases (mulDiv512Up?_eq_some_iff a b c₁ out₁).mp h₁ with ⟨hC₁, hFit₁, hOut₁⟩
  rcases (mulDiv512Up?_eq_some_iff a b c₂ out₂).mp h₂ with ⟨hC₂, hFit₂, hOut₂⟩
  rw [← hOut₁, ← hOut₂]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit₁),
    Nat.mod_eq_of_lt (lt_modulus_of_le_max hFit₂)]
  exact nat_ceil_div_antitone_divisor ((a : Nat) * (b : Nat)) (c₁ : Nat) (c₂ : Nat) hC hC₁ hC₂

/-- Regression: full-precision ceil `mulDiv512` permits a 256-bit-overflowing
intermediate product when the rounded quotient fits. -/
theorem mulDiv512Up?_wide_product_regression :
    mulDiv512Up?
        (Verity.Core.Uint256.ofNat MAX_UINT256)
        (Verity.Core.Uint256.ofNat 2)
        (Verity.Core.Uint256.ofNat 2) =
      some (Verity.Core.Uint256.ofNat MAX_UINT256) := by
  have hMaxMod :
      MAX_UINT256 % Verity.Core.Uint256.modulus = MAX_UINT256 :=
    Nat.mod_eq_of_lt max_uint256_lt_modulus
  have hTwoMod : (2 : Nat) % Verity.Core.Uint256.modulus = 2 :=
    Nat.mod_eq_of_lt (by
      dsimp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
      decide)
  have hQuot : (MAX_UINT256 * 2 + (2 - 1)) / 2 = MAX_UINT256 := by
    rw [show (2 : Nat) - 1 = 1 by omega]
    calc
      (MAX_UINT256 * 2 + 1) / 2 = (1 + 2 * MAX_UINT256) / 2 := by
        rw [Nat.mul_comm MAX_UINT256 2, Nat.add_comm]
      _ = 1 / 2 + MAX_UINT256 := Nat.add_mul_div_left 1 MAX_UINT256 (by decide : 0 < 2)
      _ = MAX_UINT256 := by
        rw [Nat.div_eq_of_lt (by decide : 1 < 2)]
        rfl
  simp [Verity.Stdlib.Math.mulDiv512Up?, hMaxMod, hTwoMod, hQuot]

/-- Regression: full-precision ceil `mulDiv512` rejects when the rounded
512-bit quotient does not fit in `uint256`. -/
theorem mulDiv512Up?_final_overflow_regression :
    mulDiv512Up?
        (Verity.Core.Uint256.ofNat MAX_UINT256)
        (Verity.Core.Uint256.ofNat 2)
        (Verity.Core.Uint256.ofNat 1) =
      none := by
  have hMaxMod :
      MAX_UINT256 % Verity.Core.Uint256.modulus = MAX_UINT256 :=
    Nat.mod_eq_of_lt max_uint256_lt_modulus
  have hTwoMod : (2 : Nat) % Verity.Core.Uint256.modulus = 2 :=
    Nat.mod_eq_of_lt (by
      dsimp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
      decide)
  have hOverflow : MAX_UINT256 < MAX_UINT256 * 2 := by
    have hMaxPos : 0 < MAX_UINT256 := by
      dsimp [MAX_UINT256, Verity.Core.MAX_UINT256]
      decide
    simpa [Nat.mul_two] using Nat.lt_add_of_pos_right (n := MAX_UINT256) hMaxPos
  simp [Verity.Stdlib.Math.mulDiv512Up?, hMaxMod, hTwoMod, hOverflow]

/-! ## mulDiv / wad helpers -/

/-- `mulDivDown` agrees with exact natural-number division when the numerator does not wrap. -/
theorem mulDivDown_nat_eq (a b c : Uint256) (hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
    (mulDivDown a b c : Nat) =
      if (c : Nat) = 0 then 0 else ((a : Nat) * (b : Nat)) / (c : Nat) := by
  have hMulLt : (a : Nat) * (b : Nat) < Verity.Core.Uint256.modulus :=
    lt_modulus_of_le_max hMul
  have hProd : ((a * b : Uint256) : Nat) = (a : Nat) * (b : Nat) :=
    Verity.Core.Uint256.mul_eq_of_lt hMulLt
  by_cases hZero : (c : Nat) = 0
  · simp [mulDivDown, HDiv.hDiv, Verity.Core.Uint256.div, hZero]
  · have hCPos : 0 < (c : Nat) := Nat.pos_of_ne_zero hZero
    have hDivLt : ((a : Nat) * (b : Nat)) / (c : Nat) < Verity.Core.Uint256.modulus := by
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hMulLt
    calc
      (mulDivDown a b c : Nat)
          = (((a * b : Uint256) : Nat) / (c : Nat)) % Verity.Core.Uint256.modulus := by
              simp [mulDivDown, HDiv.hDiv, Verity.Core.Uint256.div, hZero]
      _ = (((a : Nat) * (b : Nat)) / (c : Nat)) % Verity.Core.Uint256.modulus := by
              simp [hProd]
      _ = ((a : Nat) * (b : Nat)) / (c : Nat) := Nat.mod_eq_of_lt hDivLt
      _ = dite ((c : Nat) = 0) (fun _ => 0) (fun _ => ((a : Nat) * (b : Nat)) / (c : Nat)) := by
              simp [hZero]

/-- Rounding down never overshoots the exact numerator product. -/
theorem mulDivDown_mul_le (a b c : Uint256) (hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
    (mulDivDown a b c : Nat) * (c : Nat) ≤ (a : Nat) * (b : Nat) := by
  by_cases hZero : (c : Nat) = 0
  · rw [mulDivDown_nat_eq a b c hMul]
    simp [hZero]
  · rw [mulDivDown_nat_eq a b c hMul]
    simp [hZero]
    exact Nat.div_mul_le_self _ _

/-- Floor division is positive once the exact numerator reaches at least one divisor-width. -/
theorem mulDivDown_pos (a b c : Uint256)
    (hC : c ≠ 0)
    (hLower : (c : Nat) ≤ (a : Nat) * (b : Nat))
    (hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
    0 < (mulDivDown a b c : Nat) := by
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  have hCPos : 0 < (c : Nat) := Nat.pos_of_ne_zero hCVal
  rw [mulDivDown_nat_eq a b c hMul]
  simpa [hCVal, Nat.div_pos_iff, hCPos] using hLower

/-- A zero left numerator collapses `mulDivDown` to zero. -/
theorem mulDivDown_zero_left (b c : Uint256) :
    (mulDivDown 0 b c : Nat) = 0 := by
  have hMul : ((0 : Uint256) : Nat) * (b : Nat) ≤ MAX_UINT256 := by simp
  by_cases hZero : (c : Nat) = 0
  · rw [mulDivDown_nat_eq 0 b c hMul]
    simp [hZero]
  · rw [mulDivDown_nat_eq 0 b c hMul]
    simp [hZero]

/-- A zero right numerator collapses `mulDivDown` to zero. -/
theorem mulDivDown_zero_right (a c : Uint256) :
    (mulDivDown a 0 c : Nat) = 0 := by
  have hMul : (a : Nat) * ((0 : Uint256) : Nat) ≤ MAX_UINT256 := by simp
  by_cases hZero : (c : Nat) = 0
  · rw [mulDivDown_nat_eq a 0 c hMul]
    simp [hZero]
  · rw [mulDivDown_nat_eq a 0 c hMul]
    simp [hZero]

/-- `mulDivDown` is monotone in its left numerator operand when the product stays exact. -/
theorem mulDivDown_monotone_left (a₁ a₂ b c : Uint256)
    (hA : (a₁ : Nat) ≤ (a₂ : Nat))
    (hMul : (a₂ : Nat) * (b : Nat) ≤ MAX_UINT256) :
    (mulDivDown a₁ b c : Nat) ≤ (mulDivDown a₂ b c : Nat) := by
  have hMul₁ : (a₁ : Nat) * (b : Nat) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.mul_le_mul_right _ hA) hMul
  by_cases hZero : (c : Nat) = 0
  · rw [mulDivDown_nat_eq a₁ b c hMul₁, mulDivDown_nat_eq a₂ b c hMul]
    simp [hZero]
  · rw [mulDivDown_nat_eq a₁ b c hMul₁, mulDivDown_nat_eq a₂ b c hMul]
    simp [hZero]
    exact Nat.div_le_div_right (Nat.mul_le_mul_right _ hA)

/-- `mulDivDown` is monotone in its right numerator operand when the product stays exact. -/
theorem mulDivDown_monotone_right (a b₁ b₂ c : Uint256)
    (hB : (b₁ : Nat) ≤ (b₂ : Nat))
    (hMul : (a : Nat) * (b₂ : Nat) ≤ MAX_UINT256) :
    (mulDivDown a b₁ c : Nat) ≤ (mulDivDown a b₂ c : Nat) := by
  have hMul₁ : (a : Nat) * (b₁ : Nat) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.mul_le_mul_left _ hB) hMul
  by_cases hZero : (c : Nat) = 0
  · rw [mulDivDown_nat_eq a b₁ c hMul₁, mulDivDown_nat_eq a b₂ c hMul]
    simp [hZero]
  · rw [mulDivDown_nat_eq a b₁ c hMul₁, mulDivDown_nat_eq a b₂ c hMul]
    simp [hZero]
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ hB)

/-- `mulDivDown` is commutative in its numerator operands. -/
theorem mulDivDown_comm (a b c : Uint256) :
    mulDivDown a b c = mulDivDown b a c := by
  simp [mulDivDown, Verity.Core.Uint256.mul_comm]

/-- Dividing an exact numerator product by its right factor recovers the left factor. -/
theorem mulDivDown_cancel_right (a c : Uint256)
    (hC : c ≠ 0)
    (hMul : (a : Nat) * (c : Nat) ≤ MAX_UINT256) :
    (mulDivDown a c c : Nat) = (a : Nat) := by
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  have hCPos : 0 < (c : Nat) := Nat.pos_of_ne_zero hCVal
  rw [mulDivDown_nat_eq a c c hMul]
  simp [hCVal]

/-- Dividing an exact numerator product by its left factor recovers the right factor. -/
theorem mulDivDown_cancel_left (a c : Uint256)
    (hC : c ≠ 0)
    (hMul : (c : Nat) * (a : Nat) ≤ MAX_UINT256) :
    (mulDivDown c a c : Nat) = (a : Nat) := by
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  have hCPos : 0 < (c : Nat) := Nat.pos_of_ne_zero hCVal
  rw [mulDivDown_nat_eq c a c hMul]
  simp [hCVal, Nat.mul_comm]

/-- Floor rounding undershoots the exact numerator by less than one divisor-width. -/
theorem mulDivDown_mul_lt_add (a b c : Uint256)
    (hC : c ≠ 0)
    (hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
    (a : Nat) * (b : Nat) < (mulDivDown a b c : Nat) * (c : Nat) + (c : Nat) := by
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  rw [mulDivDown_nat_eq a b c hMul]
  simp [hCVal]
  have hModLt : ((a : Nat) * (b : Nat)) % (c : Nat) < (c : Nat) := Nat.mod_lt _ (Nat.pos_of_ne_zero hCVal)
  calc
    (a : Nat) * (b : Nat)
        = (c : Nat) * (((a : Nat) * (b : Nat)) / (c : Nat)) + (((a : Nat) * (b : Nat)) % (c : Nat)) := by
            simpa [Nat.mul_comm] using (Nat.div_add_mod ((a : Nat) * (b : Nat)) (c : Nat)).symm
    _ < (c : Nat) * (((a : Nat) * (b : Nat)) / (c : Nat)) + (c : Nat) := by
          exact Nat.add_lt_add_left hModLt _
    _ = (((a : Nat) * (b : Nat)) / (c : Nat)) * (c : Nat) + (c : Nat) := by
          simp [Nat.mul_comm]

/-- Increasing the divisor can only decrease `mulDivDown` when both quotients are exact. -/
theorem mulDivDown_antitone_divisor (a b c₁ c₂ : Uint256)
    (hC : (c₁ : Nat) ≤ (c₂ : Nat))
    (hC₁ : c₁ ≠ 0)
    (hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
    (mulDivDown a b c₂ : Nat) ≤ (mulDivDown a b c₁ : Nat) := by
  have hC₁Val : (c₁ : Nat) ≠ 0 := by
    intro h
    apply hC₁
    exact Verity.Core.Uint256.ext (by simpa using h)
  by_cases hC₂Val : (c₂ : Nat) = 0
  · have hC₁Zero : (c₁ : Nat) = 0 := Nat.eq_zero_of_le_zero (by simpa [hC₂Val] using hC)
    exact (hC₁Val hC₁Zero).elim
  · have hLeft :
        (mulDivDown a b c₂ : Nat) * (c₁ : Nat) ≤ (a : Nat) * (b : Nat) := by
      exact Nat.le_trans
        (Nat.mul_le_mul_left _ hC)
        (mulDivDown_mul_le a b c₂ hMul)
    have hRight :
        (a : Nat) * (b : Nat) <
          (mulDivDown a b c₁ : Nat) * (c₁ : Nat) + (c₁ : Nat) :=
      mulDivDown_mul_lt_add a b c₁ hC₁ hMul
    have hLt :
        (mulDivDown a b c₂ : Nat) * (c₁ : Nat) <
          ((mulDivDown a b c₁ : Nat) + 1) * (c₁ : Nat) := by
      calc
        (mulDivDown a b c₂ : Nat) * (c₁ : Nat) ≤ (a : Nat) * (b : Nat) := hLeft
        _ < (mulDivDown a b c₁ : Nat) * (c₁ : Nat) + (c₁ : Nat) := hRight
        _ = ((mulDivDown a b c₁ : Nat) + 1) * (c₁ : Nat) := by
              simp [Nat.right_distrib]
    have hLt' :
        (c₁ : Nat) * (mulDivDown a b c₂ : Nat) <
          (c₁ : Nat) * ((mulDivDown a b c₁ : Nat) + 1) := by
      simpa [Nat.mul_comm] using hLt
    exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left hLt')

/-- `mulDivUp` agrees with exact ceil-division when the widened numerator does not wrap. -/
theorem mulDivUp_nat_eq (a b c : Uint256)
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivUp a b c : Nat) = (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) := by
  have hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.le_add_right _ _) hNum
  have hMulLt : (a : Nat) * (b : Nat) < Verity.Core.Uint256.modulus :=
    lt_modulus_of_le_max hMul
  have hProd : ((a * b : Uint256) : Nat) = (a : Nat) * (b : Nat) :=
    Verity.Core.Uint256.mul_eq_of_lt hMulLt
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  have hOneLe : (1 : Nat) ≤ (c : Nat) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hCVal)
  have hSub : ((c - 1 : Uint256) : Nat) = (c : Nat) - 1 :=
    Verity.Core.Uint256.sub_eq_of_le hOneLe
  have hNumLt : (a : Nat) * (b : Nat) + ((c : Nat) - 1) < Verity.Core.Uint256.modulus :=
    lt_modulus_of_le_max hNum
  have hNumerator :
      (((a * b : Uint256) + (c - 1 : Uint256) : Uint256) : Nat) =
        (a : Nat) * (b : Nat) + ((c : Nat) - 1) := by
    have hAdd :
        (((a * b : Uint256) + (c - 1 : Uint256) : Uint256) : Nat) =
          ((a * b : Uint256) : Nat) + ((c - 1 : Uint256) : Nat) :=
      Verity.Core.Uint256.add_eq_of_lt (by simpa [hProd, hSub] using hNumLt)
    simpa [hProd, hSub] using hAdd
  have hDivLt :
      (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) < Verity.Core.Uint256.modulus := by
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hNumLt
  calc
    (mulDivUp a b c : Nat)
        = ((((a * b : Uint256) + (c - 1 : Uint256) : Uint256) : Nat) / (c : Nat)) %
            Verity.Core.Uint256.modulus := by
              simp [mulDivUp, HDiv.hDiv, Verity.Core.Uint256.div, hCVal]
    _ = (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) % Verity.Core.Uint256.modulus := by
            simp [hNumerator]
    _ = (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) := Nat.mod_eq_of_lt hDivLt

/-- `mulDiv512Down?` agrees with the existing `mulDivDown` helper when the
intermediate product fits in `uint256`. -/
theorem mulDiv512Down?_eq_mulDivDown_of_no_overflow (a b c : Uint256)
    (hC : (c : Nat) ≠ 0)
    (hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
    mulDiv512Down? a b c = some (mulDivDown a b c) := by
  have hQuotFit : ((a : Nat) * (b : Nat)) / (c : Nat) ≤ MAX_UINT256 :=
    Nat.le_trans (Nat.div_le_self _ _) hMul
  rw [mulDiv512Down?_some (a := a) (b := b) (c := c) hC hQuotFit]
  congr
  apply Verity.Core.Uint256.ext
  rw [mulDivDown_nat_eq a b c hMul]
  simp [hC, Nat.mod_eq_of_lt (lt_modulus_of_le_max hQuotFit)]

/-- `mulDiv512Up?` agrees with the existing `mulDivUp` helper when the
rounded numerator expression fits in `uint256`. -/
theorem mulDiv512Up?_eq_mulDivUp_of_no_overflow (a b c : Uint256)
    (hC : (c : Nat) ≠ 0)
    (hNum : (a : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    mulDiv512Up? a b c = some (mulDivUp a b c) := by
  have hCUint : c ≠ 0 := by
    intro h
    exact hC (by simpa using congrArg (fun x : Uint256 => (x : Nat)) h)
  have hQuotFit :
      (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) ≤ MAX_UINT256 :=
    Nat.le_trans (Nat.div_le_self _ _) hNum
  rw [mulDiv512Up?_some (a := a) (b := b) (c := c) hC hQuotFit]
  congr
  apply Verity.Core.Uint256.ext
  rw [mulDivUp_nat_eq a b c hCUint hNum]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hQuotFit)]

/-- The ceil helper never rounds below the floor helper when both are exact. -/
theorem mulDivDown_le_mulDivUp (a b c : Uint256)
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivDown a b c : Nat) ≤ (mulDivUp a b c : Nat) := by
  have hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.le_add_right _ _) hNum
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  rw [mulDivDown_nat_eq a b c hMul, mulDivUp_nat_eq a b c hC hNum]
  simp [hCVal]
  apply Nat.div_le_div_right
  exact Nat.le_add_right _ _

private theorem nat_ceil_div_le_div_add_one (n c : Nat) (hC : c ≠ 0) :
    (n + (c - 1)) / c ≤ n / c + 1 := by
  have hCPos : 0 < c := Nat.pos_of_ne_zero hC
  refine (Nat.div_le_iff_le_mul_add_pred hCPos).2 ?_
  have hDivBound : n ≤ c * (n / c) + c := by
    calc
      n = c * (n / c) + (n % c) := by simpa [Nat.mul_comm] using (Nat.div_add_mod' n c).symm
      _ ≤ c * (n / c) + c := Nat.add_le_add_left (Nat.le_of_lt (Nat.mod_lt _ hCPos)) _
  calc
    n + (c - 1) ≤ (c * (n / c) + c) + (c - 1) := Nat.add_le_add_right hDivBound _
    _ = c * (n / c + 1) + (c - 1) := by
      rw [Nat.mul_add]
      ac_rfl

private theorem nat_ceil_div_eq_div_of_dvd (n c : Nat) (hC : c ≠ 0) (hDvd : c ∣ n) :
    (n + (c - 1)) / c = n / c := by
  have hCPos : 0 < c := Nat.pos_of_ne_zero hC
  have hSubLt : c - 1 < c := Nat.sub_lt hCPos (by decide)
  rw [Nat.add_div hCPos]
  simp [Nat.mod_eq_zero_of_dvd hDvd, Nat.div_eq_of_lt hSubLt, Nat.mod_eq_of_lt hSubLt, hSubLt]

private theorem nat_ceil_div_eq_div_add_one_of_not_dvd (n c : Nat) (hC : c ≠ 0)
    (hNotDvd : ¬ c ∣ n) :
    (n + (c - 1)) / c = n / c + 1 := by
  have hCPos : 0 < c := Nat.pos_of_ne_zero hC
  have hSubLt : c - 1 < c := Nat.sub_lt hCPos (by decide)
  have hModPos : 0 < n % c := by
    exact Nat.pos_of_ne_zero (by
      intro hMod
      apply hNotDvd
      exact Nat.dvd_of_mod_eq_zero hMod)
  rw [Nat.add_div hCPos]
  have hCarry : c ≤ n % c + ((c - 1) % c) := by
    rw [Nat.mod_eq_of_lt hSubLt]
    omega
  rw [Nat.div_eq_of_lt hSubLt, Nat.mod_eq_of_lt hSubLt]
  simp
  simpa [Nat.mod_eq_of_lt hSubLt] using hCarry

/-- Exact divisibility removes the full-precision ceil/floor gap. -/
theorem mulDiv512Up?_eq_down_of_dvd (a b c : Uint256)
    (hC : (c : Nat) ≠ 0)
    (hFit : (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) ≤ MAX_UINT256)
    (hDvd : (c : Nat) ∣ (a : Nat) * (b : Nat)) :
    mulDiv512Up? a b c = mulDiv512Down? a b c := by
  have hCeil :
      (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) =
        ((a : Nat) * (b : Nat)) / (c : Nat) :=
    nat_ceil_div_eq_div_of_dvd ((a : Nat) * (b : Nat)) (c : Nat) hC hDvd
  rw [mulDiv512Up?_some (a := a) (b := b) (c := c) hC hFit]
  rw [mulDiv512Down?_some (a := a) (b := b) (c := c) hC]
  · congr
  · simpa [← hCeil] using hFit

/-- If the full-precision numerator is not divisible by the divisor, ceil
division is the successor of floor division. -/
theorem mulDiv512Up?_some_succ_of_not_dvd (a b c : Uint256)
    (hC : (c : Nat) ≠ 0)
    (hFit : (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) ≤ MAX_UINT256)
    (hNotDvd : ¬ (c : Nat) ∣ (a : Nat) * (b : Nat)) :
    mulDiv512Up? a b c =
      some (Verity.Core.Uint256.ofNat (((a : Nat) * (b : Nat)) / (c : Nat) + 1)) := by
  have hCeil :
      (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) =
        ((a : Nat) * (b : Nat)) / (c : Nat) + 1 :=
    nat_ceil_div_eq_div_add_one_of_not_dvd
      ((a : Nat) * (b : Nat)) (c : Nat) hC hNotDvd
  rw [mulDiv512Up?_some (a := a) (b := b) (c := c) hC hFit]
  congr

/-- A successful full-precision ceil result never rounds below the matching
floor result. -/
theorem mulDiv512Down?_le_up (a b c down up : Uint256)
    (hDown : mulDiv512Down? a b c = some down)
    (hUp : mulDiv512Up? a b c = some up) :
    (down : Nat) ≤ (up : Nat) := by
  rcases (mulDiv512Down?_eq_some_iff a b c down).mp hDown with ⟨_hCDown, hDownFit, hDownOut⟩
  rcases (mulDiv512Up?_eq_some_iff a b c up).mp hUp with ⟨_hCUp, hUpFit, hUpOut⟩
  rw [← hDownOut, ← hUpOut]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hDownFit),
    Nat.mod_eq_of_lt (lt_modulus_of_le_max hUpFit)]
  apply Nat.div_le_div_right
  exact Nat.le_add_right _ _

/-- A successful full-precision ceil result is at most one quotient step above
the matching floor result. -/
theorem mulDiv512Up?_le_down_add_one (a b c down up : Uint256)
    (hDown : mulDiv512Down? a b c = some down)
    (hUp : mulDiv512Up? a b c = some up) :
    (up : Nat) ≤ (down : Nat) + 1 := by
  rcases (mulDiv512Down?_eq_some_iff a b c down).mp hDown with ⟨hC, hDownFit, hDownOut⟩
  rcases (mulDiv512Up?_eq_some_iff a b c up).mp hUp with ⟨_hCUp, hUpFit, hUpOut⟩
  rw [← hDownOut, ← hUpOut]
  simp [Nat.mod_eq_of_lt (lt_modulus_of_le_max hDownFit),
    Nat.mod_eq_of_lt (lt_modulus_of_le_max hUpFit)]
  exact nat_ceil_div_le_div_add_one ((a : Nat) * (b : Nat)) (c : Nat) hC

/-- Successful full-precision ceil and floor results either match exactly or
differ by one quotient step. -/
theorem mulDiv512Up?_eq_down_or_succ (a b c down up : Uint256)
    (hDown : mulDiv512Down? a b c = some down)
    (hUp : mulDiv512Up? a b c = some up) :
    (up : Nat) = (down : Nat) ∨ (up : Nat) = (down : Nat) + 1 := by
  have hLower : (down : Nat) ≤ (up : Nat) :=
    mulDiv512Down?_le_up a b c down up hDown hUp
  have hUpper : (up : Nat) ≤ (down : Nat) + 1 :=
    mulDiv512Up?_le_down_add_one a b c down up hDown hUp
  omega

/-- The ceil helper exceeds the floor helper by at most one quotient step when both are exact. -/
theorem mulDivUp_le_mulDivDown_add_one (a b c : Uint256)
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivUp a b c : Nat) ≤ (mulDivDown a b c : Nat) + 1 := by
  have hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.le_add_right _ _) hNum
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  rw [mulDivUp_nat_eq a b c hC hNum, mulDivDown_nat_eq a b c hMul]
  simp [hCVal]
  exact nat_ceil_div_le_div_add_one ((a : Nat) * (b : Nat)) (c : Nat) hCVal

/-- Exact ceil/floor division differs by at most one step. -/
theorem mulDivUp_eq_mulDivDown_or_succ (a b c : Uint256)
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivUp a b c : Nat) = (mulDivDown a b c : Nat) ∨
      (mulDivUp a b c : Nat) = (mulDivDown a b c : Nat) + 1 := by
  have hLower : (mulDivDown a b c : Nat) ≤ (mulDivUp a b c : Nat) :=
    mulDivDown_le_mulDivUp a b c hC hNum
  have hUpper : (mulDivUp a b c : Nat) ≤ (mulDivDown a b c : Nat) + 1 :=
    mulDivUp_le_mulDivDown_add_one a b c hC hNum
  omega

/-- Exact divisibility removes the ceil/floor gap for `mulDivUp` and `mulDivDown`. -/
theorem mulDivUp_eq_mulDivDown_of_dvd (a b c : Uint256)
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256)
    (hDvd : (c : Nat) ∣ (a : Nat) * (b : Nat)) :
    (mulDivUp a b c : Nat) = (mulDivDown a b c : Nat) := by
  have hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.le_add_right _ _) hNum
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  rw [mulDivUp_nat_eq a b c hC hNum, mulDivDown_nat_eq a b c hMul]
  simp [hCVal]
  exact nat_ceil_div_eq_div_of_dvd ((a : Nat) * (b : Nat)) (c : Nat) hCVal hDvd

/-- If the numerator is not divisible by the divisor, ceil division is the successor of floor division. -/
theorem mulDivUp_eq_mulDivDown_add_one_of_not_dvd (a b c : Uint256)
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256)
    (hNotDvd : ¬ (c : Nat) ∣ (a : Nat) * (b : Nat)) :
    (mulDivUp a b c : Nat) = (mulDivDown a b c : Nat) + 1 := by
  have hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.le_add_right _ _) hNum
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  rw [mulDivUp_nat_eq a b c hC hNum, mulDivDown_nat_eq a b c hMul]
  simp [hCVal]
  exact nat_ceil_div_eq_div_add_one_of_not_dvd ((a : Nat) * (b : Nat)) (c : Nat) hCVal hNotDvd

/-- Ceil division is positive whenever both numerator factors are positive. -/
theorem mulDivUp_pos (a b c : Uint256)
    (hA : 0 < (a : Nat))
    (hB : 0 < (b : Nat))
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    0 < (mulDivUp a b c : Nat) := by
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  have hCPos : 0 < (c : Nat) := Nat.pos_of_ne_zero hCVal
  have hProdPos : 0 < (a : Nat) * (b : Nat) := Nat.mul_pos hA hB
  rw [mulDivUp_nat_eq a b c hC hNum]
  have hDivisorLe :
      (c : Nat) ≤ (a : Nat) * (b : Nat) + ((c : Nat) - 1) := by
    omega
  simpa [Nat.div_pos_iff, hCPos] using hDivisorLe

/-- A zero left numerator collapses `mulDivUp` to zero. -/
theorem mulDivUp_zero_left (b c : Uint256)
    (hC : c ≠ 0) :
    (mulDivUp 0 b c : Nat) = 0 := by
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  have hNum : ((0 : Uint256) : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256 := by
    calc
      ((0 : Uint256) : Nat) * (b : Nat) + ((c : Nat) - 1) = (c : Nat) - 1 := by simp
      _ ≤ (c : Nat) := Nat.sub_le _ _
      _ ≤ MAX_UINT256 := Verity.Core.Uint256.val_le_max c
  rw [mulDivUp_nat_eq 0 b c hC hNum]
  have hLt : (c : Nat) - 1 < (c : Nat) := Nat.sub_lt (Nat.pos_of_ne_zero hCVal) (by decide)
  simpa using (Nat.div_eq_of_lt hLt)

/-- A zero right numerator collapses `mulDivUp` to zero. -/
theorem mulDivUp_zero_right (a c : Uint256)
    (hC : c ≠ 0) :
    (mulDivUp a 0 c : Nat) = 0 := by
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  have hNum : (a : Nat) * ((0 : Uint256) : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256 := by
    calc
      (a : Nat) * ((0 : Uint256) : Nat) + ((c : Nat) - 1) = (c : Nat) - 1 := by simp
      _ ≤ (c : Nat) := Nat.sub_le _ _
      _ ≤ MAX_UINT256 := Verity.Core.Uint256.val_le_max c
  rw [mulDivUp_nat_eq a 0 c hC hNum]
  have hLt : (c : Nat) - 1 < (c : Nat) := Nat.sub_lt (Nat.pos_of_ne_zero hCVal) (by decide)
  simpa using (Nat.div_eq_of_lt hLt)

/-- `mulDivUp` is monotone in its left numerator operand when the widened numerator stays exact. -/
theorem mulDivUp_monotone_left (a₁ a₂ b c : Uint256)
    (hA : (a₁ : Nat) ≤ (a₂ : Nat))
    (hC : c ≠ 0)
    (hNum : (a₂ : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivUp a₁ b c : Nat) ≤ (mulDivUp a₂ b c : Nat) := by
  have hNum₁ : (a₁ : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hA) _) hNum
  rw [mulDivUp_nat_eq a₁ b c hC hNum₁, mulDivUp_nat_eq a₂ b c hC hNum]
  exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hA) _)

/-- `mulDivUp` is monotone in its right numerator operand when the widened numerator stays exact. -/
theorem mulDivUp_monotone_right (a b₁ b₂ c : Uint256)
    (hB : (b₁ : Nat) ≤ (b₂ : Nat))
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (b₂ : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivUp a b₁ c : Nat) ≤ (mulDivUp a b₂ c : Nat) := by
  have hNum₁ : (a : Nat) * (b₁ : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hB) _) hNum
  rw [mulDivUp_nat_eq a b₁ c hC hNum₁, mulDivUp_nat_eq a b₂ c hC hNum]
  exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ hB) _)

/-- `mulDivUp` is commutative in its numerator operands. -/
theorem mulDivUp_comm (a b c : Uint256) :
    mulDivUp a b c = mulDivUp b a c := by
  simp [mulDivUp, Verity.Core.Uint256.mul_comm]

/-- Ceil-division of an exact numerator product by its right factor recovers the left factor. -/
theorem mulDivUp_cancel_right (a c : Uint256)
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (c : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivUp a c c : Nat) = (a : Nat) := by
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  have hCPos : 0 < (c : Nat) := Nat.pos_of_ne_zero hCVal
  rw [mulDivUp_nat_eq a c c hC hNum]
  have hLower : (a : Nat) ≤ ((((a : Nat) * (c : Nat)) + ((c : Nat) - 1)) / (c : Nat)) := by
    exact (Nat.le_div_iff_mul_le hCPos).2 (Nat.le_add_right _ _)
  have hUpper :
      ((((a : Nat) * (c : Nat)) + ((c : Nat) - 1)) / (c : Nat)) < (a : Nat) + 1 := by
    refine (Nat.div_lt_iff_lt_mul hCPos).2 ?_
    have hSubLt : (c : Nat) - 1 < (c : Nat) := Nat.sub_lt hCPos (by decide)
    calc
      (a : Nat) * (c : Nat) + ((c : Nat) - 1) < (a : Nat) * (c : Nat) + (c : Nat) := by
        exact Nat.add_lt_add_left hSubLt _
      _ = ((a : Nat) + 1) * (c : Nat) := by
        simp [Nat.right_distrib]
  omega

/-- Ceil-division of an exact numerator product by its left factor recovers the right factor. -/
theorem mulDivUp_cancel_left (a c : Uint256)
    (hC : c ≠ 0)
    (hNum : (c : Nat) * (a : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivUp c a c : Nat) = (a : Nat) := by
  have hNum' : (a : Nat) * (c : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256 := by
    simpa [Nat.mul_comm] using hNum
  simpa [Nat.mul_comm] using mulDivUp_cancel_right a c hC hNum'

/-- Ceil rounding overshoots the exact numerator by less than one divisor-width. -/
theorem mulDivUp_mul_lt_add (a b c : Uint256)
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivUp a b c : Nat) * (c : Nat) < (a : Nat) * (b : Nat) + (c : Nat) := by
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  rw [mulDivUp_nat_eq a b c hC hNum]
  calc
    ((((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat)) * (c : Nat)
        ≤ ((a : Nat) * (b : Nat)) + ((c : Nat) - 1) := Nat.div_mul_le_self _ _
    _ < (a : Nat) * (b : Nat) + (c : Nat) := by
      exact Nat.add_lt_add_left (Nat.sub_lt (Nat.pos_of_ne_zero hCVal) (by decide)) _

/-- Ceil rounding never drops below the exact numerator product. -/
theorem mulDivUp_mul_ge (a b c : Uint256)
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (a : Nat) * (b : Nat) ≤ (mulDivUp a b c : Nat) * (c : Nat) := by
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  have hCPos : 0 < (c : Nat) := Nat.pos_of_ne_zero hCVal
  rw [mulDivUp_nat_eq a b c hC hNum]
  have hLift :
      (a : Nat) * (b : Nat) + ((c : Nat) - 1) ≤
        ((((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat)) * (c : Nat) + (c : Nat) - 1 := by
    exact (Nat.div_le_iff_le_mul hCPos).mp (Nat.le_refl _)
  omega

/-- Increasing the divisor can only decrease `mulDivUp` when both widened numerators are exact. -/
theorem mulDivUp_antitone_divisor (a b c₁ c₂ : Uint256)
    (hC : (c₁ : Nat) ≤ (c₂ : Nat))
    (hC₁ : c₁ ≠ 0)
    (hC₂ : c₂ ≠ 0)
    (hNum : (a : Nat) * (b : Nat) + ((c₂ : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivUp a b c₂ : Nat) ≤ (mulDivUp a b c₁ : Nat) := by
  have hNum₁ : (a : Nat) * (b : Nat) + ((c₁ : Nat) - 1) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.add_le_add_left (Nat.sub_le_sub_right hC 1) _) hNum
  have hUpper :
      (mulDivUp a b c₂ : Nat) * (c₂ : Nat) < (a : Nat) * (b : Nat) + (c₂ : Nat) :=
    mulDivUp_mul_lt_add a b c₂ hC₂ hNum
  have hLower :
      (a : Nat) * (b : Nat) ≤ (mulDivUp a b c₁ : Nat) * (c₂ : Nat) := by
    exact Nat.le_trans
      (mulDivUp_mul_ge a b c₁ hC₁ hNum₁)
      (Nat.mul_le_mul_left _ hC)
  have hLt :
      (mulDivUp a b c₂ : Nat) * (c₂ : Nat) <
        ((mulDivUp a b c₁ : Nat) + 1) * (c₂ : Nat) := by
    calc
      (mulDivUp a b c₂ : Nat) * (c₂ : Nat) < (a : Nat) * (b : Nat) + (c₂ : Nat) := hUpper
      _ ≤ (mulDivUp a b c₁ : Nat) * (c₂ : Nat) + (c₂ : Nat) := Nat.add_le_add_right hLower _
      _ = ((mulDivUp a b c₁ : Nat) + 1) * (c₂ : Nat) := by
            simp [Nat.right_distrib]
  have hLt' :
      (c₂ : Nat) * (mulDivUp a b c₂ : Nat) <
        (c₂ : Nat) * ((mulDivUp a b c₁ : Nat) + 1) := by
    simpa [Nat.mul_comm] using hLt
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left hLt')

/-- `wMulDown` is `mulDivDown` specialized to the canonical wad scale. -/
theorem wMulDown_nat_eq (a b : Uint256)
    (hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
    (wMulDown a b : Nat) = ((a : Nat) * (b : Nat)) / (WAD : Nat) := by
  rw [wMulDown_def, mulDivDown_nat_eq a b WAD hMul]
  simp [WAD_val]

/-- Wad multiplication inherits the generic floor bound. -/
theorem wMulDown_mul_le (a b : Uint256)
    (hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
    (wMulDown a b : Nat) * (WAD : Nat) ≤ (a : Nat) * (b : Nat) := by
  simpa [WAD_val] using mulDivDown_mul_le a b WAD hMul

/-- Wad multiplication is positive once the product reaches one full wad. -/
theorem wMulDown_pos (a b : Uint256)
    (hLower : (WAD : Nat) ≤ (a : Nat) * (b : Nat))
    (hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
    0 < (wMulDown a b : Nat) := by
  simpa [WAD_val] using mulDivDown_pos a b WAD WAD_ne_zero hLower hMul

/-- A zero left operand collapses `wMulDown` to zero. -/
theorem wMulDown_zero_left (b : Uint256) :
    (wMulDown 0 b : Nat) = 0 := by
  exact mulDivDown_zero_left b WAD

/-- A zero right operand collapses `wMulDown` to zero. -/
theorem wMulDown_zero_right (a : Uint256) :
    (wMulDown a 0 : Nat) = 0 := by
  exact mulDivDown_zero_right a WAD

/-- Multiplying by one wad on the right is the identity when the product stays exact. -/
theorem wMulDown_one_right (a : Uint256)
    (hMul : (a : Nat) * (WAD : Nat) ≤ MAX_UINT256) :
    (wMulDown a WAD : Nat) = (a : Nat) := by
  simpa [WAD_val] using mulDivDown_cancel_right a WAD WAD_ne_zero hMul

/-- Multiplying by one wad on the left is the identity when the product stays exact. -/
theorem wMulDown_one_left (a : Uint256)
    (hMul : (WAD : Nat) * (a : Nat) ≤ MAX_UINT256) :
    (wMulDown WAD a : Nat) = (a : Nat) := by
  simpa [WAD_val] using mulDivDown_cancel_left a WAD WAD_ne_zero hMul

/-- `wMulDown` is monotone in its left operand when the product stays exact. -/
theorem wMulDown_monotone_left (a₁ a₂ b : Uint256)
    (hA : (a₁ : Nat) ≤ (a₂ : Nat))
    (hMul : (a₂ : Nat) * (b : Nat) ≤ MAX_UINT256) :
    (wMulDown a₁ b : Nat) ≤ (wMulDown a₂ b : Nat) := by
  simpa [WAD_val] using mulDivDown_monotone_left a₁ a₂ b WAD hA hMul

/-- `wMulDown` is monotone in its right operand when the product stays exact. -/
theorem wMulDown_monotone_right (a b₁ b₂ : Uint256)
    (hB : (b₁ : Nat) ≤ (b₂ : Nat))
    (hMul : (a : Nat) * (b₂ : Nat) ≤ MAX_UINT256) :
    (wMulDown a b₁ : Nat) ≤ (wMulDown a b₂ : Nat) := by
  simpa [WAD_val] using mulDivDown_monotone_right a b₁ b₂ WAD hB hMul

/-- `wMulDown` is commutative in its operands. -/
theorem wMulDown_comm (a b : Uint256) :
    wMulDown a b = wMulDown b a := by
  simp [wMulDown_def]

/-- Wad multiplication undershoots the numerator by less than one wad-width. -/
theorem wMulDown_mul_lt_add (a b : Uint256)
    (hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
    (a : Nat) * (b : Nat) < (wMulDown a b : Nat) * (WAD : Nat) + (WAD : Nat) := by
  simpa [WAD_val] using mulDivDown_mul_lt_add a b WAD (by decide) hMul

/-- `wDivUp` is `mulDivUp` specialized to the canonical wad scale. -/
theorem wDivUp_nat_eq (a b : Uint256)
    (hB : b ≠ 0)
    (hNum : (a : Nat) * (WAD : Nat) + ((b : Nat) - 1) ≤ MAX_UINT256) :
    (wDivUp a b : Nat) = (((a : Nat) * (WAD : Nat)) + ((b : Nat) - 1)) / (b : Nat) := by
  rw [wDivUp_def, mulDivUp_nat_eq a WAD b hB hNum]

/-- `wDivUp` is monotone in its numerator when the widened numerator stays exact. -/
theorem wDivUp_monotone_left (a₁ a₂ b : Uint256)
    (hA : (a₁ : Nat) ≤ (a₂ : Nat))
    (hB : b ≠ 0)
    (hNum : (a₂ : Nat) * (WAD : Nat) + ((b : Nat) - 1) ≤ MAX_UINT256) :
    (wDivUp a₁ b : Nat) ≤ (wDivUp a₂ b : Nat) := by
  simpa [WAD_val] using mulDivUp_monotone_left a₁ a₂ WAD b hA hB hNum

/-- `wDivUp` is antitone in its divisor when the widened numerator stays exact. -/
theorem wDivUp_antitone_right (a b₁ b₂ : Uint256)
    (hB : (b₁ : Nat) ≤ (b₂ : Nat))
    (hB₁ : b₁ ≠ 0)
    (hB₂ : b₂ ≠ 0)
    (hNum : (a : Nat) * (WAD : Nat) + ((b₂ : Nat) - 1) ≤ MAX_UINT256) :
    (wDivUp a b₂ : Nat) ≤ (wDivUp a b₁ : Nat) := by
  simpa [WAD_val] using mulDivUp_antitone_divisor a WAD b₁ b₂ hB hB₁ hB₂ hNum

/-- Wad ceil-division overshoots the scaled numerator by less than one divisor-width. -/
theorem wDivUp_mul_lt_add (a b : Uint256)
    (hB : b ≠ 0)
    (hNum : (a : Nat) * (WAD : Nat) + ((b : Nat) - 1) ≤ MAX_UINT256) :
    (wDivUp a b : Nat) * (b : Nat) < (a : Nat) * (WAD : Nat) + (b : Nat) := by
  simpa [WAD_val] using mulDivUp_mul_lt_add a WAD b hB hNum

/-- Wad ceil-division never drops below the scaled numerator. -/
theorem wDivUp_mul_ge (a b : Uint256)
    (hB : b ≠ 0)
    (hNum : (a : Nat) * (WAD : Nat) + ((b : Nat) - 1) ≤ MAX_UINT256) :
    (a : Nat) * (WAD : Nat) ≤ (wDivUp a b : Nat) * (b : Nat) := by
  simpa [WAD_val] using mulDivUp_mul_ge a WAD b hB hNum

/-- Positive wad numerators yield a positive ceil-division result. -/
theorem wDivUp_pos (a b : Uint256)
    (hA : 0 < (a : Nat))
    (hB : b ≠ 0)
    (hNum : (a : Nat) * (WAD : Nat) + ((b : Nat) - 1) ≤ MAX_UINT256) :
    0 < (wDivUp a b : Nat) := by
  have hWadPos : 0 < (WAD : Nat) := by simp [WAD_val]
  simpa [WAD_val] using mulDivUp_pos a WAD b hA hWadPos hB hNum

/-- A zero wad numerator collapses `wDivUp` to zero. -/
theorem wDivUp_zero (b : Uint256)
    (hB : b ≠ 0) :
    (wDivUp 0 b : Nat) = 0 := by
  simpa [WAD_val] using mulDivUp_zero_left WAD b hB

/-- Dividing by one wad is the identity when the widened numerator stays exact. -/
theorem wDivUp_by_wad (a : Uint256)
    (hNum : (a : Nat) * (WAD : Nat) + ((WAD : Nat) - 1) ≤ MAX_UINT256) :
    (wDivUp a WAD : Nat) = (a : Nat) := by
  simpa [WAD_val] using mulDivUp_cancel_right a WAD WAD_ne_zero hNum

/-! ## ceilDiv Correctness -/

/-- ceilDiv of zero is zero. -/
theorem ceilDiv_zero_left (b : Uint256) :
    (ceilDiv 0 b : Nat) = 0 := by
  simp [ceilDiv]

/-- ceilDiv agrees with Nat ceiling division when there is no overflow.
    Key identity: for a > 0, b > 0: (a - 1) / b + 1 = (a + b - 1) / b. -/
theorem ceilDiv_nat_eq (a b : Uint256) (hB : b ≠ 0) :
    (ceilDiv a b : Nat) = ((a : Nat) + (b : Nat) - 1) / (b : Nat) := by
  have hBVal : (b : Nat) ≠ 0 := by
    intro h
    apply hB
    exact Verity.Core.Uint256.ext (by simpa using h)
  have hBPos : 0 < (b : Nat) := Nat.pos_of_ne_zero hBVal
  by_cases hA : (a : Nat) = 0
  · -- a = 0 case: ceilDiv 0 b = 0 and (0 + b - 1) / b = (b - 1) / b = 0
    have hAZ : a = 0 := Verity.Core.Uint256.ext (by simpa using hA)
    simp [ceilDiv, hAZ]
    have hSubLt : (b : Nat) - 1 < (b : Nat) := Nat.sub_lt hBPos (by decide)
    exact (Nat.div_eq_of_lt hSubLt).symm
  · -- a > 0 case
    have hAPos : 0 < (a : Nat) := Nat.pos_of_ne_zero hA
    have hANe : (a == 0) = false := by
      simp [BEq.beq]
      intro h
      exact hA (congrArg (fun x : Uint256 => x.val) h)
    have hOneLe : (1 : Nat) ≤ (a : Nat) := hAPos
    have hSub : ((a - 1 : Uint256) : Nat) = (a : Nat) - 1 :=
      Verity.Core.Uint256.sub_eq_of_le hOneLe
    have hDivLtMod : ((a : Nat) - 1) / (b : Nat) < Verity.Core.Uint256.modulus :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt)
    have hDivLt : ((a : Nat) - 1) / (b : Nat) + 1 < Verity.Core.Uint256.modulus :=
      Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt hAPos (by decide)))) a.isLt
    -- Prove ((a-1)/b : Uint256).val = (a.val-1)/b.val (Uint256 div matches Nat div here)
    have hDivEq : ((a - 1 : Uint256) / b : Uint256).val = ((a : Nat) - 1) / (b : Nat) := by
      -- Uint256.div is: if b.val = 0 then 0 else ofNat (a.val / b.val)
      -- After unfolding, since b ≠ 0, we get ofNat ((a-1).val / b.val) = ofNat ((a.val-1) / b.val)
      simp only [HDiv.hDiv, Verity.Core.Uint256.div]
      simp only [hBVal, ↓reduceIte, Verity.Core.Uint256.ofNat, hSub]
      exact Nat.mod_eq_of_lt hDivLtMod
    -- Prove ((a-1)/b + 1 : Uint256).val = (a.val-1)/b.val + 1
    have hAddLt : ((a - 1 : Uint256) / b).val + (1 : Uint256).val < Verity.Core.Uint256.modulus := by
      rw [hDivEq, Verity.Core.Uint256.val_one]; exact hDivLt
    have hCeilEq : ceilDiv a b = (a - 1) / b + 1 := by
      unfold ceilDiv; rw [hANe]; rfl
    rw [hCeilEq, Verity.Core.Uint256.add_eq_of_lt hAddLt, hDivEq, Verity.Core.Uint256.val_one]
    -- Now prove the Nat identity: (a - 1) / b + 1 = (a + b - 1) / b for a > 0, b > 0
    have hIdentity : ((a : Nat) - 1) / (b : Nat) + 1 = ((a : Nat) + (b : Nat) - 1) / (b : Nat) := by
      have key : (a : Nat) + (b : Nat) - 1 = ((a : Nat) - 1) + (b : Nat) := by omega
      rw [key, Nat.add_div_right _ hBPos]
    exact hIdentity

/-- Ceiling division times divisor is at least the dividend: ceilDiv(a,b) * b >= a.
    This is the key property for solvency proofs. -/
theorem ceilDiv_mul_ge (a b : Uint256) (hB : b ≠ 0)
    (hNoOverflow : (ceilDiv a b).val * b.val < Verity.Core.Uint256.modulus) :
    (a : Nat) ≤ (Verity.Core.Uint256.mul (ceilDiv a b) b : Nat) := by
  have hBVal : (b : Nat) ≠ 0 := by
    intro h
    apply hB
    exact Verity.Core.Uint256.ext (by simpa using h)
  have hBPos : 0 < (b : Nat) := Nat.pos_of_ne_zero hBVal
  have hMulExact : ((Verity.Core.Uint256.mul (ceilDiv a b) b : Uint256) : Nat) =
      (ceilDiv a b).val * b.val :=
    Verity.Core.Uint256.mul_eq_of_lt hNoOverflow
  rw [hMulExact]
  rw [ceilDiv_nat_eq a b hB]
  -- Goal: a.val ≤ ((a.val + b.val - 1) / b.val) * b.val
  -- From division: (a+b-1) = ((a+b-1)/b)*b + (a+b-1) mod b
  -- So ((a+b-1)/b)*b = (a+b-1) - (a+b-1) mod b ≥ a+b-1 - (b-1) = a
  have h1 := Nat.div_add_mod ((a : Nat) + (b : Nat) - 1) (b : Nat)
  rw [Nat.mul_comm] at h1
  have h2 := Nat.mod_lt ((a : Nat) + (b : Nat) - 1) hBPos
  omega

/-- ceilDiv is monotone: a >= b → ceilDiv a c >= ceilDiv b c -/
theorem ceilDiv_monotone (a b c : Uint256) (hAB : (a : Nat) ≥ (b : Nat)) (hC : c ≠ 0) :
    (ceilDiv a c : Nat) ≥ (ceilDiv b c : Nat) := by
  rw [ceilDiv_nat_eq a c hC, ceilDiv_nat_eq b c hC]
  exact Nat.div_le_div_right (by omega)

/-- ceilDiv result never exceeds the dividend when divisor >= 1 -/
theorem ceilDiv_le (a b : Uint256) (hB : b ≠ 0) :
    (ceilDiv a b : Nat) ≤ (a : Nat) := by
  have hBVal : (b : Nat) ≠ 0 := by
    intro h
    apply hB
    exact Verity.Core.Uint256.ext (by simpa using h)
  have hBPos : 0 < (b : Nat) := Nat.pos_of_ne_zero hBVal
  rw [ceilDiv_nat_eq a b hB]
  -- Goal: (a.val + b.val - 1) / b.val ≤ a.val
  -- Since b ≥ 1: (a + b - 1) / b ≤ (a + b - 1) / 1 = a + b - 1
  -- But we need a tighter bound. Key: (a + b - 1) / b = (a - 1) / b + 1 ≤ a - 1 + 1 = a (for a > 0)
  -- And for a = 0: (0 + b - 1) / b = (b - 1) / b = 0 ≤ 0
  by_cases hA : (a : Nat) = 0
  · rw [hA, Nat.zero_add]
    exact Nat.le_of_eq (Nat.div_eq_of_lt (by omega))
  · have hAPos : 0 < (a : Nat) := Nat.pos_of_ne_zero hA
    have key : (a : Nat) + (b : Nat) - 1 = ((a : Nat) - 1) + (b : Nat) := by omega
    rw [key, Nat.add_div_right _ hBPos]
    calc
      ((a : Nat) - 1) / (b : Nat) + 1
          ≤ ((a : Nat) - 1) + 1 := Nat.add_le_add_right (Nat.div_le_self _ _) _
      _ = (a : Nat) := by omega

/-! ## safeAdd Correctness -/

/-- safeAdd returns the sum when no overflow occurs. -/
theorem safeAdd_some (a b : Uint256) (h : (a : Nat) + (b : Nat) ≤ MAX_UINT256) :
  safeAdd a b = some (a + b) := by
  simp [safeAdd, Nat.not_lt.mpr h]

/-- safeAdd returns none on overflow. -/
theorem safeAdd_none (a b : Uint256) (h : (a : Nat) + (b : Nat) > MAX_UINT256) :
  safeAdd a b = none := by
  simp [safeAdd, h]

/-- safeAdd with zero on the left returns the other operand (when within bounds). -/
theorem safeAdd_zero_left (b : Uint256) (h : (b : Nat) ≤ MAX_UINT256) :
  safeAdd 0 b = some b := by
  simp [safeAdd, Nat.not_lt.mpr h]

/-- safeAdd with zero on the right returns the other operand (when within bounds). -/
theorem safeAdd_zero_right (a : Uint256) (h : (a : Nat) ≤ MAX_UINT256) :
  safeAdd a 0 = some a := by
  simp [safeAdd, Nat.not_lt.mpr h]

/-- safeAdd is commutative. -/
theorem safeAdd_comm (a b : Uint256) :
  safeAdd a b = safeAdd b a := by
  simp [safeAdd, Nat.add_comm]

/-- safeAdd result is always bounded by MAX_UINT256 when successful. -/
theorem safeAdd_result_bounded (a b : Uint256) (c : Uint256)
  (_h : safeAdd a b = some c) : c ≤ MAX_UINT256 :=
  Verity.Core.Uint256.val_le_max c

/-! ## safeSub Correctness -/

/-- safeSub returns the difference when no underflow occurs. -/
theorem safeSub_some (a b : Uint256) (h : (a : Nat) ≥ (b : Nat)) :
  safeSub a b = some (a - b) := by
  simp [safeSub, Nat.not_lt.mpr h]

/-- safeSub returns none on underflow. -/
theorem safeSub_none (a b : Uint256) (h : (b : Nat) > (a : Nat)) :
  safeSub a b = none := by
  simp [safeSub, h]

/-- safeSub of zero from any value is always safe. -/
theorem safeSub_zero (a : Uint256) :
  safeSub a 0 = some a := by
  simp [safeSub]

/-- safeSub of a value from itself returns zero. -/
theorem safeSub_self (a : Uint256) :
  safeSub a a = some 0 := by
  simp [safeSub]

/-- safeSub result never exceeds the minuend. -/
theorem safeSub_result_le (a b : Uint256) (c : Uint256)
  (h : safeSub a b = some c) : c ≤ a := by
  by_cases hlt : (b : Nat) > (a : Nat)
  · simp [safeSub, hlt] at h
  · have hle' : (b : Nat) ≤ (a : Nat) := Nat.not_lt.mp hlt
    simp [safeSub, hlt] at h
    have hc : a - b = c := by cases h; rfl
    have hsub : ((a - b : Uint256) : Nat) = (a : Nat) - (b : Nat) :=
      Verity.Core.Uint256.sub_eq_of_le hle'
    simp [hc.symm, hsub]

/-! ## safeMul Correctness -/

/-- safeMul returns the product when no overflow occurs. -/
theorem safeMul_some (a b : Uint256) (h : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
  safeMul a b = some (a * b) := by
  simp [safeMul, Nat.not_lt.mpr h]

/-- safeMul returns none on overflow. -/
theorem safeMul_none (a b : Uint256) (h : (a : Nat) * (b : Nat) > MAX_UINT256) :
  safeMul a b = none := by
  simp [safeMul, h]

/-- safeMul of zero is always safe and returns zero. -/
theorem safeMul_zero_left (b : Uint256) :
  safeMul 0 b = some 0 := by
  simp [safeMul]

/-- safeMul of zero is always safe and returns zero. -/
theorem safeMul_zero_right (a : Uint256) :
  safeMul a 0 = some 0 := by
  simp [safeMul]

/-- safeMul of one returns the other operand (when within bounds). -/
theorem safeMul_one_left (b : Uint256) (h : (b : Nat) ≤ MAX_UINT256) :
  safeMul 1 b = some b := by
  simp [safeMul, Nat.not_lt.mpr h]

/-- safeMul of one returns the other operand (when within bounds). -/
theorem safeMul_one_right (a : Uint256) (h : (a : Nat) ≤ MAX_UINT256) :
  safeMul a 1 = some a := by
  simp [safeMul, Nat.not_lt.mpr h]

/-- safeMul is commutative. -/
theorem safeMul_comm (a b : Uint256) :
  safeMul a b = safeMul b a := by
  simp [safeMul, Nat.mul_comm]

/-! ## safeDiv Correctness -/

/-- safeDiv returns the quotient when divisor is nonzero. -/
theorem safeDiv_some (a b : Uint256) (h : b ≠ 0) :
  safeDiv a b = some (a / b) := by
  have h_not : b.val ≠ 0 := fun hv => h (Verity.Core.Uint256.ext (by simp [Verity.Core.Uint256.val_zero, hv]))
  simp [safeDiv, h_not]

/-- safeDiv returns none when divisor is zero. -/
theorem safeDiv_none (a : Uint256) :
  safeDiv a 0 = none := by
  simp [safeDiv]

/-- safeDiv of zero always returns zero (when divisor is nonzero). -/
theorem safeDiv_zero_numerator (b : Uint256) (h : b ≠ 0) :
  safeDiv 0 b = some 0 := by
  have h_not : b.val ≠ 0 := fun hv => h (Verity.Core.Uint256.ext (by simp [Verity.Core.Uint256.val_zero, hv]))
  simp [safeDiv, h_not]

/-- safeDiv by one returns the numerator. -/
theorem safeDiv_by_one (a : Uint256) :
  safeDiv a 1 = some a := by
  simp [safeDiv]

/-- safeDiv of a value by itself returns 1 (when nonzero). -/
theorem safeDiv_self (a : Uint256) (h : a ≠ 0) :
  safeDiv a a = some 1 := by
  have h_not : a.val ≠ 0 := fun hv => h (Verity.Core.Uint256.ext (by simp [Verity.Core.Uint256.val_zero, hv]))
  have hpos : 0 < (a : Nat) := Nat.pos_of_ne_zero h_not
  have hlt : (1 : Nat) < Verity.Core.Uint256.modulus := by decide
  have hdiv : a / a = (1 : Uint256) := by
    apply Verity.Core.Uint256.ext
    calc (a / a).val
        = (a.val / a.val) % Verity.Core.Uint256.modulus := by
          simp [HDiv.hDiv, Verity.Core.Uint256.div, h_not, Verity.Core.Uint256.ofNat]
      _ = 1 % Verity.Core.Uint256.modulus := by simp [Nat.div_self hpos]
      _ = 1 := Nat.mod_eq_of_lt hlt
  simp [safeDiv, h_not, hdiv]

/-! ## Cross-Operation Properties -/

/-- safeMul result is always bounded by MAX_UINT256 when successful. -/
theorem safeMul_result_bounded (a b : Uint256) (c : Uint256)
  (_h : safeMul a b = some c) : c ≤ MAX_UINT256 :=
  Verity.Core.Uint256.val_le_max c

/-- safeDiv result never exceeds the numerator. -/
theorem safeDiv_result_le_numerator (a b : Uint256) (c : Uint256)
  (h_div : safeDiv a b = some c) : c ≤ a := by
  by_cases hzero : b.val = 0
  · simp [safeDiv, hzero] at h_div
  · simp [safeDiv, hzero] at h_div
    have hc : a / b = c := by cases h_div; rfl
    have hdiv_lt : (a : Nat) / (b : Nat) < Verity.Core.Uint256.modulus :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt
    have hdiv : ((a / b : Uint256) : Nat) = (a : Nat) / (b : Nat) := by
      simp only [HDiv.hDiv, Verity.Core.Uint256.div, hzero, Verity.Core.Uint256.ofNat, ↓reduceIte]
      exact Nat.mod_eq_of_lt hdiv_lt
    have hcval : (c : Nat) = (a : Nat) / (b : Nat) :=
      (hdiv.symm.trans (congrArg (fun x => x.val) hc)).symm
    simp only [Verity.Core.Uint256.le_def, hcval]
    exact Nat.div_le_self _ _

/-! ## Summary

All 25 theorems fully proven with zero sorry:

safeAdd:
1. safeAdd_some — returns sum when no overflow
2. safeAdd_none — returns none on overflow
3. safeAdd_zero_left — 0 + b = b when bounded
4. safeAdd_zero_right — a + 0 = a when bounded
5. safeAdd_comm — commutativity
6. safeAdd_result_bounded — successful result ≤ MAX_UINT256

safeSub:
7. safeSub_some — returns difference when no underflow
8. safeSub_none — returns none on underflow
9. safeSub_zero — a - 0 = a always safe
10. safeSub_self — a - a = 0 always safe
11. safeSub_result_le — result never exceeds minuend

safeMul:
12. safeMul_some — returns product when no overflow
13. safeMul_none — returns none on overflow
14. safeMul_zero_left — 0 * b = 0 always safe
15. safeMul_zero_right — a * 0 = 0 always safe
16. safeMul_one_left — 1 * b = b when bounded
17. safeMul_one_right — a * 1 = a when bounded
18. safeMul_comm — commutativity
19. safeMul_result_bounded — successful result ≤ MAX_UINT256

safeDiv:
20. safeDiv_some — returns quotient when divisor nonzero
21. safeDiv_none — returns none on division by zero
22. safeDiv_zero_numerator — 0 / b = 0
23. safeDiv_by_one — a / 1 = a
24. safeDiv_self — a / a = 1
25. safeDiv_result_le_numerator — result never exceeds numerator
-/

/-! ## Fixed-point Helper Summary

Full-precision mulDiv512 helpers:
- `mulDiv512Down?_some` / `mulDiv512Up?_some` — return exact natural quotients when they fit
- `mulDiv512Down?_none_of_zero_divisor` / `mulDiv512Up?_none_of_zero_divisor` — reject zero divisors
- `mulDiv512Down?_none_of_overflow` / `mulDiv512Up?_none_of_overflow` — reject overflowing quotients
- `mulDiv512Down?_eq_some_iff` / `mulDiv512Up?_eq_some_iff` — characterize successful results
- `mulDiv512Down?_isSome_iff` / `mulDiv512Up?_isSome_iff` — characterize fit conditions
- `mulDiv512Down?_isNone_iff` / `mulDiv512Up?_isNone_iff` — characterize rejection conditions
- `mulDiv512Down?_mul_le` / `mulDiv512Down?_lt_succ_mul` — floor sandwich bounds
- `mulDiv512Down?_mul_lt_add` / `mulDiv512Up?_mul_lt_add` — one-divisor error bounds
- `mulDiv512Up?_mul_ge` / `mulDiv512Up?_mul_le_add_pred` — ceil sandwich bounds
- `mulDiv512Down?_comm` / `mulDiv512Up?_comm` — numerator multiplication order does not matter
- `mulDiv512Down?_monotone_left/right` / `mulDiv512Up?_monotone_left/right` — numerator monotonicity
- `mulDiv512Down?_antitone_divisor` / `mulDiv512Up?_antitone_divisor` — divisor antitonicity
- `mulDiv512Down?_isSome_of_up_isSome` / `mulDiv512Up?_isNone_of_down_isNone` — ceil/floor success and rejection bridge
- `mulDiv512Down?_pos` / `mulDiv512Up?_pos` — positive full-precision results under nonzero-output conditions
- `mulDiv512Down?_zero_left/right` / `mulDiv512Up?_zero_left/right` — zero numerators collapse helpers
- `mulDiv512Down?_cancel_right/left` / `mulDiv512Up?_cancel_right/left` — exact same-denominator cancellation
- `mulDiv512Down?_wide_product_regression` / `mulDiv512Up?_wide_product_regression` — products may exceed 256 bits when quotients fit
- `mulDiv512Down?_final_overflow_regression` / `mulDiv512Up?_final_overflow_regression` — final quotients above `MAX_UINT256` are rejected
- `mulDiv512Up?_eq_down_of_dvd` / `mulDiv512Up?_some_succ_of_not_dvd` — ceil/floor divisibility shape
- `mulDiv512Down?_le_up` / `mulDiv512Up?_le_down_add_one` / `mulDiv512Up?_eq_down_or_succ` — ceil/floor one-step rounding boundary

26. mulDivDown_nat_eq — exact floor division when the numerator fits
27. mulDivDown_mul_le — floor result never overshoots the numerator
28. mulDivDown_pos — floor division is positive once the numerator reaches one divisor-width
29. mulDivDown_zero_left/right — zero numerators collapse floor helpers
30. mulDivDown_comm — numerator multiplication order does not matter
31. mulDivDown_cancel_right/left — exact factor cancellation for floor helpers
32. mulDivDown_mul_lt_add — floor undershoot is less than one divisor-width
33. mulDivDown_antitone_divisor — larger divisors can only shrink floor helpers
34. mulDivUp_nat_eq — exact ceil-style division when the widened numerator fits
35. mulDivDown_le_mulDivUp — ceil result never rounds below floor
36. mulDivUp_le_mulDivDown_add_one — ceil result is at most one step above floor
37. mulDivUp_eq_mulDivDown_or_succ — ceil/floor either match exactly or differ by one
38. mulDivUp_eq_mulDivDown_of_dvd — exact divisibility removes the ceil/floor gap
39. mulDivUp_eq_mulDivDown_add_one_of_not_dvd — non-divisibility forces the one-step ceil gap
40. mulDivUp_pos — ceil division is positive for positive numerator factors
41. mulDivUp_zero_left/right — zero numerators collapse ceil helpers
42. mulDivUp_comm — widened numerator multiplication order does not matter
43. mulDivUp_cancel_right/left — exact factor cancellation for ceil helpers
44. mulDivUp_antitone_divisor — larger divisors can only shrink ceil helpers
45. wMulDown_nat_eq — wad-multiply specialization of mulDivDown
46. wMulDown_pos — wad multiplication is positive once the product reaches one full wad
47. wMulDown_zero_left/right — zero operands collapse wad multiplication
48. wMulDown_one_left/right — wad-multiply identity lemmas
49. wMulDown_comm — wad multiplication order does not matter
50. wMulDown_mul_lt_add — wad floor undershoot is less than one wad-width
51. wDivUp_nat_eq — wad-divide specialization of mulDivUp
52. wDivUp_antitone_right — larger wad divisors can only shrink ceil helpers
53. wDivUp_pos — positive wad numerators yield a positive ceil-division result
54. wDivUp_zero — zero wad numerators collapse ceil helpers
55. wDivUp_by_wad — wad ceil-division identity lemma
-/

end Verity.Proofs.Stdlib.Math
