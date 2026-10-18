/-
  Core Uint256 Operations

  This module provides arithmetic operations with EVM semantics:
  - All operations wrap at 2^256 (modular arithmetic)
  - Division and modulo by zero return 0 (matches EVM)
  - Provides overflow/underflow detection predicates

  These operations ensure semantic equivalence between EDSL
  verification and compiled EVM execution.
-/

namespace Verity.Core

-- EVM maximum value for uint256
def MAX_UINT256 : Nat := 2^256 - 1

-- 256-bit modulus
def UINT256_MODULUS : Nat := 2^256

structure Uint256 where
  val : Nat
  isLt : val < UINT256_MODULUS
  deriving DecidableEq

namespace Uint256

def modulus : Nat := UINT256_MODULUS

theorem modulus_pos : 0 < modulus := by
  have h2 : (0 : Nat) < (2 : Nat) := by decide
  have h : 0 < (2 : Nat) ^ 256 := Nat.pow_pos h2
  simp [modulus]
  exact h

theorem max_uint256_succ_eq_modulus : MAX_UINT256 + 1 = modulus := by
  have h2 : (0 : Nat) < (2 : Nat) := by decide
  have hle : 1 ≤ (2 ^ 256) := by
    exact Nat.succ_le_of_lt (Nat.pow_pos (a := 2) (n := 256) h2)
  have h : (2 ^ 256 - 1) + 1 = 2 ^ 256 := Nat.sub_add_cancel hle
  simp [MAX_UINT256, modulus, UINT256_MODULUS, h]

theorem val_le_max (a : Uint256) : a.val ≤ MAX_UINT256 := by
  have hlt : a.val < modulus := a.isLt
  have hlt' : a.val < MAX_UINT256 + 1 := by
    calc
      a.val < modulus := hlt
      _ = MAX_UINT256 + 1 := by
        symm
        exact max_uint256_succ_eq_modulus
  exact Nat.lt_succ_iff.mp hlt'

def ofNat (n : Nat) : Uint256 :=
  ⟨n % modulus, Nat.mod_lt _ modulus_pos⟩

instance : OfNat Uint256 n := ⟨ofNat n⟩
instance : Inhabited Uint256 := ⟨ofNat 0⟩
instance : Repr Uint256 := ⟨fun u _ => repr u.val⟩
instance : Coe Uint256 Nat := ⟨Uint256.val⟩
instance : Coe Nat Uint256 := ⟨ofNat⟩
instance : BEq Uint256 := ⟨fun a b => decide (a = b)⟩

instance : LawfulBEq Uint256 where
  eq_of_beq {a b} h := by
    simp only [BEq.beq] at h
    exact of_decide_eq_true h
  rfl {a} := by
    show decide (a = a) = true
    exact decide_eq_true rfl

@[simp] theorem val_ofNat (n : Nat) : (ofNat n).val = n % modulus := rfl
@[simp] theorem coe_ofNat (n : Nat) : ((ofNat n : Uint256) : Nat) = n % modulus := rfl

@[simp] theorem val_zero : (0 : Uint256).val = 0 := by
  change (ofNat 0).val = 0
  simp [ofNat]

@[simp] theorem ofNat_zero : ofNat 0 = (0 : Uint256) := rfl

@[simp] theorem ofNat_one : ofNat 1 = (1 : Uint256) := rfl

@[simp] theorem val_one : (1 : Uint256).val = 1 := by
  change (ofNat 1).val = 1
  have hlt : (1 : Nat) < modulus := by
    dsimp [modulus, UINT256_MODULUS]
    decide
  simp [ofNat, Nat.mod_eq_of_lt hlt]
@[simp] theorem val_ite {c : Prop} [Decidable c] (t e : Uint256) :
  (ite c t e).val = ite c t.val e.val := by
  by_cases c <;> simp [*]

-- Order instances
instance : LT Uint256 := ⟨fun a b => a.val < b.val⟩
instance : LE Uint256 := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : Uint256) : Decidable (a < b) := by
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      change Decidable (a < b)
      exact inferInstance
instance (a b : Uint256) : Decidable (a ≤ b) := by
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      change Decidable (a ≤ b)
      exact inferInstance

@[simp] theorem le_def (a b : Uint256) : (a ≤ b) = (a.val ≤ b.val) := rfl
@[simp] theorem lt_def (a b : Uint256) : (a < b) = (a.val < b.val) := rfl

-- Modular addition (wraps at 2^256)
def add (a b : Uint256) : Uint256 := ofNat (a.val + b.val)

-- Modular subtraction (two's complement wrapping)
def sub (a b : Uint256) : Uint256 :=
  if b.val ≤ a.val then
    ofNat (a.val - b.val)
  else
    ofNat (modulus - (b.val - a.val))

-- Modular multiplication (wraps at 2^256)
def mul (a b : Uint256) : Uint256 := ofNat (a.val * b.val)

/-- EVM EXP semantics: exponentiation modulo `2^256`. -/
def pow (base exponent : Uint256) : Uint256 := ofNat (base.val ^ exponent.val)

/-- Binary exponentiation over `Uint256`; accumulates `acc * base ^ exp` modulo
    `2^256` without materializing `Nat.pow`. -/
def powBySquaring (acc base : Uint256) (exp : Nat) : Uint256 :=
  match exp with
  | 0 => acc
  | n + 1 =>
    if (n + 1) % 2 = 1 then
      powBySquaring (mul acc base) (mul base base) ((n + 1) / 2)
    else
      powBySquaring acc (mul base base) ((n + 1) / 2)
termination_by exp

private theorem mul_val (a b : Uint256) : (mul a b).val = (a.val * b.val) % modulus := by
  simp [mul, ofNat]

private theorem mod_mul_pow_mod (a b k m : Nat) :
    (a % m * (b % m) ^ k) % m = (a * b ^ k) % m := by
  rw [Nat.mul_mod (a % m) ((b % m) ^ k) m, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod]

private theorem mul_pow_mod (a b k m : Nat) :
    (a * (b % m) ^ k) % m = (a * b ^ k) % m := by
  rw [Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]

theorem powBySquaring_val (acc base : Uint256) (n : Nat) :
    (powBySquaring acc base n).val = (acc.val * base.val ^ n) % modulus := by
  induction n using Nat.strongRecOn generalizing acc base with
  | _ n ih =>
    match n with
    | 0 =>
      simp only [powBySquaring, Nat.pow_zero, Nat.mul_one]
      exact (Nat.mod_eq_of_lt acc.isLt).symm
    | (k + 1) =>
      have hlt : (k + 1) / 2 < k + 1 := Nat.div_lt_self (Nat.succ_pos k) (by omega)
      unfold powBySquaring
      split
      · rename_i hodd
        rw [ih _ hlt, mul_val, mul_val, mod_mul_pow_mod]
        congr 1
        rw [Nat.mul_assoc, Nat.mul_comm base.val ((base.val * base.val) ^ _)]
        congr 1
        rw [show base.val * base.val = base.val ^ 2 from by rw [Nat.pow_succ, Nat.pow_one],
            ← Nat.pow_mul, ← Nat.pow_succ]
        congr 1; omega
      · rename_i heven
        rw [ih _ hlt, mul_val, mul_pow_mod]
        congr 1; congr 1
        rw [show base.val * base.val = base.val ^ 2 from by rw [Nat.pow_succ, Nat.pow_one],
            ← Nat.pow_mul]
        congr 1; omega

/-- `powEff` computes the same result as `pow` using binary exponentiation. -/
def powEff (base exponent : Uint256) : Uint256 :=
  powBySquaring (ofNat 1) base exponent.val

private theorem val_injective {a b : Uint256} (h : a.val = b.val) : a = b := by
  cases a with | mk av ah => cases b with | mk bv bh => simp_all

theorem powEff_eq_pow (base exponent : Uint256) :
    powEff base exponent = pow base exponent :=
  val_injective (by simp [powEff, powBySquaring_val, pow, ofNat])

-- Division (returns 0 on division by zero, matching EVM)
def div (a b : Uint256) : Uint256 :=
  if b.val = 0 then ofNat 0 else ofNat (a.val / b.val)

-- Modulo (returns 0 on mod by zero, matching EVM)
def mod (a b : Uint256) : Uint256 :=
  if b.val = 0 then ofNat 0 else ofNat (a.val % b.val)

-- Bitwise operations (EVM semantics)
def and (a b : Uint256) : Uint256 := ofNat (Nat.land a.val b.val)
def or (a b : Uint256) : Uint256 := ofNat (Nat.lor a.val b.val)
def xor (a b : Uint256) : Uint256 := ofNat (Nat.xor a.val b.val)
def not (a : Uint256) : Uint256 := ofNat (MAX_UINT256 - a.val)

-- Shifts (EVM semantics: shl(shift, value) computes value << shift)
-- To match EVM convention, we put shift first
def shl (shift value : Uint256) : Uint256 := ofNat (value.val <<< shift.val)
def shr (shift value : Uint256) : Uint256 := ofNat (value.val >>> shift.val)

-- EVM BYTE(i, x): extract byte i from x, where byte 0 is most significant.
def byte (index value : Uint256) : Uint256 :=
  if index.val > 31 then
    ofNat 0
  else
    ofNat ((value.val >>> ((31 - index.val) * 8)) &&& 0xff)

-- EVM SIGNEXTEND(b, x): extend sign bit at byte position b
def signextend (byteIdx value : Uint256) : Uint256 :=
  let b := byteIdx.val
  if b ≥ 31 then value
  else
    let bitPos := b * 8 + 7
    let mask := 2 ^ (bitPos + 1) - 1
    if value.val &&& (2 ^ bitPos) ≠ 0 then
      ofNat (value.val ||| (modulus - 1 - mask))
    else
      ofNat (value.val &&& mask)

/-- Checked addition: `some` of the exact sum when it fits, `none` on
overflow — the semantic counterpart of solc-0.8 checked `+` (#1993). -/
def checkedAdd (a b : Uint256) : Option Uint256 :=
  if h : a.val + b.val < modulus then some ⟨a.val + b.val, h⟩ else none

/-- A successful checked addition is the wrapping addition, and its value is
the exact Nat sum — no wrap occurred. -/
theorem checkedAdd_eq_some {a b c : Uint256}
    (h : checkedAdd a b = some c) :
    c = add a b ∧ c.val = a.val + b.val := by
  unfold checkedAdd at h
  split at h
  · rename_i hlt
    obtain rfl := Option.some.inj h
    exact ⟨by simp [add, ofNat, Nat.mod_eq_of_lt hlt], rfl⟩
  · cases h

/-- Checked addition fails exactly on overflow. -/
theorem checkedAdd_eq_none_iff (a b : Uint256) :
    checkedAdd a b = none ↔ modulus ≤ a.val + b.val := by
  unfold checkedAdd
  split <;> rename_i hlt
  · simp
    omega
  · simp
    omega

/-- Non-overflowing addition is exact: the wrapped sum's value is the Nat
sum. -/
theorem addNoWrap {a b : Uint256} (h : a.val + b.val < modulus) :
    (add a b).val = a.val + b.val := by
  simp [add, ofNat, Nat.mod_eq_of_lt h]

/-- Checked subtraction: `some` of the exact difference when `b ≤ a`, `none`
on underflow — the semantic counterpart of solc-0.8 checked `-` (#1993). -/
def checkedSub (a b : Uint256) : Option Uint256 :=
  if b.val ≤ a.val then
    some ⟨a.val - b.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt⟩
  else none

/-- A successful checked subtraction is the wrapping subtraction, and its
value is the exact Nat difference — no wrap occurred. -/
theorem checkedSub_eq_some {a b c : Uint256}
    (h : checkedSub a b = some c) :
    c = sub a b ∧ c.val = a.val - b.val := by
  unfold checkedSub at h
  split at h
  · rename_i hle
    obtain rfl := Option.some.inj h
    have hlt : a.val - b.val < modulus :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
    exact ⟨by simp [sub, hle, ofNat, Nat.mod_eq_of_lt hlt], rfl⟩
  · cases h

/-- Checked subtraction fails exactly on underflow. -/
theorem checkedSub_eq_none_iff (a b : Uint256) :
    checkedSub a b = none ↔ a.val < b.val := by
  unfold checkedSub
  split <;> rename_i hle <;> simp <;> omega

/-- Non-underflowing subtraction is exact: the wrapped difference's value is
the Nat difference. -/
theorem subNoWrap {a b : Uint256} (h : b.val ≤ a.val) :
    (sub a b).val = a.val - b.val := by
  have hlt : a.val - b.val < modulus :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
  simp [sub, h, ofNat, Nat.mod_eq_of_lt hlt]

/-- Checked multiplication: `some` of the exact product when it fits, `none`
on overflow — the semantic counterpart of solc-0.8 checked `*` (#1993). -/
def checkedMul (a b : Uint256) : Option Uint256 :=
  if h : a.val * b.val < modulus then some ⟨a.val * b.val, h⟩ else none

/-- A successful checked multiplication is the wrapping multiplication, and
its value is the exact Nat product — no wrap occurred. -/
theorem checkedMul_eq_some {a b c : Uint256}
    (h : checkedMul a b = some c) :
    c = mul a b ∧ c.val = a.val * b.val := by
  unfold checkedMul at h
  split at h
  · rename_i hlt
    obtain rfl := Option.some.inj h
    exact ⟨by simp [mul, ofNat, Nat.mod_eq_of_lt hlt], rfl⟩
  · cases h

/-- Checked multiplication fails exactly on overflow. -/
theorem checkedMul_eq_none_iff (a b : Uint256) :
    checkedMul a b = none ↔ modulus ≤ a.val * b.val := by
  unfold checkedMul
  split <;> rename_i hlt <;> simp <;> omega

/-- Non-overflowing multiplication is exact: the wrapped product's value is
the Nat product. -/
theorem mulNoWrap {a b : Uint256} (h : a.val * b.val < modulus) :
    (mul a b).val = a.val * b.val := by
  simp [mul, ofNat, Nat.mod_eq_of_lt h]

-- Overflow detection predicates for safety proofs (on raw Nat values)
def willAddOverflow (a b : Uint256) : Bool :=
  a.val + b.val ≥ modulus

def willSubUnderflow (a b : Uint256) : Bool :=
  b.val > a.val

def willMulOverflow (a b : Uint256) : Bool :=
  a.val * b.val ≥ modulus

-- Instances for infix operators
instance : HAdd Uint256 Uint256 Uint256 := ⟨add⟩
instance : HSub Uint256 Uint256 Uint256 := ⟨sub⟩
instance : HMul Uint256 Uint256 Uint256 := ⟨mul⟩
instance : HPow Uint256 Uint256 Uint256 := ⟨pow⟩
instance : HDiv Uint256 Uint256 Uint256 := ⟨div⟩
instance : HMod Uint256 Uint256 Uint256 := ⟨mod⟩
instance : Add Uint256 := ⟨add⟩
instance : Sub Uint256 := ⟨sub⟩
instance : Mul Uint256 := ⟨mul⟩
instance : Pow Uint256 Uint256 := ⟨pow⟩
instance : Div Uint256 := ⟨div⟩
instance : Mod Uint256 := ⟨mod⟩

-- Lemmas for modular arithmetic reasoning when no overflow/underflow occurs.

theorem add_eq_of_lt {a b : Uint256} (h : a.val + b.val < modulus) :
  ((a + b : Uint256) : Nat) = a.val + b.val := by
  simp [HAdd.hAdd, add, ofNat]
  exact Nat.mod_eq_of_lt h

theorem mul_eq_of_lt {a b : Uint256} (h : a.val * b.val < modulus) :
  ((a * b : Uint256) : Nat) = a.val * b.val := by
  simp [HMul.hMul, mul, ofNat]
  exact Nat.mod_eq_of_lt h

theorem pow_eq_of_lt {a b : Uint256} (h : a.val ^ b.val < modulus) :
  ((a ^ b : Uint256) : Nat) = a.val ^ b.val := by
  simp [HPow.hPow, Pow.pow, pow, ofNat]
  exact Nat.mod_eq_of_lt h

theorem sub_eq_of_le {a b : Uint256} (h : b.val ≤ a.val) :
  ((a - b : Uint256) : Nat) = a.val - b.val := by
  have hlt : a.val - b.val < modulus := by
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
  simp [HSub.hSub, sub, h, ofNat]
  exact Nat.mod_eq_of_lt hlt

theorem sub_val_of_gt {a b : Uint256} (h : b.val > a.val) :
  (sub a b).val = (modulus - (b.val - a.val)) % modulus := by
  have h' : ¬ b.val ≤ a.val := Nat.not_le_of_gt h
  simp [sub, h', ofNat]

@[ext] theorem ext {a b : Uint256} (h : a.val = b.val) : a = b := by
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      cases h
      have : ha = hb := by
        apply Subsingleton.elim
      cases this
      rfl

@[simp] theorem ofNat_add (a b : Nat) : ofNat (a + b) = (ofNat a) + (ofNat b) := by
  apply ext
  simp [HAdd.hAdd, add, ofNat]
  exact Nat.add_mod a b modulus

@[simp] theorem zero_add (a : Uint256) : (0 : Uint256) + a = a := by
  apply ext
  have hlt : a.val < modulus := a.isLt
  have hlt' : 0 + a.val < modulus := by
    simp [Nat.zero_add]
    exact hlt
  calc
    ((0 : Uint256) + a).val = (0 + a.val) % modulus := by
      simp [HAdd.hAdd, add, ofNat]
    _ = 0 + a.val := by
      exact Nat.mod_eq_of_lt hlt'
    _ = a.val := by simp

@[simp] theorem add_zero (a : Uint256) : a + (0 : Uint256) = a := by
  apply ext
  have hlt : a.val < modulus := a.isLt
  have hlt' : a.val + 0 < modulus := by
    simp [Nat.add_zero]
    exact hlt
  calc
    (a + (0 : Uint256)).val = (a.val + 0) % modulus := by
      simp [HAdd.hAdd, add, ofNat]
    _ = a.val + 0 := by
      exact Nat.mod_eq_of_lt hlt'
    _ = a.val := by simp

@[simp] theorem add_comm (a b : Uint256) : a + b = b + a := by
  apply ext
  calc
    (a + b).val = (a.val + b.val) % modulus := by
      simp [HAdd.hAdd, add, ofNat]
    _ = (b.val + a.val) % modulus := by
      simp [Nat.add_comm]
    _ = (b + a).val := by
      simp [HAdd.hAdd, add, ofNat]

@[simp] theorem add_assoc (a b c : Uint256) : (a + b) + c = a + (b + c) := by
  apply ext
  let m : Nat := modulus
  have hmod_c : c.val % m = c.val := Nat.mod_eq_of_lt (by
    simp [m]
    exact c.isLt)
  have hmod_a : a.val % m = a.val := Nat.mod_eq_of_lt (by
    simp [m]
    exact a.isLt)
  calc
    ((a + b) + c).val
        = (((a.val + b.val) % m) + c.val) % m := by
            simp [HAdd.hAdd, add, ofNat, m]
    _ = ((a.val + b.val) + c.val) % m := by
            -- Normalize through add_mod
            simp [Nat.add_mod, hmod_c]
    _ = (a.val + b.val + c.val) % m := by
            simp [Nat.add_assoc]
    _ = (a.val + (b.val + c.val)) % m := by
            simp [Nat.add_assoc]
    _ = ((a.val % m) + ((b.val + c.val) % m)) % m := by
            -- Reverse add_mod
            exact (Nat.add_mod a.val (b.val + c.val) m)
    _ = (a.val + ((b.val + c.val) % m)) % m := by
            simp [hmod_a]
    _ = (a + (b + c)).val := by
            simp [HAdd.hAdd, add, ofNat, m]

@[simp] theorem add_left_comm (a b c : Uint256) : a + b + c = b + a + c := by
  calc
    a + b + c = (a + b) + c := rfl
    _ = (b + a) + c := by simp [add_comm]
    _ = b + a + c := rfl


@[simp] theorem sub_zero (a : Uint256) : a - (0 : Uint256) = a := by
  apply ext
  have hlt : a.val < modulus := a.isLt
  have hlt' : a.val - 0 < modulus := by
    simp [Nat.sub_zero]
    exact hlt
  calc
    (a - (0 : Uint256)).val = (a.val - 0) % modulus := by
      simp [HSub.hSub, sub]
    _ = a.val - 0 := by
      exact Nat.mod_eq_of_lt hlt'
    _ = a.val := by simp

@[simp] theorem sub_self (a : Uint256) : a - a = 0 := by
  apply ext
  calc
    (a - a).val = (a.val - a.val) % modulus := by
      simp [HSub.hSub, sub]
    _ = 0 := by simp

@[simp] theorem zero_mul (a : Uint256) : (0 : Uint256) * a = 0 := by
  apply ext
  calc
    ((0 : Uint256) * a).val = (0 * a.val) % modulus := by
      simp [HMul.hMul, mul, ofNat]
    _ = 0 := by simp

@[simp] theorem mul_zero (a : Uint256) : a * (0 : Uint256) = 0 := by
  apply ext
  calc
    (a * (0 : Uint256)).val = (a.val * 0) % modulus := by
      simp [HMul.hMul, mul, ofNat]
    _ = 0 := by simp

@[simp] theorem one_mul (a : Uint256) : (1 : Uint256) * a = a := by
  apply ext
  have hlt : a.val < modulus := a.isLt
  have hlt' : 1 * a.val < modulus := by
    simp [Nat.one_mul]
    exact hlt
  calc
    ((1 : Uint256) * a).val = (1 * a.val) % modulus := by
      simp [HMul.hMul, mul, ofNat]
    _ = 1 * a.val := by
      exact Nat.mod_eq_of_lt hlt'
    _ = a.val := by simp

@[simp] theorem mul_one (a : Uint256) : a * (1 : Uint256) = a := by
  apply ext
  have hlt : a.val < modulus := a.isLt
  have hlt' : a.val * 1 < modulus := by
    simp [Nat.mul_one]
    exact hlt
  calc
    (a * (1 : Uint256)).val = (a.val * 1) % modulus := by
      simp [HMul.hMul, mul, ofNat]
    _ = a.val * 1 := by
      exact Nat.mod_eq_of_lt hlt'
    _ = a.val := by simp

@[simp] theorem mul_comm (a b : Uint256) : a * b = b * a := by
  apply ext
  calc
    (a * b).val = (a.val * b.val) % modulus := by
      simp [HMul.hMul, mul, ofNat]
    _ = (b.val * a.val) % modulus := by
      simp [Nat.mul_comm]
    _ = (b * a).val := by
      simp [HMul.hMul, mul, ofNat]

@[simp] theorem add_mul (a b c : Uint256) : (a + b) * c = a * c + b * c := by
  apply ext
  let m : Nat := modulus
  calc
    ((a + b) * c).val
        = (((a.val + b.val) % m) * c.val) % m := by
            simp [HMul.hMul, HAdd.hAdd, add, mul, ofNat, m]
    _ = ((a.val + b.val) * c.val) % m := by
            -- drop the inner mod on the left factor
            simp [m]
    _ = (a.val * c.val + b.val * c.val) % m := by
            simp [Nat.add_mul]
    _ = (((a.val * c.val) % m) + ((b.val * c.val) % m)) % m := by
            -- expand with add_mod
            exact (Nat.add_mod (a.val * c.val) (b.val * c.val) m)
    _ = (a * c + b * c).val := by
            simp [HMul.hMul, HAdd.hAdd, add, mul, ofNat, m]

/-- Wrapping subtraction as a single modular expression. -/
private theorem sub_val_eq_mod (a b : Uint256) :
    (a - b).val = (a.val + (modulus - b.val)) % modulus := by
  have hb : b.val < modulus := b.isLt
  show (sub a b).val = _
  by_cases h : b.val ≤ a.val
  · have hsum : a.val + (modulus - b.val) = (a.val - b.val) + modulus := by omega
    simp only [sub, h, if_true, ofNat]
    rw [hsum, Nat.add_mod_right]
  · have hsum : a.val + (modulus - b.val) = modulus - (b.val - a.val) := by omega
    simp only [sub, h, if_false, ofNat]
    rw [hsum]

@[simp] theorem sub_add_cancel_left (a b : Uint256) : (a - b) + b = a := by
  apply ext
  have hb : b.val < modulus := b.isLt
  have hsum : a.val + (modulus - b.val) + b.val = a.val + modulus := by omega
  show ((a - b).val + b.val) % modulus = a.val
  rw [sub_val_eq_mod, Nat.mod_add_mod, hsum, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt a.isLt

@[simp] theorem div_one (a : Uint256) : a / (1 : Uint256) = a := by
  apply ext
  have hlt : a.val < modulus := a.isLt
  have hlt' : a.val / 1 < modulus := by
    simp [Nat.div_one]
    exact hlt
  calc
    (a / (1 : Uint256)).val = (a.val / 1) % modulus := by
      simp [HDiv.hDiv, div, ofNat]
    _ = a.val / 1 := by
      exact Nat.mod_eq_of_lt hlt'
    _ = a.val := by simp

@[simp] theorem zero_div (a : Uint256) : (0 : Uint256) / a = 0 := by
  apply ext
  by_cases h : a.val = 0
  · simp [HDiv.hDiv, div, h]
  · calc
      ((0 : Uint256) / a).val = (0 / a.val) % modulus := by
        simp [HDiv.hDiv, div, h, ofNat]
      _ = 0 := by simp

theorem sub_add_cancel_of_lt {a b : Uint256} (ha : a.val < modulus) (hb : b.val < modulus) :
  (a + b - b) = a := by
  apply ext
  have hsum : a.val + b.val + (modulus - b.val) = a.val + modulus := by omega
  rw [sub_val_eq_mod]
  show ((a.val + b.val) % modulus + (modulus - b.val)) % modulus = a.val
  rw [Nat.mod_add_mod, hsum, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt ha

theorem sub_add_cancel (a b : Uint256) : (a + b - b) = a :=
  sub_add_cancel_of_lt a.isLt b.isLt

theorem add_right_cancel {a b c : Uint256} (h : a + c = b + c) : a = b := by
  calc
    a = a + c - c := by
          symm
          exact (sub_add_cancel a c)
    _ = b + c - c := by simp [h]
    _ = b := by
          exact (sub_add_cancel b c)

end Uint256

end Verity.Core
