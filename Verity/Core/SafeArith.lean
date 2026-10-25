/-
  Verity 2.0 Safe-by-Construction Arithmetic (`SafeArith`)

  Unifies checked arithmetic in the `Contract` monad, explicit modular
  wrapping operators (`+%`, `-%`, `*%`), canonical sub-word invariants
  (`CanonicalWord`), and explicit narrowing primitives (`narrowChecked`,
  `truncateMask`).
-/

import Verity.Core

namespace Verity.Core.SafeArith

open Verity

/-! ## 1. Checked Arithmetic in the `Contract` Monad -/

/-- Checked addition on `Uint256`: reverts when `a.val + b.val ≥ 2 ^ 256`. -/
def checkedAdd (a b : Uint256) : Contract Uint256 :=
  fun s =>
    if a.val + b.val < 2 ^ 256 then
      .success (Uint256.add a b) s
    else
      .revert "SafeArith: addition overflow" s

/-- Checked subtraction on `Uint256`: reverts when `a.val < b.val`. -/
def checkedSub (a b : Uint256) : Contract Uint256 :=
  fun s =>
    if b.val ≤ a.val then
      .success (Uint256.sub a b) s
    else
      .revert "SafeArith: subtraction underflow" s

/-- Checked multiplication on `Uint256`: reverts when `a.val * b.val ≥ 2 ^ 256`. -/
def checkedMul (a b : Uint256) : Contract Uint256 :=
  fun s =>
    if a.val * b.val < 2 ^ 256 then
      .success (Uint256.mul a b) s
    else
      .revert "SafeArith: multiplication overflow" s

/-- Checked division on `Uint256`: reverts when `b.val = 0`. -/
def checkedDiv (a b : Uint256) : Contract Uint256 :=
  fun s =>
    if b.val = 0 then
      .revert "SafeArith: division by zero" s
    else
      .success (Uint256.div a b) s

/-- Checked modulo on `Uint256`: reverts when `b.val = 0`. -/
def checkedMod (a b : Uint256) : Contract Uint256 :=
  fun s =>
    if b.val = 0 then
      .revert "SafeArith: modulo by zero" s
    else
      .success (Uint256.mod a b) s

@[simp] theorem checkedAdd_run (a b : Uint256) (s : ContractState) :
    (checkedAdd a b).run s = checkedAdd a b s := by
  by_cases h : a.val + b.val < 2 ^ 256 <;> simp [checkedAdd, Contract.run, h]

@[simp] theorem checkedSub_run (a b : Uint256) (s : ContractState) :
    (checkedSub a b).run s = checkedSub a b s := by
  by_cases h : b.val ≤ a.val <;> simp [checkedSub, Contract.run, h]

@[simp] theorem checkedMul_run (a b : Uint256) (s : ContractState) :
    (checkedMul a b).run s = checkedMul a b s := by
  by_cases h : a.val * b.val < 2 ^ 256 <;> simp [checkedMul, Contract.run, h]

@[simp] theorem checkedDiv_run (a b : Uint256) (s : ContractState) :
    (checkedDiv a b).run s = checkedDiv a b s := by
  by_cases h : b.val = 0 <;> simp [checkedDiv, Contract.run, h]

@[simp] theorem checkedMod_run (a b : Uint256) (s : ContractState) :
    (checkedMod a b).run s = checkedMod a b s := by
  by_cases h : b.val = 0 <;> simp [checkedMod, Contract.run, h]

theorem checkedAdd_eq_success_iff (a b c : Uint256) (s s' : ContractState) :
    (checkedAdd a b).run s = .success c s' ↔
      a.val + b.val < 2 ^ 256 ∧ c = Uint256.add a b ∧ s' = s := by
  by_cases h : a.val + b.val < 2 ^ 256 <;> simp [checkedAdd, h, eq_comm]

theorem checkedSub_eq_success_iff (a b c : Uint256) (s s' : ContractState) :
    (checkedSub a b).run s = .success c s' ↔
      b.val ≤ a.val ∧ c = Uint256.sub a b ∧ s' = s := by
  by_cases h : b.val ≤ a.val <;> simp [checkedSub, h, eq_comm]

theorem checkedMul_eq_success_iff (a b c : Uint256) (s s' : ContractState) :
    (checkedMul a b).run s = .success c s' ↔
      a.val * b.val < 2 ^ 256 ∧ c = Uint256.mul a b ∧ s' = s := by
  by_cases h : a.val * b.val < 2 ^ 256 <;> simp [checkedMul, h, eq_comm]

theorem checkedDiv_eq_success_iff (a b c : Uint256) (s s' : ContractState) :
    (checkedDiv a b).run s = .success c s' ↔
      b.val ≠ 0 ∧ c = Uint256.div a b ∧ s' = s := by
  by_cases h : b.val = 0 <;> simp [checkedDiv, h, eq_comm]

theorem checkedMod_eq_success_iff (a b c : Uint256) (s s' : ContractState) :
    (checkedMod a b).run s = .success c s' ↔
      b.val ≠ 0 ∧ c = Uint256.mod a b ∧ s' = s := by
  by_cases h : b.val = 0 <;> simp [checkedMod, h, eq_comm]

@[simp] theorem checkedAdd_preserves_state (a b : Uint256) (s : ContractState) :
    ((checkedAdd a b).run s).snd = s := by
  by_cases h : a.val + b.val < 2 ^ 256 <;> simp [checkedAdd, h]

@[simp] theorem checkedSub_preserves_state (a b : Uint256) (s : ContractState) :
    ((checkedSub a b).run s).snd = s := by
  by_cases h : b.val ≤ a.val <;> simp [checkedSub, h]

@[simp] theorem checkedMul_preserves_state (a b : Uint256) (s : ContractState) :
    ((checkedMul a b).run s).snd = s := by
  by_cases h : a.val * b.val < 2 ^ 256 <;> simp [checkedMul, h]

@[simp] theorem checkedDiv_preserves_state (a b : Uint256) (s : ContractState) :
    ((checkedDiv a b).run s).snd = s := by
  by_cases h : b.val = 0 <;> simp [checkedDiv, h]

@[simp] theorem checkedMod_preserves_state (a b : Uint256) (s : ContractState) :
    ((checkedMod a b).run s).snd = s := by
  by_cases h : b.val = 0 <;> simp [checkedMod, h]

/-! ## 2. Explicit Modular Wrapping Arithmetic (`2 ^ 256`) -/

/-- Explicit modular wrapping addition modulo `2 ^ 256`. -/
def wrappingAdd (a b : Uint256) : Uint256 := Uint256.add a b

/-- Explicit modular wrapping subtraction modulo `2 ^ 256`. -/
def wrappingSub (a b : Uint256) : Uint256 := Uint256.sub a b

/-- Explicit modular wrapping multiplication modulo `2 ^ 256`. -/
def wrappingMul (a b : Uint256) : Uint256 := Uint256.mul a b

infixl:65 " +% " => wrappingAdd
infixl:65 " -% " => wrappingSub
infixl:70 " *% " => wrappingMul

@[simp] theorem wrappingAdd_comm (a b : Uint256) :
    wrappingAdd a b = wrappingAdd b a :=
  Uint256.add_comm a b

@[simp] theorem wrappingAdd_assoc (a b c : Uint256) :
    wrappingAdd (wrappingAdd a b) c = wrappingAdd a (wrappingAdd b c) :=
  Uint256.add_assoc a b c

@[simp] theorem wrappingAdd_zero (a : Uint256) :
    wrappingAdd a 0 = a :=
  Uint256.add_zero a

@[simp] theorem zero_wrappingAdd (a : Uint256) :
    wrappingAdd 0 a = a :=
  Uint256.zero_add a

@[simp] theorem wrappingMul_comm (a b : Uint256) :
    wrappingMul a b = wrappingMul b a :=
  Uint256.mul_comm a b

@[simp] theorem wrappingSub_self (a : Uint256) :
    wrappingSub a a = 0 :=
  Uint256.sub_self a

/-! ## 3. Canonical Sub-Word Invariant & Safe Narrowing -/

/-- A 256-bit word is canonical at width `bits` iff all bits at or above `bits` are zero. -/
def CanonicalWord (bits : Nat) (val : Uint256) : Prop :=
  val.val < 2 ^ bits

instance (bits : Nat) (val : Uint256) : Decidable (CanonicalWord bits val) :=
  inferInstanceAs (Decidable (val.val < 2 ^ bits))

/-- Checked narrowing in `Contract`: succeeds with `x` iff `x.val < 2 ^ bits`, else reverts. -/
def narrowChecked (bits : Nat) (x : Uint256) : Contract Uint256 :=
  fun s =>
    if x.val < 2 ^ bits then
      .success x s
    else
      .revert "SafeArith: narrowing overflow" s

/-- Explicit low-bit truncation mask (`x mod 2 ^ bits`). -/
def truncateMask (bits : Nat) (x : Uint256) : Uint256 :=
  Uint256.ofNat (x.val % (2 ^ bits))

@[simp] theorem narrowChecked_run (bits : Nat) (x : Uint256) (s : ContractState) :
    (narrowChecked bits x).run s = narrowChecked bits x s := by
  by_cases h : x.val < 2 ^ bits <;> simp [narrowChecked, Contract.run, h]

@[simp] theorem narrowChecked_preserves_state (bits : Nat) (x : Uint256) (s : ContractState) :
    ((narrowChecked bits x).run s).snd = s := by
  by_cases h : x.val < 2 ^ bits <;> simp [narrowChecked, h]

theorem narrowChecked_eq_success_iff (bits : Nat) (x y : Uint256) (s s' : ContractState) :
    (narrowChecked bits x).run s = .success y s' ↔
      CanonicalWord bits x ∧ y = x ∧ s' = s := by
  by_cases h : x.val < 2 ^ bits <;> simp [narrowChecked, CanonicalWord, h, eq_comm]

theorem narrowChecked_canonical_of_success {bits : Nat} {x y : Uint256} {s s' : ContractState} :
    (narrowChecked bits x).run s = .success y s' → CanonicalWord bits y := by
  intro h
  rw [narrowChecked_eq_success_iff] at h
  rcases h with ⟨hCan, rfl, -⟩
  exact hCan

@[simp] theorem truncateMask_val {bits : Nat} (hbits : bits ≤ 256) (x : Uint256) :
    (truncateMask bits x).val = x.val % (2 ^ bits) := by
  unfold truncateMask Uint256.ofNat
  have hlt : x.val % (2 ^ bits) < 2 ^ bits :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hle : 2 ^ bits ≤ Uint256.modulus :=
    Nat.pow_le_pow_right (by decide) hbits
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hle)

theorem truncateMask_canonical {bits : Nat} (hbits : bits ≤ 256) (x : Uint256) :
    CanonicalWord bits (truncateMask bits x) := by
  unfold CanonicalWord
  rw [truncateMask_val hbits]
  exact Nat.mod_lt _ (Nat.pow_pos (by decide))

/-! ## 4. Pure `Nat`-Level Checked U256 Arithmetic & `requireSome` Algebra -/

/-- Maximum `Uint256` value (`2 ^ 256 - 1`), re-exported in `SafeArith`. -/
abbrev MAX_UINT256 : Nat := Verity.Core.MAX_UINT256

/-- Pure `Nat`-level checked addition bounded by `MAX_UINT256`. -/
def checkedAddU256 (a b : Nat) : Option Nat :=
  if a + b ≤ MAX_UINT256 then some (a + b) else none

/-- Pure `Nat`-level checked subtraction (returns `none` on underflow `a < b`). -/
def checkedSubU256 (a b : Nat) : Option Nat :=
  if b ≤ a then some (a - b) else none

/-- Pure `Nat`-level checked multiplication bounded by `MAX_UINT256`. -/
def checkedMulU256 (a b : Nat) : Option Nat :=
  if a * b ≤ MAX_UINT256 then some (a * b) else none

/-- Pure `Nat`-level checked division (returns `none` when divisor `b = 0`). -/
def checkedDivU256 (a b : Nat) : Option Nat :=
  if b = 0 then none else some (a / b)

/-- Lift an `Option α` result into the `Contract` monad, reverting with `msg` on `none`. -/
def requireSome {α : Type} (opt : Option α) (msg : String := "SafeArith: arithmetic failure") :
    Contract α :=
  fun s =>
    match opt with
    | some v => .success v s
    | none => .revert msg s

theorem checkedAddU256_comm (a b : Nat) :
    checkedAddU256 a b = checkedAddU256 b a := by
  unfold checkedAddU256
  rw [Nat.add_comm]

@[simp] theorem checkedAddU256_zero_right (a : Nat) (ha : a ≤ MAX_UINT256) :
    checkedAddU256 a 0 = some a := by
  unfold checkedAddU256
  simp [ha]

@[simp] theorem checkedAddU256_zero_left (a : Nat) (ha : a ≤ MAX_UINT256) :
    checkedAddU256 0 a = some a := by
  unfold checkedAddU256
  simp [ha]

@[simp] theorem checkedSubU256_self (a : Nat) :
    checkedSubU256 a a = some 0 := by
  unfold checkedSubU256
  simp

@[simp] theorem checkedSubU256_zero (a : Nat) :
    checkedSubU256 a 0 = some a := by
  unfold checkedSubU256
  simp

theorem checkedMulU256_comm (a b : Nat) :
    checkedMulU256 a b = checkedMulU256 b a := by
  unfold checkedMulU256
  rw [Nat.mul_comm]

@[simp] theorem checkedMulU256_zero_right (a : Nat) :
    checkedMulU256 a 0 = some 0 := by
  unfold checkedMulU256
  simp

@[simp] theorem checkedMulU256_zero_left (a : Nat) :
    checkedMulU256 0 a = some 0 := by
  unfold checkedMulU256
  simp

@[simp] theorem checkedMulU256_one_right (a : Nat) (ha : a ≤ MAX_UINT256) :
    checkedMulU256 a 1 = some a := by
  unfold checkedMulU256
  simp [ha]

@[simp] theorem checkedMulU256_one_left (a : Nat) (ha : a ≤ MAX_UINT256) :
    checkedMulU256 1 a = some a := by
  unfold checkedMulU256
  simp [ha]

@[simp] theorem checkedDivU256_one_right (a : Nat) :
    checkedDivU256 a 1 = some a := by
  unfold checkedDivU256
  simp

theorem checkedAddU256_eq_some_iff (a b c : Nat) :
    checkedAddU256 a b = some c ↔ a + b ≤ MAX_UINT256 ∧ c = a + b := by
  by_cases h : a + b ≤ MAX_UINT256 <;> simp [checkedAddU256, h, eq_comm]

theorem checkedSubU256_eq_some_iff (a b c : Nat) :
    checkedSubU256 a b = some c ↔ b ≤ a ∧ c = a - b := by
  by_cases h : b ≤ a <;> simp [checkedSubU256, h, eq_comm]

theorem checkedMulU256_eq_some_iff (a b c : Nat) :
    checkedMulU256 a b = some c ↔ a * b ≤ MAX_UINT256 ∧ c = a * b := by
  by_cases h : a * b ≤ MAX_UINT256 <;> simp [checkedMulU256, h, eq_comm]

theorem checkedDivU256_eq_some_iff (a b c : Nat) :
    checkedDivU256 a b = some c ↔ b ≠ 0 ∧ c = a / b := by
  by_cases h : b = 0 <;> simp [checkedDivU256, h, eq_comm]

theorem checkedAddU256_mono_left {a₁ a₂ b c₁ c₂ : Nat} :
    a₁ ≤ a₂ →
    checkedAddU256 a₁ b = some c₁ →
    checkedAddU256 a₂ b = some c₂ →
    c₁ ≤ c₂ := by
  intro hle h₁ h₂
  rw [checkedAddU256_eq_some_iff] at h₁ h₂
  rcases h₁ with ⟨-, rfl⟩
  rcases h₂ with ⟨-, rfl⟩
  omega

theorem checkedSubU256_mono_left {a₁ a₂ b c₁ c₂ : Nat} :
    a₁ ≤ a₂ →
    checkedSubU256 a₁ b = some c₁ →
    checkedSubU256 a₂ b = some c₂ →
    c₁ ≤ c₂ := by
  intro hle h₁ h₂
  rw [checkedSubU256_eq_some_iff] at h₁ h₂
  rcases h₁ with ⟨-, rfl⟩
  rcases h₂ with ⟨-, rfl⟩
  omega

@[simp] theorem requireSome_some {α : Type} (v : α) (msg : String) (s : ContractState) :
    (requireSome (some v) msg).run s = .success v s := rfl

@[simp] theorem requireSome_none {α : Type} (msg : String) (s : ContractState) :
    (requireSome (none : Option α) msg).run s = .revert msg s := rfl

theorem requireSome_eq_success_iff {α : Type} (opt : Option α) (msg : String)
    (v : α) (s s' : ContractState) :
    (requireSome opt msg).run s = .success v s' ↔ opt = some v ∧ s' = s := by
  cases opt <;> simp [requireSome, Contract.run, eq_comm]

theorem checkedAdd_comm (a b : Uint256) :
    checkedAdd a b = checkedAdd b a := by
  funext s
  unfold checkedAdd
  have hAdd : Uint256.add a b = Uint256.add b a := Uint256.add_comm a b
  rw [Nat.add_comm a.val b.val, hAdd]

theorem checkedMul_comm (a b : Uint256) :
    checkedMul a b = checkedMul b a := by
  funext s
  unfold checkedMul
  have hMul : Uint256.mul a b = Uint256.mul b a := Uint256.mul_comm a b
  rw [Nat.mul_comm a.val b.val, hMul]

end Verity.Core.SafeArith
