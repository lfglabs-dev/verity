/-
  Verity 2.0 Structurally Bounded Loop Combinators (`BoundedLoops`)

  Provides total, fuel/count-bounded loop combinators inside the `Contract`
  monad (`0 partial def`), together with meta-theorems for invariant and
  frame preservation.
-/

import Verity.Core

namespace Verity.Core.BoundedLoops

open Verity

@[simp] theorem run_eq_success_iff {α : Type} (c : Contract α) (s s' : ContractState) (v : α) :
    c.run s = .success v s' ↔ c s = .success v s' := by
  unfold Contract.run
  cases c s <;> simp

/-- Monadic bind success characterization for `Contract.run`. -/
theorem bind_run_eq_success_iff {α β : Type} (ma : Contract α) (f : α → Contract β)
    (s s'' : ContractState) (b : β) :
    (Verity.bind ma f).run s = .success b s'' ↔
      ∃ a s', ma.run s = .success a s' ∧ (f a).run s' = .success b s'' := by
  simp only [run_eq_success_iff, Verity.bind]
  cases hma : ma s with
  | success a s' =>
    constructor
    · intro h
      exact ⟨a, s', rfl, h⟩
    · rintro ⟨a', s₁, h1, h2⟩
      injection h1 with ha hs
      subst ha hs
      exact h2
  | revert msg s' =>
    simp

/-! ## 1. `forEachRange` -/

/-- Execute `body (start + k)` for `k = 0, ..., count - 1` sequentially in `Contract`. -/
def forEachRange (start count : Nat) (body : Nat → Contract Unit) : Contract Unit :=
  match count with
  | 0 => Verity.pure ()
  | n + 1 => Verity.bind (body start) (fun _ => forEachRange (start + 1) n body)

@[simp] theorem forEachRange_zero (start : Nat) (body : Nat → Contract Unit) :
    forEachRange start 0 body = Verity.pure () := rfl

@[simp] theorem forEachRange_succ (start count : Nat) (body : Nat → Contract Unit) :
    forEachRange start (count + 1) body =
      Verity.bind (body start) (fun _ => forEachRange (start + 1) count body) := rfl

theorem forEachRange_preserves_invariant
    {P : ContractState → Prop} {count : Nat} {body : Nat → Contract Unit}
    (hStep : ∀ i s s', (body i).run s = .success () s' → P s → P s') :
    ∀ start s s', (forEachRange start count body).run s = .success () s' → P s → P s' := by
  induction count with
  | zero =>
    intro start s s' hRun hP
    simp [forEachRange, Verity.pure, Contract.run] at hRun
    subst hRun
    exact hP
  | succ n ih =>
    intro start s s' hRun hP
    rw [forEachRange_succ, bind_run_eq_success_iff] at hRun
    rcases hRun with ⟨⟨⟩, sMid, hBody, hRest⟩
    exact ih (start + 1) sMid s' hRest (hStep start s sMid hBody hP)

/-! ## 2. `forEachSetBit` -/

/-- Iterate over set bits of `word` (from MSB to LSB) with an explicit `fuel` budget. -/
def forEachSetBit (word : Uint256) (fuel : Nat := 256) (body : Nat → Contract Unit) : Contract Unit :=
  match fuel with
  | 0 => Verity.pure ()
  | n + 1 =>
    if word.val = 0 then
      Verity.pure ()
    else
      let idx := Nat.log2 word.val
      let nextWord := Uint256.ofNat (word.val - 2 ^ idx)
      Verity.bind (body idx) (fun _ => forEachSetBit nextWord n body)

@[simp] theorem forEachSetBit_zero (word : Uint256) (body : Nat → Contract Unit) :
    forEachSetBit word 0 body = Verity.pure () := rfl

theorem forEachSetBit_preserves_invariant
    {P : ContractState → Prop} {fuel : Nat} {body : Nat → Contract Unit}
    (hStep : ∀ idx s s', (body idx).run s = .success () s' → P s → P s') :
    ∀ word s s', (forEachSetBit word fuel body).run s = .success () s' → P s → P s' := by
  induction fuel with
  | zero =>
    intro word s s' hRun hP
    simp [forEachSetBit, Verity.pure, Contract.run] at hRun
    subst hRun
    exact hP
  | succ n ih =>
    intro word s s' hRun hP
    unfold forEachSetBit at hRun
    split at hRun
    · simp [Verity.pure, Contract.run] at hRun
      subst hRun
      exact hP
    · rw [bind_run_eq_success_iff] at hRun
      rcases hRun with ⟨⟨⟩, sMid, hBody, hRest⟩
      exact ih _ sMid s' hRest (hStep _ s sMid hBody hP)

/-! ## 3. `binarySearchInterval` -/

/-- Structurally bounded binary search over `[low, high)` with explicit `fuel`. -/
def binarySearchInterval (low high : Nat) (fuel : Nat) (pred : Nat → Contract Bool) : Contract Nat :=
  match fuel with
  | 0 => Verity.pure low
  | n + 1 =>
    if high ≤ low then
      Verity.pure low
    else
      let mid := low + (high - low) / 2
      Verity.bind (pred mid) (fun ok =>
        if ok then
          binarySearchInterval low mid n pred
        else
          binarySearchInterval (mid + 1) high n pred)

@[simp] theorem binarySearchInterval_zero (low high : Nat) (pred : Nat → Contract Bool) :
    binarySearchInterval low high 0 pred = Verity.pure low := rfl

theorem binarySearchInterval_preserves_invariant
    {P : ContractState → Prop} {fuel : Nat} {pred : Nat → Contract Bool}
    (hPred : ∀ mid b s s', (pred mid).run s = .success b s' → P s → P s') :
    ∀ low high res s s', (binarySearchInterval low high fuel pred).run s = .success res s' →
      P s → P s' := by
  induction fuel with
  | zero =>
    intro low high res s s' hRun hP
    simp [binarySearchInterval, Verity.pure, Contract.run] at hRun
    rcases hRun with ⟨_, rfl⟩
    exact hP
  | succ n ih =>
    intro low high res s s' hRun hP
    unfold binarySearchInterval at hRun
    split at hRun
    · simp [Verity.pure, Contract.run] at hRun
      rcases hRun with ⟨_, rfl⟩
      exact hP
    · rw [bind_run_eq_success_iff] at hRun
      rcases hRun with ⟨ok, sMid, hP0, hNext⟩
      have hPMid := hPred _ ok s sMid hP0 hP
      cases ok <;> exact ih _ _ res sMid s' hNext hPMid

/-! ## 4. `boundedWhile` -/

/-- Execute `body` while `cond` returns `true`, up to `fuel` iterations. -/
def boundedWhile (fuel : Nat) (cond : Contract Bool) (body : Contract Unit) : Contract Unit :=
  match fuel with
  | 0 => Verity.pure ()
  | n + 1 =>
    Verity.bind cond (fun c =>
      if c then
        Verity.bind body (fun _ => boundedWhile n cond body)
      else
        Verity.pure ())

@[simp] theorem boundedWhile_zero (cond : Contract Bool) (body : Contract Unit) :
    boundedWhile 0 cond body = Verity.pure () := rfl

@[simp] theorem boundedWhile_succ (fuel : Nat) (cond : Contract Bool) (body : Contract Unit) :
    boundedWhile (fuel + 1) cond body =
      Verity.bind cond (fun c =>
        if c then
          Verity.bind body (fun _ => boundedWhile fuel cond body)
        else
          Verity.pure ()) := rfl

theorem boundedWhile_preserves_invariant
    {P : ContractState → Prop} {fuel : Nat} {cond : Contract Bool} {body : Contract Unit}
    (hCond : ∀ b s s', cond.run s = .success b s' → P s → P s')
    (hBody : ∀ s s', body.run s = .success () s' → P s → P s') :
    ∀ s s', (boundedWhile fuel cond body).run s = .success () s' → P s → P s' := by
  induction fuel with
  | zero =>
    intro s s' hRun hP
    simp [boundedWhile, Verity.pure, Contract.run] at hRun
    subst hRun
    exact hP
  | succ n ih =>
    intro s s' hRun hP
    rw [boundedWhile_succ, bind_run_eq_success_iff] at hRun
    rcases hRun with ⟨b, s1, hC, hNext⟩
    have hP1 := hCond b s s1 hC hP
    cases b
    · simp [Verity.pure, Contract.run] at hNext
      subst hNext
      exact hP1
    · simp only [↓reduceIte, bind_run_eq_success_iff] at hNext
      rcases hNext with ⟨⟨⟩, s2, hB, hRest⟩
      exact ih s2 s' hRest (hBody s1 s2 hB hP1)

end Verity.Core.BoundedLoops
