/-
  Sum helper functions for proving sum properties.

  This module provides utilities for summing balances over finite address sets.
-/

import Verity.Core
import Verity.EVM.Uint256

namespace Verity.Specs.Common

open Verity
open Verity.Core
open Verity.EVM.Uint256

/-- Sum balances from a mapping over a finite set of addresses -/
def sumBalances (slot : Nat) (addrs : FiniteAddressSet) (balances : Nat → Address → Uint256) : Uint256 :=
  addrs.addresses.sum (fun addr => balances slot addr)

/-- Exact mathematical `Nat`-valued sum of balances from a mapping over a finite set of addresses.
    Unlike `sumBalances`, this sum takes values in `Nat` and cannot silently wrap modulo 2^256. -/
def sumBalancesNat (slot : Nat) (addrs : FiniteAddressSet) (balances : Nat → Address → Uint256) : Nat :=
  addrs.addresses.elements.foldl (fun acc addr => acc + (balances slot addr).val) 0

/-- Overflow-free invariant: the exact `Nat` sum of balances over `addrs` at `slot`
    fits within `Uint256` (`≤ MAX_UINT256`). -/
def NoSupplyOverflow (slot : Nat) (addrs : FiniteAddressSet) (s : ContractState) : Prop :=
  sumBalancesNat slot addrs s.storageMap ≤ MAX_UINT256

/-- Duplicate-freeness predicate for a finite address set. -/
def NodupAddressSet (addrs : FiniteAddressSet) : Prop :=
  addrs.addresses.elements.Nodup

/-- Every `FiniteAddressSet` satisfies `NodupAddressSet` by construction. -/
theorem nodupAddressSet (addrs : FiniteAddressSet) : NodupAddressSet addrs :=
  addrs.addresses.nodup

/-- Invariant: only known addresses have non-zero balances -/
def balancesFinite (slot : Nat) (s : ContractState) : Prop :=
  ∀ addr, addr ∉ (s.knownAddresses slot).addresses.elements →
    s.storageMap slot addr = 0

/-! ## Foldl Helper Lemmas -/

/-- Helper: foldl of addition over zeros starting from zero gives zero -/
private theorem foldl_add_zero_acc (l : List α) (f : α → Uint256)
    (h : ∀ x ∈ l, f x = 0) (acc : Uint256) :
    l.foldl (fun a x => a + f x) acc = acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl]
    have ha : f a = 0 := h a (by simp)
    rw [ha, Uint256.add_zero]
    exact ih (fun x hx => h x (List.mem_cons_of_mem a hx)) acc

/-- Helper: foldl with non-zero accumulator equals accumulator plus foldl from zero.
    This is the key lemma for decomposing foldl sums. -/
private theorem foldl_acc_comm (l : List α) (f : α → Uint256) (acc : Uint256) :
    l.foldl (fun a x => a + f x) acc = acc + l.foldl (fun a x => a + f x) 0 := by
  induction l generalizing acc with
  | nil =>
    simp only [List.foldl]
    rw [Uint256.add_zero]
  | cons a t ih =>
    simp only [List.foldl]
    rw [Uint256.zero_add]
    rw [ih (acc + f a)]
    rw [ih (f a)]
    simp [Uint256.add_assoc]

/-- Helper: foldl is invariant under pointwise-equal functions on list elements -/
private theorem foldl_congr (l : List α) (f g : α → Uint256) (acc : Uint256)
    (h : ∀ x ∈ l, f x = g x) :
    l.foldl (fun a x => a + f x) acc = l.foldl (fun a x => a + g x) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl]
    have ha : f a = g a := h a (by simp)
    rw [ha]
    exact ih (acc + g a) (fun x hx => h x (List.mem_cons_of_mem a hx))

/-! ## Sum Properties -/

/-- Helper: sum is preserved when adding to known address -/
theorem sumBalances_insert_existing {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256}
    (h : addr ∈ addrs.addresses.elements) :
    sumBalances slot (addrs.insert addr) balances = sumBalances slot addrs balances := by
  unfold sumBalances FiniteAddressSet.insert FiniteSet.insert
  simp [h]

/-- Helper: sum increases when adding balance to new address -/
theorem sumBalances_insert_new {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256} {amount : Uint256}
    (h : addr ∉ addrs.addresses.elements)
    (_h_zero : balances slot addr = 0) :
    sumBalances slot (addrs.insert addr) (fun s a =>
      if s == slot && a == addr then amount else balances s a) =
    add (sumBalances slot addrs balances) amount := by
  unfold sumBalances FiniteSet.sum
  -- After insert_of_not_mem, elements become addr :: addrs.addresses.elements
  rw [FiniteAddressSet.insert, FiniteSet.insert_of_not_mem addr addrs.addresses h]
  simp only [List.foldl]
  -- The head element is addr, so the if-condition is true: simplify 0 + amount to amount
  simp only [BEq.beq, decide_true, Bool.true_and, ite_true, Uint256.zero_add]
  -- Now goal: foldl (updated) amount rest = add (foldl (original) 0 rest) amount
  -- Step 1: use foldl_acc_comm to extract amount from the accumulator
  rw [foldl_acc_comm]
  -- Now goal: amount + foldl (updated) 0 rest = add (foldl (original) 0 rest) amount
  -- Step 2: show updated and original foldl agree on rest elements (none equal addr)
  have h_eq := foldl_congr addrs.addresses.elements
    (fun a => if decide (a = addr) = true then amount else balances slot a)
    (fun a => balances slot a)
    0
    (fun x hx => by
      have hne : x ≠ addr := fun heq => h (heq ▸ hx)
      simp [hne])
  -- Step 3: rewrite LHS foldl to match RHS foldl, then use add_comm
  -- h_eq equates the two foldl forms. Unfold HAdd/add so both sides use same notation.
  show amount + List.foldl (fun a x => a + (fun a => if decide (a = addr) = true then amount else balances slot a) x) 0
      addrs.addresses.elements =
    Uint256.add (List.foldl (fun acc x => acc + balances slot x) 0 addrs.addresses.elements) amount
  rw [h_eq]
  exact Uint256.add_comm amount _

/-- Helper: a + (b - c) = (a + b) - c in modular arithmetic (Z/2^256Z is a group) -/
private theorem add_sub_assoc (a b c : Uint256) : a + (b - c) = (a + b) - c := by
  -- Strategy: show both sides + c give the same result, then use add_right_cancel
  have lhs_eq : (a + (b - c)) + c = a + b := by
    have := Uint256.sub_add_cancel_left b c  -- (b - c) + c = b
    calc (a + (b - c)) + c
        = a + ((b - c) + c) := by
          rw [Uint256.add_assoc]
      _ = a + b := by rw [this]
  have rhs_eq : ((a + b) - c) + c = a + b := Uint256.sub_add_cancel_left (a + b) c
  exact Uint256.add_right_cancel (by rw [lhs_eq, rhs_eq])

/-- Helper: head case of `foldl_replace_one`, where the target is the list head. -/
private theorem foldl_replace_one_head (t : List α) (f g : α → Uint256) (target : α)
    (new_val : Uint256) (h_not_mem : target ∉ t)
    (h_other : ∀ x ∈ t, x ≠ target → g x = f x) :
    t.foldl (fun acc x => acc + g x) new_val =
    t.foldl (fun acc x => acc + f x) (f target) - f target + new_val := by
  -- Extract accumulators, then use that `g` agrees with `f` on the tail
  rw [foldl_acc_comm t g new_val,
    foldl_congr t g f 0 (fun x hx => h_other x hx (fun heq => h_not_mem (heq ▸ hx))),
    foldl_acc_comm t f (f target)]
  -- (f target + X) - f target + new_val = new_val + X
  rw [Uint256.add_comm (f target) (List.foldl (fun a x => a + f x) 0 t),
    Uint256.sub_add_cancel]
  exact Uint256.add_comm new_val _

/-- Helper: tail step of `foldl_replace_one`, pushing a non-target head through. -/
private theorem foldl_replace_one_tail (t : List α) (f g : α → Uint256) (a target : α)
    (new_val : Uint256)
    (ih : t.foldl (fun acc x => acc + g x) 0 =
      t.foldl (fun acc x => acc + f x) 0 - f target + new_val) :
    t.foldl (fun acc x => acc + g x) (f a) =
    t.foldl (fun acc x => acc + f x) (f a) - f target + new_val := by
  rw [foldl_acc_comm t g (f a), foldl_acc_comm t f (f a), ih]
  -- f a + ((X - Y) + Z) = ((f a + X) - Y) + Z
  rw [← Uint256.add_assoc (f a) _ new_val]
  rw [add_sub_assoc (f a) (List.foldl (fun a x => a + f x) 0 t) (f target)]

/-- Helper: for a nodup list containing target, replacing target's value with new_val
    changes the foldl sum by (new_val - old_val):
    foldl(updated) = (foldl(original) - old_val) + new_val -/
private theorem foldl_replace_one (l : List α) [DecidableEq α]
    (f g : α → Uint256) (target : α) (new_val : Uint256)
    (h_mem : target ∈ l) (h_nodup : l.Nodup)
    (h_target : g target = new_val)
    (h_other : ∀ x ∈ l, x ≠ target → g x = f x) :
    l.foldl (fun acc x => acc + g x) 0 =
    (l.foldl (fun acc x => acc + f x) 0) - (f target) + new_val := by
  induction l with
  | nil => cases h_mem
  | cons a t ih =>
    simp only [List.foldl, Uint256.zero_add]
    have h_nodup_t := (List.nodup_cons.mp h_nodup).2
    cases List.mem_cons.mp h_mem with
    | inl heq =>
      subst heq
      rw [h_target]
      exact foldl_replace_one_head t f g target new_val (List.nodup_cons.mp h_nodup).1
        (fun x hx hne => h_other x (List.mem_cons_of_mem _ hx) hne)
    | inr hmem =>
      have h_ne : a ≠ target := fun heq => (List.nodup_cons.mp h_nodup).1 (heq ▸ hmem)
      rw [h_other a (by simp) h_ne]
      exact foldl_replace_one_tail t f g a target new_val
        (ih hmem h_nodup_t (fun x hx hne => h_other x (List.mem_cons_of_mem a hx) hne))

/-- Helper: sum changes when updating balance of existing address -/
theorem sumBalances_update_existing {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256} {old_amount new_amount : Uint256}
    (h : addr ∈ addrs.addresses.elements)
    (h_old : balances slot addr = old_amount) :
    sumBalances slot addrs (fun s a =>
      if s == slot && a == addr then new_amount else balances s a) =
    add (sub (sumBalances slot addrs balances) old_amount) new_amount := by
  unfold sumBalances FiniteSet.sum
  -- Apply foldl_replace_one with g = updated balances, f = original balances
  -- First rewrite the LHS foldl lambda to separate slot/addr BEq
  have h_lhs_eq : ∀ acc,
    List.foldl (fun acc x => acc + if slot == slot && x == addr then new_amount else balances slot x)
      acc addrs.addresses.elements =
    List.foldl (fun acc x => acc + (fun a => if slot == slot && a == addr then new_amount else balances slot a) x)
      acc addrs.addresses.elements := by
    intro acc; rfl
  rw [h_lhs_eq 0]
  have h_result := foldl_replace_one
    addrs.addresses.elements
    (fun a => balances slot a)
    (fun a => if slot == slot && a == addr then new_amount else balances slot a)
    addr new_amount
    h addrs.addresses.nodup
    (by simp [BEq.beq])
    (fun x _ hne => by simp [BEq.beq, hne])
  -- h_result has (fun a => balances slot a) addr which beta-reduces to balances slot addr
  rw [h_old] at h_result
  -- h_result uses HSub/HAdd: _ - _ + _, goal uses add (sub ...) ...
  -- These are definitionally equal
  exact h_result

/-- Helper: sumBalances equals zero when all balances are zero -/
theorem sumBalances_zero_of_all_zero {slot : Nat} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256} :
    (∀ addr ∈ addrs.addresses.elements, balances slot addr = 0) →
    sumBalances slot addrs balances = 0 := by
  intro h
  unfold sumBalances FiniteSet.sum
  exact foldl_add_zero_acc addrs.addresses.elements (fun addr => balances slot addr) h 0

/-- Helper: balancesFinite preserved by setMapping (deposit) -/
theorem balancesFinite_preserved_deposit {slot : Nat} (s : ContractState)
    (addr : Address) (amount : Uint256) :
    balancesFinite slot s →
    balancesFinite slot { s.writeMap slot addr amount with
      knownAddresses := fun s' =>
        if s' == slot then (s.knownAddresses s').insert addr
        else s.knownAddresses s' } := by
  intro h_finite
  unfold balancesFinite
  intro addr' h_not_in
  -- The new knownAddresses at slot is (s.knownAddresses slot).insert addr
  -- h_not_in : addr' ∉ (if slot == slot then ... else ...).addresses.elements
  -- Since slot == slot is true, this simplifies to addr' ∉ ((s.knownAddresses slot).insert addr).addresses.elements
  simp only [BEq.beq, decide_true, ite_true] at h_not_in
  -- By mem_elements_insert: addr' ∉ insert means addr' ≠ addr ∧ addr' ∉ original
  rw [FiniteAddressSet.insert] at h_not_in
  have h_not_or := mt (FiniteSet.mem_elements_insert addr' addr (s.knownAddresses slot).addresses).mpr h_not_in
  simp only [not_or] at h_not_or
  obtain ⟨h_ne, h_not_orig⟩ := h_not_or
  -- The `knownAddresses` record update does not alter the canonical word
  -- lens, and constructor injectivity makes the different-key write inert.
  change (s.writeMap slot addr amount).storageMap slot addr' = 0
  rw [← ContractState.readMap]
  rw [ContractState.readMap_writeMap_other_key s slot h_ne amount]
  exact h_finite addr' h_not_orig

/-! ## Exact `Nat` Sum Properties and Bridge Lemmas -/

/-- Helper: `Nat` foldl of addition over zeros preserves the accumulator. -/
private theorem foldl_nat_add_zero_acc (l : List α) (f : α → Nat)
    (h : ∀ x ∈ l, f x = 0) (acc : Nat) :
    l.foldl (fun a x => a + f x) acc = acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl]
    have ha : f a = 0 := h a (by simp)
    rw [ha, Nat.add_zero]
    exact ih (fun x hx => h x (List.mem_cons_of_mem a hx)) acc

/-- Helper: `Nat` foldl with non-zero accumulator equals accumulator plus foldl from zero. -/
private theorem foldl_nat_acc_comm (l : List α) (f : α → Nat) (acc : Nat) :
    l.foldl (fun a x => a + f x) acc = acc + l.foldl (fun a x => a + f x) 0 := by
  induction l generalizing acc with
  | nil =>
    simp only [List.foldl, Nat.add_zero]
  | cons a t ih =>
    simp only [List.foldl, Nat.zero_add]
    rw [ih (acc + f a), ih (f a), Nat.add_assoc]

/-- Helper: `Nat` foldl is invariant under pointwise-equal functions on list elements. -/
private theorem foldl_nat_congr (l : List α) (f g : α → Nat) (acc : Nat)
    (h : ∀ x ∈ l, f x = g x) :
    l.foldl (fun a x => a + f x) acc = l.foldl (fun a x => a + g x) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl]
    have ha : f a = g a := h a (by simp)
    rw [ha]
    exact ih (acc + g a) (fun x hx => h x (List.mem_cons_of_mem a hx))

/-- Helper: any element's value in a list is bounded above by the `Nat` foldl sum. -/
private theorem le_foldl_nat_of_mem (l : List α) (f : α → Nat) (target : α)
    (h_mem : target ∈ l) :
    f target ≤ l.foldl (fun acc x => acc + f x) 0 := by
  induction l with
  | nil => cases h_mem
  | cons a t ih =>
    simp only [List.foldl, Nat.zero_add]
    rw [foldl_nat_acc_comm t f (f a)]
    cases List.mem_cons.mp h_mem with
    | inl heq =>
      subst heq
      exact Nat.le_add_right (f target) _
    | inr hmem =>
      have h_le := ih hmem
      omega

/-- Helper: for a nodup list containing `target`, replacing `target`'s `Nat` value with `new_val`
    changes the `Nat` foldl sum by subtracting `f target` and adding `new_val`. -/
private theorem foldl_nat_replace_one (l : List α) [DecidableEq α]
    (f g : α → Nat) (target : α) (new_val : Nat)
    (h_mem : target ∈ l) (h_nodup : l.Nodup)
    (h_target : g target = new_val)
    (h_other : ∀ x ∈ l, x ≠ target → g x = f x) :
    l.foldl (fun acc x => acc + g x) 0 =
    l.foldl (fun acc x => acc + f x) 0 - f target + new_val := by
  induction l with
  | nil => cases h_mem
  | cons a t ih =>
    simp only [List.foldl, Nat.zero_add]
    have h_nodup_t := (List.nodup_cons.mp h_nodup).2
    cases List.mem_cons.mp h_mem with
    | inl heq =>
      subst heq
      rw [h_target,
        foldl_nat_acc_comm t g new_val,
        foldl_nat_congr t g f 0 (fun x hx =>
          h_other x (List.mem_cons_of_mem _ hx) (fun heq => (List.nodup_cons.mp h_nodup).1 (heq ▸ hx))),
        foldl_nat_acc_comm t f (f target)]
      omega
    | inr hmem =>
      have h_ne : a ≠ target := fun heq => (List.nodup_cons.mp h_nodup).1 (heq ▸ hmem)
      have h_ih := ih hmem h_nodup_t (fun x hx hne => h_other x (List.mem_cons_of_mem a hx) hne)
      have h_le := le_foldl_nat_of_mem t f target hmem
      rw [h_other a (by simp) h_ne,
        foldl_nat_acc_comm t g (f a),
        foldl_nat_acc_comm t f (f a),
        h_ih]
      omega

/-- `sumBalancesNat` over an empty address list is zero. -/
@[simp] theorem sumBalancesNat_nil (slot : Nat) (balances : Nat → Address → Uint256) :
    sumBalancesNat slot ⟨⟨[], List.nodup_nil⟩⟩ balances = 0 := rfl

/-- `sumBalancesNat` over `FiniteAddressSet.empty` is zero. -/
@[simp] theorem sumBalancesNat_empty (slot : Nat) (balances : Nat → Address → Uint256) :
    sumBalancesNat slot FiniteAddressSet.empty balances = 0 := rfl

/-- `sumBalancesNat` over a cons address list splits into the head balance plus the tail sum. -/
@[simp] theorem sumBalancesNat_cons (slot : Nat) (addr : Address) (rest : List Address)
    (h_nodup : (addr :: rest).Nodup) (balances : Nat → Address → Uint256) :
    sumBalancesNat slot ⟨⟨addr :: rest, h_nodup⟩⟩ balances =
      (balances slot addr).val +
        sumBalancesNat slot ⟨⟨rest, (List.nodup_cons.mp h_nodup).2⟩⟩ balances := by
  unfold sumBalancesNat
  simp only [List.foldl, Nat.zero_add]
  exact foldl_nat_acc_comm rest (fun a => (balances slot a).val) (balances slot addr).val

/-- `sumBalancesNat` is preserved when inserting an already-present address. -/
theorem sumBalancesNat_insert_existing {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256}
    (h : addr ∈ addrs.addresses.elements) :
    sumBalancesNat slot (addrs.insert addr) balances = sumBalancesNat slot addrs balances := by
  unfold sumBalancesNat FiniteAddressSet.insert FiniteSet.insert
  simp [h]

/-- `sumBalancesNat` increases by `amount.val` when inserting a new address with balance `amount`. -/
theorem sumBalancesNat_insert_new {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256} {amount : Uint256}
    (h : addr ∉ addrs.addresses.elements)
    (_h_zero : balances slot addr = 0) :
    sumBalancesNat slot (addrs.insert addr) (fun s a =>
      if s == slot && a == addr then amount else balances s a) =
    sumBalancesNat slot addrs balances + amount.val := by
  unfold sumBalancesNat
  rw [FiniteAddressSet.insert, FiniteSet.insert_of_not_mem addr addrs.addresses h]
  simp only [List.foldl, BEq.beq, decide_true, Bool.true_and, ite_true, Nat.zero_add]
  rw [foldl_nat_acc_comm]
  have h_eq := foldl_nat_congr addrs.addresses.elements
    (fun a => (if decide (a = addr) = true then amount else balances slot a).val)
    (fun a => (balances slot a).val)
    0
    (fun x hx => by
      have hne : x ≠ addr := fun heq => h (heq ▸ hx)
      simp [hne])
  rw [h_eq, Nat.add_comm]

/-- Every member's balance is bounded above by `sumBalancesNat`. -/
theorem balance_le_sumBalancesNat {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256}
    (h : addr ∈ addrs.addresses.elements) :
    (balances slot addr).val ≤ sumBalancesNat slot addrs balances :=
  le_foldl_nat_of_mem addrs.addresses.elements (fun a => (balances slot a).val) addr h

/-- Updating the balance of an existing address in `addrs` (general point-update form)
    shifts `sumBalancesNat` by the exact `Nat` difference. -/
theorem sumBalancesNat_point_update {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances balances' : Nat → Address → Uint256} {old_amount new_amount : Uint256}
    (h : addr ∈ addrs.addresses.elements)
    (h_old : balances slot addr = old_amount)
    (h_target : balances' slot addr = new_amount)
    (h_other : ∀ a ∈ addrs.addresses.elements, a ≠ addr → balances' slot a = balances slot a) :
    sumBalancesNat slot addrs balances' =
    sumBalancesNat slot addrs balances - old_amount.val + new_amount.val := by
  unfold sumBalancesNat
  have h_res := foldl_nat_replace_one
    addrs.addresses.elements
    (fun a => (balances slot a).val)
    (fun a => (balances' slot a).val)
    addr new_amount.val
    h addrs.addresses.nodup
    (by rw [h_target])
    (fun x hx hne => by rw [h_other x hx hne])
  rw [h_old] at h_res
  exact h_res

/-- Updating the balance of an existing address in `addrs` shifts `sumBalancesNat`
    by subtracting `old_amount.val` and adding `new_amount.val` in exact `Nat` arithmetic. -/
theorem sumBalancesNat_update_existing {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256} {old_amount new_amount : Uint256}
    (h : addr ∈ addrs.addresses.elements)
    (h_old : balances slot addr = old_amount) :
    sumBalancesNat slot addrs (fun s a =>
      if s == slot && a == addr then new_amount else balances s a) =
    sumBalancesNat slot addrs balances - old_amount.val + new_amount.val := by
  exact sumBalancesNat_point_update h h_old
    (by simp [BEq.beq])
    (fun a _ hne => by simp [BEq.beq, hne])

/-- `sumBalancesNat` equals zero when all balances in the set are zero. -/
theorem sumBalancesNat_zero_of_all_zero {slot : Nat} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256} :
    (∀ addr ∈ addrs.addresses.elements, balances slot addr = 0) →
    sumBalancesNat slot addrs balances = 0 := by
  intro h
  unfold sumBalancesNat
  exact foldl_nat_add_zero_acc addrs.addresses.elements (fun addr => (balances slot addr).val)
    (fun addr h_mem => by simp [h addr h_mem]) 0

/-- Exact `Nat` balance conservation for a relational transfer from `sender` to `recipient`
    when `amount ≤ (balances slot sender).val` and `(balances slot recipient).val + amount ≤ MAX_UINT256`. -/
theorem sumBalancesNat_transfer_eq {slot : Nat} {sender recipient : Address}
    {addrs : FiniteAddressSet} {balances balances' : Nat → Address → Uint256} {amount : Uint256}
    (h_sender : sender ∈ addrs.addresses.elements)
    (h_recipient : recipient ∈ addrs.addresses.elements)
    (h_ne : sender ≠ recipient)
    (h_sub : amount.val ≤ (balances slot sender).val)
    (h_add : (balances slot recipient).val + amount.val ≤ MAX_UINT256)
    (h_sender_bal : balances' slot sender = sub (balances slot sender) amount)
    (h_recipient_bal : balances' slot recipient = add (balances slot recipient) amount)
    (h_other : ∀ a ∈ addrs.addresses.elements, a ≠ sender → a ≠ recipient →
      balances' slot a = balances slot a) :
    sumBalancesNat slot addrs balances' = sumBalancesNat slot addrs balances := by
  let balances_mid : Nat → Address → Uint256 := fun s a =>
    if s == slot && a == sender then sub (balances slot sender) amount else balances s a
  have h_mid : sumBalancesNat slot addrs balances_mid =
      sumBalancesNat slot addrs balances - (balances slot sender).val +
        (sub (balances slot sender) amount).val :=
    sumBalancesNat_update_existing h_sender rfl
  have h_mid_recip : balances_mid slot recipient = balances slot recipient := by
    have h_ne' : recipient ≠ sender := Ne.symm h_ne
    simp [balances_mid, BEq.beq, h_ne']
  have h_final : sumBalancesNat slot addrs balances' =
      sumBalancesNat slot addrs balances_mid - (balances slot recipient).val +
        (add (balances slot recipient) amount).val := by
    refine sumBalancesNat_point_update h_recipient h_mid_recip h_recipient_bal ?_
    intro a ha hne_recip
    by_cases h_eq_sender : a = sender
    · subst h_eq_sender
      simp [balances_mid, BEq.beq, h_sender_bal]
    · have h_other_a := h_other a ha h_eq_sender hne_recip
      simp [balances_mid, BEq.beq, h_eq_sender, h_other_a]
  have h_sender_le : (balances slot sender).val ≤ sumBalancesNat slot addrs balances :=
    balance_le_sumBalancesNat h_sender
  have h_recip_le : (balances slot recipient).val ≤ sumBalancesNat slot addrs balances_mid := by
    rw [← h_mid_recip]
    exact balance_le_sumBalancesNat h_recipient
  have h_sub_val : (sub (balances slot sender) amount).val =
      (balances slot sender).val - amount.val :=
    Verity.Core.Uint256.subNoWrap h_sub
  have h_add_lt : (balances slot recipient).val + amount.val < Verity.Core.Uint256.modulus := by
    have h_succ := Verity.Core.Uint256.max_uint256_succ_eq_modulus
    omega
  have h_add_val : (add (balances slot recipient) amount).val =
      (balances slot recipient).val + amount.val :=
    Verity.Core.Uint256.addNoWrap h_add_lt
  omega

/-- Exact `Nat` balance conservation for a transfer of `amount` from `sender` to `recipient`
    where `amount.val ≤ (balances slot sender).val` and
    `(balances slot recipient).val + amount.val ≤ MAX_UINT256`. -/
theorem sumBalancesNat_transfer_conserved {slot : Nat} {sender recipient : Address}
    {addrs : FiniteAddressSet} {balances : Nat → Address → Uint256} {amount : Uint256}
    (h_sender : sender ∈ addrs.addresses.elements)
    (h_recipient : recipient ∈ addrs.addresses.elements)
    (h_ne : sender ≠ recipient)
    (h_sub : amount.val ≤ (balances slot sender).val)
    (h_add : (balances slot recipient).val + amount.val ≤ MAX_UINT256) :
    sumBalancesNat slot addrs (fun s a =>
      if s == slot && a == recipient then add (balances slot recipient) amount
      else if s == slot && a == sender then sub (balances slot sender) amount
      else balances s a) =
    sumBalancesNat slot addrs balances := by
  exact sumBalancesNat_transfer_eq h_sender h_recipient h_ne h_sub h_add
    (by simp [BEq.beq, h_ne])
    (by simp [BEq.beq])
    (fun a _ hne_s hne_r => by simp [BEq.beq, hne_s, hne_r])

/-- Helper: `Uint256` foldl sum equals `Uint256.ofNat` of the `Nat` foldl sum. -/
private theorem foldl_uint256_eq_ofNat_foldl_nat (l : List α) (f : α → Uint256) (acc : Nat) :
    l.foldl (fun u x => u + f x) (Verity.Core.Uint256.ofNat acc) =
      Verity.Core.Uint256.ofNat (l.foldl (fun n x => n + (f x).val) acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl]
    have h_step : Verity.Core.Uint256.ofNat acc + f a =
        Verity.Core.Uint256.ofNat (acc + (f a).val) := by
      rw [Verity.Core.Uint256.ofNat_add]
      congr 1
      exact Verity.Core.Uint256.ext (Nat.mod_eq_of_lt (f a).isLt).symm
    rw [h_step]
    exact ih (acc + (f a).val)

/-- Bridge theorem: `sumBalances` is the `Uint256.ofNat` projection of `sumBalancesNat`. -/
theorem sumBalances_eq_ofNat_sumBalancesNat (slot : Nat) (addrs : FiniteAddressSet)
    (balances : Nat → Address → Uint256) :
    sumBalances slot addrs balances =
      Verity.Core.Uint256.ofNat (sumBalancesNat slot addrs balances) := by
  unfold sumBalances sumBalancesNat FiniteSet.sum
  exact foldl_uint256_eq_ofNat_foldl_nat addrs.addresses.elements (fun addr => balances slot addr) 0

/-- Bridge theorem: `(sumBalances ...).val` equals `sumBalancesNat` modulo `2^256`. -/
theorem sumBalances_val_eq_mod (slot : Nat) (addrs : FiniteAddressSet)
    (balances : Nat → Address → Uint256) :
    (sumBalances slot addrs balances).val =
      sumBalancesNat slot addrs balances % Verity.Core.Uint256.modulus := by
  rw [sumBalances_eq_ofNat_sumBalancesNat]
  rfl

/-- Bridge theorem: when `sumBalancesNat slot addrs balances ≤ MAX_UINT256`,
    no modular wrap occurs and `(sumBalances slot addrs balances).val = sumBalancesNat slot addrs balances`. -/
theorem sumBalances_val_eq_sumBalancesNat {slot : Nat} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256}
    (h_no_overflow : sumBalancesNat slot addrs balances ≤ MAX_UINT256) :
    (sumBalances slot addrs balances).val = sumBalancesNat slot addrs balances := by
  rw [sumBalances_val_eq_mod]
  have h_lt : sumBalancesNat slot addrs balances < Verity.Core.Uint256.modulus := by
    have h_succ := Verity.Core.Uint256.max_uint256_succ_eq_modulus
    omega
  exact Nat.mod_eq_of_lt h_lt

/-- Symmetric bridge theorem: under `NoSupplyOverflow`, `sumBalancesNat` equals `(sumBalances ...).val`. -/
theorem sumBalancesNat_eq_sumBalances_val {slot : Nat} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256}
    (h_no_overflow : sumBalancesNat slot addrs balances ≤ MAX_UINT256) :
    sumBalancesNat slot addrs balances = (sumBalances slot addrs balances).val :=
  (sumBalances_val_eq_sumBalancesNat h_no_overflow).symm

/-- Bridge theorem specialized to `NoSupplyOverflow` on `ContractState`. -/
theorem sumBalances_val_of_noSupplyOverflow {slot : Nat} {addrs : FiniteAddressSet}
    {s : ContractState} (h : NoSupplyOverflow slot addrs s) :
    (sumBalances slot addrs s.storageMap).val = sumBalancesNat slot addrs s.storageMap :=
  sumBalances_val_eq_sumBalancesNat h

/-- `NoSupplyOverflow` is preserved across any transition that conserves `sumBalancesNat`. -/
theorem noSupplyOverflow_preserved_of_sumBalancesNat_eq {slot : Nat} {addrs : FiniteAddressSet}
    {s s' : ContractState}
    (h_eq : sumBalancesNat slot addrs s'.storageMap = sumBalancesNat slot addrs s.storageMap)
    (h_no_overflow : NoSupplyOverflow slot addrs s) :
    NoSupplyOverflow slot addrs s' := by
  unfold NoSupplyOverflow at *
  omega

end Verity.Specs.Common
