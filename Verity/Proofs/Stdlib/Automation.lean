/-
  Verity.Proofs.Stdlib.Automation

  Helper lemmas and automation for proving specification correctness.

  This module provides proven lemmas for Contract monad operations,
  storage operations, and common proof patterns.

  ## Sections

  - Contract Result Lemmas: `isSuccess`, `getState` for success/revert
  - Basic Storage Operation Lemmas: `getStorage`/`setStorage` runState/runValue
  - Address Storage Lemmas: `getStorageAddr`/`setStorageAddr` runState/runValue
  - Mapping Storage Lemmas: `getMapping`/`setMapping` runState/runValue
  - Require Lemmas: `require_true/false_isSuccess`, `require_state`
  - Address Equality: `address_beq` lemmas
  - Spec Storage Helpers: slot/mapping field access
  - Uint256 Arithmetic: `add`/`sub` value lemmas, `safeSub`/`safeAdd`
  - Well-Formedness Preservation: `wf_of_state_eq` for read-only ops
  - Generic Storage Preservation: cross-type preservation for setStorage/setStorageAddr/setMapping

  Status: All lemmas fully proven with zero sorry, zero axioms.
  Note: addressToNat_injective is now a provable theorem (was an axiom when Address = String).
-/

import Verity.Core
import Verity.Specs.Common
import Verity.Macro.EffectAnalysis
import Verity.Stdlib.Math
import Verity.EVM.Uint256
import Verity.Proofs.Stdlib.UnfoldSet

namespace Verity.Proofs.Stdlib.Automation

open Verity
open Lean Parser.Tactic

/-!
## Standard Unfold Simp Set
-/

/-- Canonical simp-lemma names used by `verity_unfold`. -/
def verity_simp_set : List Lean.Name := [
  ``msgSender,
  ``baseFee,
  ``gasPrice,
  ``getStorageAddr,
  ``getStorage,
  ``setStorage,
  ``setStorageAddr,
  ``getMapping,
  ``setMapping,
  ``setMapping2,
  ``getMappingUint,
  ``setMappingUint,
  ``getMapping2,
  ``ContractState.readSlot,
  ``ContractState.writeSlot,
  ``ContractState.readAddrSlot,
  ``ContractState.writeAddrSlot,
  ``ContractState.readMap,
  ``ContractState.writeMap,
  ``ContractState.readMapUint,
  ``ContractState.writeMapUint,
  ``ContractState.readMap2,
  ``ContractState.writeMap2,
  ``Verity.require,
  ``Verity.pure,
  ``Verity.bind,
  ``Bind.bind,
  ``Pure.pure,
  ``Contract.run,
  ``ContractResult.snd,
  ``ContractResult.fst
]

attribute [verity_unfold_simps]
  msgSender msgValue baseFee gasPrice getStorageAddr getStorage setStorage setStorageAddr
  getMapping setMapping setMapping2 getMappingUint setMappingUint getMapping2
  ContractState.readSlot ContractState.writeSlot ContractState.readAddrSlot
  ContractState.writeAddrSlot ContractState.readMap ContractState.writeMap
  ContractState.readMapUint ContractState.writeMapUint ContractState.readMap2
  ContractState.writeMap2
  emitEvent List.mapM List.mapM.loop
  Verity.require Verity.pure Verity.bind Bind.bind Pure.pure
  Contract.run ContractResult.snd ContractResult.fst

/-- Unfold a contract function with the standard Verity simp set. -/
syntax (name := verity_unfold)
  "verity_unfold " simpLemma : tactic

/-- Unfold a contract function with the standard Verity simp set plus extra simp args
    (typically the internal helpers it calls: `verity_unfold settle with settlePage, unlink`). -/
syntax (name := verity_unfold_with)
  "verity_unfold " simpLemma " with " simpLemma,+ : tactic

/-- Same, at a hypothesis. -/
syntax (name := verity_unfold_at)
  "verity_unfold " simpLemma " at " ident : tactic

/-- Frame-proof helper: rewrite by an unfold lemma, then simplify result-state fields. -/
syntax (name := verity_frame)
  "verity_frame " rwRule : tactic

/-- `verity_frame` with an extra local simp lemma for frame side conditions. -/
syntax (name := verity_frame_with)
  "verity_frame " rwRule " with " simpLemma : tactic

/-- Spec-proof helper: rewrite via an unfold lemma, then discharge standard spec goals. -/
syntax (name := verity_spec_using)
  "verity_spec " simpLemma " using " rwRule : tactic

/-- `verity_spec` with an extra local simp lemma for contract-specific slots/fields. -/
syntax (name := verity_spec_using_with)
  "verity_spec " simpLemma " using " rwRule " with " simpLemma : tactic

/-- Spec-proof helper: unfold a function with `verity_unfold`, then discharge spec goals. -/
syntax (name := verity_spec_unfold)
  "verity_spec " simpLemma " unfold " simpLemma : tactic

/-- `verity_spec` unfold-mode with an extra local simp lemma. -/
syntax (name := verity_spec_unfold_with)
  "verity_spec " simpLemma " unfold " simpLemma " with " simpLemma : tactic

/-- Discharge a common `*_meets_spec` goal after unfolding/rewrite setup. -/
syntax (name := verity_spec)
  "verity_spec " simpLemma : tactic

/-- `verity_spec` with one extra simp lemma. -/
syntax (name := verity_spec_with)
  "verity_spec " simpLemma " with " simpLemma : tactic

/-- Discharge common checked-arithmetic reachability goals (`safeAdd`/`safeSub`/`safeMul`). -/
syntax (name := verity_arith)
  "verity_arith" : tactic

/-- Discharge `viewPreservesState` / storage-frame obligations for `view` computations
containing `require`, `let` bindings, and branches (`#2422`, `#1994`, `#1895`). -/
syntax (name := verity_view_frame)
  "verity_view_frame" : tactic

/-- Unfold a `view` function and discharge its `viewPreservesState` obligation. -/
syntax (name := verity_view_frame_fn)
  "verity_view_frame " simpLemma : tactic

/-- Unfold a `view` function with extra helpers and discharge its `viewPreservesState` obligation. -/
syntax (name := verity_view_frame_with)
  "verity_view_frame " simpLemma " with " simpLemma,+ : tactic

macro_rules
  | `(tactic| verity_unfold $fn:simpLemma) =>
      `(tactic| simp only [verity_unfold_simps, $fn])
  | `(tactic| verity_unfold $fn:simpLemma with $extra,*) =>
      `(tactic| simp only [verity_unfold_simps, $fn, $extra,*])
  | `(tactic| verity_unfold $fn:simpLemma at $h:ident) =>
      `(tactic| simp only [verity_unfold_simps, $fn] at $h:ident)
  | `(tactic| verity_frame $h:rwRule) =>
      `(tactic| (rw [$h]; simp [ContractResult.snd,
        ContractState.writeSlot, ContractState.writeAddrSlot,
        ContractState.writeMap, ContractState.writeMapUint,
        ContractState.writeMap2, ContractState.writeTransient,
        ContractState.storage, ContractState.storageAddr, ContractState.storageMap,
        ContractState.storageMapUint, ContractState.storageMap2, ContractState.transientStorage,
        ContractState.storage_unfold, ContractState.storageAddr_unfold, ContractState.storageMap_unfold, ContractState.storageMapUint_unfold, ContractState.storageMap2_unfold, ContractState.transientStorage_unfold]))
  | `(tactic| verity_frame $h:rwRule with $extra:simpLemma) =>
      `(tactic| (rw [$h]; simp [ContractResult.snd,
        ContractState.writeSlot, ContractState.writeAddrSlot,
        ContractState.writeMap, ContractState.writeMapUint,
        ContractState.writeMap2, ContractState.writeTransient,
        ContractState.storage, ContractState.storageAddr, ContractState.storageMap,
        ContractState.storageMapUint, ContractState.storageMap2, ContractState.transientStorage,
        ContractState.storage_unfold, ContractState.storageAddr_unfold, ContractState.storageMap_unfold, ContractState.storageMapUint_unfold, ContractState.storageMap2_unfold, ContractState.transientStorage_unfold, $extra]))
  | `(tactic| verity_spec $spec:simpLemma using $h:rwRule) =>
      `(tactic|
        (rw [$h]
         simp [$spec, ContractResult.snd]
         try (intro slotIdx h_neq; simp [h_neq])
         try (intro n h_neq; simp [h_neq])))
  | `(tactic| verity_spec $spec:simpLemma using $h:rwRule with $extra:simpLemma) =>
      `(tactic|
        (rw [$h]
         simp [$spec, ContractResult.snd, $extra]
         try (intro slotIdx h_neq; simp [h_neq])
         try (intro n h_neq; simp [h_neq])))
  | `(tactic| verity_spec $spec:simpLemma unfold $fn:simpLemma) =>
      `(tactic|
        (simp only [
           $fn, msgSender, getStorageAddr, getStorage, setStorage, setStorageAddr,
           getMapping, setMapping, setMapping2, getMappingUint, setMappingUint, getMapping2,
           ContractState.readSlot, ContractState.writeSlot, ContractState.readAddrSlot,
           ContractState.writeAddrSlot, ContractState.readMap, ContractState.writeMap,
           ContractState.readMapUint, ContractState.writeMapUint, ContractState.readMap2,
           ContractState.writeMap2,
        ContractState.readSlot, ContractState.writeSlot, ContractState.readAddrSlot,
        ContractState.writeAddrSlot, ContractState.readMap, ContractState.writeMap,
        ContractState.readMapUint, ContractState.writeMapUint, ContractState.readMap2,
        ContractState.writeMap2,
           Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
           Contract.run, ContractResult.snd, ContractResult.fst
         ]
         simp [$spec, ContractResult.snd]
         try (intro slotIdx h_neq; simp [h_neq])
         try (intro n h_neq; simp [h_neq])))
  | `(tactic| verity_spec $spec:simpLemma unfold $fn:simpLemma with $extra:simpLemma) =>
      `(tactic|
        (simp only [
           $fn, msgSender, getStorageAddr, getStorage, setStorage, setStorageAddr,
           getMapping, setMapping, setMapping2, getMappingUint, setMappingUint, getMapping2,
           ContractState.readSlot, ContractState.writeSlot, ContractState.readAddrSlot,
           ContractState.writeAddrSlot, ContractState.readMap, ContractState.writeMap,
           ContractState.readMapUint, ContractState.writeMapUint, ContractState.readMap2,
           ContractState.writeMap2,
        ContractState.readSlot, ContractState.writeSlot, ContractState.readAddrSlot,
        ContractState.writeAddrSlot, ContractState.readMap, ContractState.writeMap,
        ContractState.readMapUint, ContractState.writeMapUint, ContractState.readMap2,
        ContractState.writeMap2,
           Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
           Contract.run, ContractResult.snd, ContractResult.fst, $extra
         ]
         simp [$spec, ContractResult.snd, $extra]
         try (intro slotIdx h_neq; simp [h_neq])
         try (intro n h_neq; simp [h_neq])))

macro "verity_spec " spec:simpLemma : tactic =>
  `(tactic|
    (simp [$spec, ContractResult.snd, Verity.Specs.sameAddrMapContext,
      Verity.Specs.sameStorageMapContext, Verity.Specs.sameContext, Verity.Specs.sameStorage,
      Verity.Specs.sameStorageAddr, Verity.Specs.sameStorageMap]))

macro "verity_spec " spec:simpLemma " with " extra:simpLemma : tactic =>
  `(tactic|
    (simp [$spec, ContractResult.snd, Verity.Specs.sameAddrMapContext,
      Verity.Specs.sameStorageMapContext, Verity.Specs.sameContext, Verity.Specs.sameStorage,
      Verity.Specs.sameStorageAddr, Verity.Specs.sameStorageMap, $extra]))

macro "verity_arith" : tactic =>
  `(tactic|
    first
      | simpa using
          (Verity.Proofs.Stdlib.Math.safeAdd_none _ _ (by first | assumption | omega))
      | simpa using
          (Verity.Proofs.Stdlib.Math.safeSub_none _ _ (by first | assumption | omega))
      | simpa using
          (Verity.Proofs.Stdlib.Math.safeMul_none _ _ (by first | assumption | omega))
      | simpa using
          (Verity.Proofs.Stdlib.Automation.safeAdd_some_val _ _ (by first | assumption | omega))
      | simpa using
          (Verity.Proofs.Stdlib.Automation.safeSub_some_val _ _ (by first | assumption | omega))
      | simpa using
          (Verity.Proofs.Stdlib.Math.safeMul_some _ _ (by first | assumption | omega))
      | simpa [safeAdd_some_iff_le, safeAdd_none_iff_gt,
          safeSub_some_iff_ge, safeSub_none_iff_lt,
          safeMul_some_iff_le, safeMul_none_iff_gt]
      | omega)

macro_rules
  | `(tactic| verity_view_frame) =>
      `(tactic|
        (try intros
         simp only [verity_unfold_simps]
         try exact Verity.Specs.viewPreservesState_rfl _
         all_goals (try split) <;> (try split) <;>
           try exact Verity.Specs.viewPreservesState_rfl _
         try simp [Verity.Specs.viewPreservesState, Verity.Specs.sameAllStorage,
           Verity.Specs.sameContext, Verity.Specs.sameEvents,
           Verity.Specs.sameKnownAddresses, Verity.Specs.sameStorage,
           Verity.Specs.sameStorageAddr, Verity.Specs.sameStorageMap,
           Verity.Specs.sameStorageMapUint, Verity.Specs.sameStorageMap2,
           Verity.Specs.sameStorageArray]))
  | `(tactic| verity_view_frame $fn:simpLemma) =>
      `(tactic|
        (try intros
         simp only [verity_unfold_simps, $fn]
         try exact Verity.Specs.viewPreservesState_rfl _
         all_goals (try split) <;> (try split) <;>
           try exact Verity.Specs.viewPreservesState_rfl _
         try simp [Verity.Specs.viewPreservesState, Verity.Specs.sameAllStorage,
           Verity.Specs.sameContext, Verity.Specs.sameEvents,
           Verity.Specs.sameKnownAddresses, Verity.Specs.sameStorage,
           Verity.Specs.sameStorageAddr, Verity.Specs.sameStorageMap,
           Verity.Specs.sameStorageMapUint, Verity.Specs.sameStorageMap2,
           Verity.Specs.sameStorageArray]))
  | `(tactic| verity_view_frame $fn:simpLemma with $extra,*) =>
      `(tactic|
        (try intros
         simp only [verity_unfold_simps, $fn, $extra,*]
         try exact Verity.Specs.viewPreservesState_rfl _
         all_goals (try split) <;> (try split) <;>
           try exact Verity.Specs.viewPreservesState_rfl _
         try simp [Verity.Specs.viewPreservesState, Verity.Specs.sameAllStorage,
           Verity.Specs.sameContext, Verity.Specs.sameEvents,
           Verity.Specs.sameKnownAddresses, Verity.Specs.sameStorage,
           Verity.Specs.sameStorageAddr, Verity.Specs.sameStorageMap,
           Verity.Specs.sameStorageMapUint, Verity.Specs.sameStorageMap2,
           Verity.Specs.sameStorageArray]))

/-!
## Index Normalization Helpers

Lean 4.22 is less eager to reduce `List.findIdx?` inside large interpreter terms.
These simp lemmas keep field/parameter lookup deterministic in spec-correctness proofs.
-/

-- Field-level findIdx simp lemmas are generated per `verity_contract` by the macro
-- elaborator (Issue #1155), including parameter-list lemmas for constructors/functions.

/-!
## Contract Result Lemmas
-/

-- Lemmas for isSuccess
@[simp]
theorem isSuccess_success {α : Type} (a : α) (s : ContractState) :
    (ContractResult.success a s).isSuccess = true := rfl

@[simp]
theorem isSuccess_revert {α : Type} (msg : String) (s : ContractState) :
    (ContractResult.revert msg s : ContractResult α).isSuccess = false := rfl

-- Lemmas for getState
@[simp]
theorem getState_success {α : Type} (a : α) (s : ContractState) :
    (ContractResult.success a s).getState = s := rfl

@[simp]
theorem getState_revert {α : Type} (msg : String) (s : ContractState) :
    (ContractResult.revert msg s : ContractResult α).getState = s := rfl

/-!
## Basic Storage Operation Lemmas
-/

-- getStorage preserves state
theorem getStorage_runState (slot : StorageSlot Uint256) (state : ContractState) :
    (getStorage slot).runState state = state := by
  simp [getStorage, Contract.runState]

-- setStorage updates the state
theorem setStorage_runState (slot : StorageSlot Uint256) (value : Uint256) (state : ContractState) :
    (setStorage slot value).runState state =
      state.writeSlot slot.slot value := by
  simp [setStorage, Contract.runState, ContractState.writeSlot]

-- getStorage returns correct value
theorem getStorage_runValue (slot : StorageSlot Uint256) (state : ContractState) :
    (getStorage slot).runValue state = state.storage slot.slot := by
  simp [getStorage, Contract.runValue, ContractState.readSlot]

-- After setStorage, getStorage returns the value
theorem setStorage_getStorage (slot : StorageSlot Uint256) (value : Uint256) (state : ContractState) :
    (getStorage slot).runValue ((setStorage slot value).runState state) = value := by
  simp [setStorage, getStorage, Contract.runState, Contract.runValue, ContractState.writeSlot,
    ContractState.readSlot, ContractState.storage]

-- getStorage for different slot is unchanged after setStorage
theorem setStorage_getStorage_diff (slot1 slot2 : StorageSlot Uint256) (value : Uint256) (state : ContractState)
    (h : slot1.slot ≠ slot2.slot) :
    (getStorage slot2).runValue ((setStorage slot1 value).runState state) =
    state.storage slot2.slot := by
  unfold setStorage getStorage Contract.runState Contract.runValue
  by_cases h_eq : slot2.slot = slot1.slot
  · exact (h h_eq.symm).elim
  · simp [h_eq, ContractState.writeSlot, ContractState.readSlot, ContractState.storage]

/-!
## Monadic Composition Lemmas

These lemmas help with proving correctness of functions that use bind (>>=).
-/

-- Left identity: binding a pure value is just function application.
@[simp]
theorem bind_pure_left {α β : Type} (a : α) (f : α → Contract β) :
    Verity.bind (Verity.pure a) f = f a := by
  funext state
  simp [Verity.bind, Verity.pure]

-- Right identity: binding to pure preserves the original computation.
@[simp]
theorem bind_pure_right {α : Type} (m : Contract α) :
    Verity.bind m Verity.pure = m := by
  funext state
  unfold Verity.bind Verity.pure
  cases h : m state <;> simp

-- Associativity: nested binds can be reassociated.
@[simp]
theorem bind_assoc {α β γ : Type} (m : Contract α) (f : α → Contract β) (g : β → Contract γ) :
    Verity.bind (Verity.bind m f) g = Verity.bind m (fun a => Verity.bind (f a) g) := by
  funext state
  unfold Verity.bind
  cases h : m state <;> simp

-- Lemma for getStorage >> setStorage pattern (the most common pattern)
@[simp]
theorem bind_getStorage_setStorage_runState (slot : StorageSlot Uint256) (f : Uint256 → Uint256) (state : ContractState) :
    (Verity.bind (getStorage slot) (fun val => setStorage slot (f val))).runState state =
      state.writeSlot slot.slot (f (state.storage slot.slot)) := by
  simp [Verity.bind, getStorage, setStorage, Contract.runState, ContractState.writeSlot,
    ContractState.readSlot]

-- Bind success propagation: if bind succeeds, first action succeeded
theorem bind_isSuccess_left {α β : Type} (m1 : Contract α) (m2 : α → Contract β) (state : ContractState) :
    ((Verity.bind m1 m2).run state).isSuccess = true →
    (m1.run state).isSuccess = true := by
  intro h_success
  -- Strategy: case analysis on m1 state
  -- Note: Contract.run is just function application, so m1.run state = m1 state
  cases h_result : m1 state
  case success val s' =>
    -- When m1 succeeds, isSuccess is trivially true
    simp [Contract.run, h_result, ContractResult.isSuccess]
  case revert msg s' =>
    -- When m1 reverts, bind also reverts, so isSuccess = false
    -- This contradicts h_success
    unfold Verity.bind Contract.run at h_success
    simp [h_result, ContractResult.isSuccess] at h_success

/-!
## Address Storage Lemmas
-/

-- getStorageAddr preserves state
theorem getStorageAddr_runState (slot : StorageSlot Address) (state : ContractState) :
    (getStorageAddr slot).runState state = state := by
  simp [getStorageAddr, Contract.runState]

-- setStorageAddr updates the state
theorem setStorageAddr_runState (slot : StorageSlot Address) (value : Address) (state : ContractState) :
    (setStorageAddr slot value).runState state =
      state.writeAddrSlot slot.slot value := by
  simp [setStorageAddr, Contract.runState, ContractState.writeAddrSlot]

-- getStorageAddr returns correct value
theorem getStorageAddr_runValue (slot : StorageSlot Address) (state : ContractState) :
    (getStorageAddr slot).runValue state = state.storageAddr slot.slot := by
  simp [getStorageAddr, Contract.runValue, ContractState.readAddrSlot]

/-!
## Address Encoding Lemmas
-/

-- Address values are always less than 2^160 (the address modulus).
theorem addressToNat_lt_modulus (addr : Address) :
    addr.val < Core.ADDRESS_MODULUS := addr.isLt

@[simp] theorem addressToNat_mod_eq (addr : Address) :
    addr.val % Core.ADDRESS_MODULUS = addr.val := by
  exact Nat.mod_eq_of_lt (addressToNat_lt_modulus addr)

@[simp] theorem addressToNat_beq_self (addr : Address) :
    (addr.val == addr.val) = true := by
  simp

-- Injectivity is now provable from the structure definition (was an axiom!).
theorem addressToNat_injective :
    ∀ (a b : Address), a.val = b.val → a = b :=
  fun _ _ h => Verity.Core.Address.ext h

/-!
## Mapping Operation Lemmas
-/

-- getMapping preserves state
theorem getMapping_runState (slot : StorageSlot (Address → Uint256)) (key : Address) (state : ContractState) :
    (getMapping slot key).runState state = state := by
  simp [getMapping, Contract.runState]

-- getMapping returns correct value
theorem getMapping_runValue (slot : StorageSlot (Address → Uint256)) (key : Address) (state : ContractState) :
    (getMapping slot key).runValue state = state.storageMap slot.slot key := by
  simp [getMapping, Contract.runValue, ContractState.readMap]

/-!
## List Lookup Lemmas
-/

-- Local variable lookups in the spec interpreter.
@[simp] theorem lookup_senderBal (recipientBal senderBal : Nat) :
    (List.lookup "senderBal" [("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      senderBal := by
  simp [List.lookup]

@[simp] theorem lookup_recipientBal (recipientBal senderBal : Nat) :
    (List.lookup "recipientBal" [("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      recipientBal := by
  simp [List.lookup]

-- Local variable lookups when transfer introduces sameAddr/delta/amountDelta.
@[simp] theorem lookup_senderBal_with_delta (amountDelta delta sameAddr recipientBal senderBal : Nat) :
    (List.lookup "senderBal"
        [("amountDelta", amountDelta), ("delta", delta), ("sameAddr", sameAddr),
          ("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      senderBal := by
  simp [List.lookup]

@[simp] theorem lookup_recipientBal_with_delta (amountDelta delta sameAddr recipientBal senderBal : Nat) :
    (List.lookup "recipientBal"
        [("amountDelta", amountDelta), ("delta", delta), ("sameAddr", sameAddr),
          ("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      recipientBal := by
  simp [List.lookup]

@[simp] theorem lookup_sameAddr_with_delta (amountDelta delta sameAddr recipientBal senderBal : Nat) :
    (List.lookup "sameAddr"
        [("amountDelta", amountDelta), ("delta", delta), ("sameAddr", sameAddr),
          ("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      sameAddr := by
  simp [List.lookup]

@[simp] theorem lookup_delta_with_delta (amountDelta delta sameAddr recipientBal senderBal : Nat) :
    (List.lookup "delta"
        [("amountDelta", amountDelta), ("delta", delta), ("sameAddr", sameAddr),
          ("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      delta := by
  simp [List.lookup]

@[simp] theorem lookup_amountDelta_with_delta (amountDelta delta sameAddr recipientBal senderBal : Nat) :
    (List.lookup "amountDelta"
        [("amountDelta", amountDelta), ("delta", delta), ("sameAddr", sameAddr),
          ("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      amountDelta := by
  simp [List.lookup]

-- Mapping lookups for two-address lists.
@[simp] theorem lookup_addr_first (k1 k2 v1 v2 : Nat) :
    (List.lookup k1 [(k1, v1), (k2, v2)]).getD 0 = v1 := by
  simp [List.lookup]

@[simp] theorem lookup_addr_second (k1 k2 v1 v2 : Nat) (h : k1 ≠ k2) :
    (List.lookup k2 [(k1, v1), (k2, v2)]).getD 0 = v2 := by
  cases h_eq : (k2 == k1) with
  | false =>
      simp [List.lookup, h_eq]
  | true =>
      have : k2 = k1 := by
        exact (beq_iff_eq).1 h_eq
      exact (False.elim (h this.symm))

-- Slot lookups for the common two-slot layout.
@[simp] theorem lookup_slot_first (v0 v1 : Nat) :
    (List.lookup 0 [(0, v0), (1, v1)]).getD 0 = v0 := by
  simp [List.lookup]

@[simp] theorem lookup_slot_second (v0 v1 : Nat) :
    (List.lookup 1 [(0, v0), (1, v1)]).getD 0 = v1 := by
  simp [List.lookup]

/-!
## msgSender Lemmas
-/

-- msgSender preserves state
theorem msgSender_runState (state : ContractState) :
    msgSender.runState state = state := by
  simp [msgSender, Contract.runState]

-- msgSender returns sender
theorem msgSender_runValue (state : ContractState) :
    msgSender.runValue state = state.sender := by
  simp [msgSender, Contract.runValue]

/-!
## require Lemmas
-/

-- require with true condition is success
theorem require_true_isSuccess (cond : Bool) (msg : String) (state : ContractState)
    (h : cond = true) :
    ((require cond msg).run state).isSuccess = true := by
  simp [h]

-- require with false condition is not success
theorem require_false_isSuccess (cond : Bool) (msg : String) (state : ContractState)
    (h : cond = false) :
    ((require cond msg).run state).isSuccess = false := by
  simp [h]

-- If require succeeds, the condition must have been true (reverse direction)
theorem require_success_implies_cond (cond : Bool) (msg : String) (state : ContractState) :
    ((require cond msg).run state).isSuccess = true →
    cond = true := by
  intro h_success
  -- Strategy: case analysis on cond
  cases cond
  case false =>
    -- When cond = false, require returns revert, which has isSuccess = false
    -- This contradicts h_success
    unfold require Contract.run at h_success
    simp [ContractResult.isSuccess] at h_success
  case true =>
    -- When cond = true, we're done
    rfl

-- require preserves state regardless of branch
@[simp] theorem require_state (cond : Bool) (msg : String) (state : ContractState) :
    (require cond msg).runState state = state := by
  by_cases h : cond
  · simp [require, Contract.runState, h]
  · simp [require, Contract.runState, h]

-- If the guard is true, binding after require is exactly the continuation.
@[simp] theorem require_bind_true_run (cond : Bool) (msg : String) (k : Unit → Contract α)
    (state : ContractState) (h : cond = true) :
    (Verity.bind (require cond msg) k).run state = (k ()).run state := by
  subst h
  simp [Verity.bind, require, Contract.run]

-- If the guard is false, bind short-circuits to revert and never runs continuation.
@[simp] theorem require_bind_false_run (cond : Bool) (msg : String) (k : Unit → Contract α)
    (state : ContractState) (h : cond = false) :
    (Verity.bind (require cond msg) k).run state = ContractResult.revert msg state := by
  subst h
  simp [Verity.bind, require, Contract.run]

/-!
## Address Equality Lemmas
-/

-- Address beq reflects equality.
theorem address_beq_eq_true_iff_eq (a b : Address) :
    (a == b) = true ↔ a = b := by
  simp only [beq_iff_eq]

/-- Address beq is false when addresses are not equal. -/
theorem address_beq_false_of_ne (a b : Address) (h : a ≠ b) :
    (a == b) = false :=
  beq_eq_false_iff_ne.mpr h

/-- Distinct addresses have distinct Nat values. -/
theorem addressToNat_ne_of_ne (a b : Address) (h : a ≠ b) :
    a.val ≠ b.val := by
  intro h_nat
  exact h (addressToNat_injective a b h_nat)

/-- Address val beq is false when addresses are not equal. -/
theorem addressToNat_beq_false_of_ne (a b : Address) (h : a ≠ b) :
    (a.val == b.val) = false :=
  beq_eq_false_iff_ne.mpr (addressToNat_ne_of_ne a b h)

/-!
## Uint256 Arithmetic Lemmas
-/

/-- 1 mod modulus is 1 (used pervasively in spec interpreter proofs). -/
@[simp] theorem one_mod_modulus : (1 % Verity.Core.Uint256.modulus) = 1 :=
  Nat.mod_eq_of_lt (by decide : (1 : Nat) < Verity.Core.Uint256.modulus)

/-- EVM.Uint256.add is definitionally equal to HAdd (+). -/
theorem evm_add_eq_hadd (a b : Verity.Core.Uint256) :
    Verity.EVM.Uint256.add a b = a + b := rfl

-- Helper: EVM add (Uint256) matches modular Nat addition.
theorem uint256_add_val (a : Verity.Core.Uint256) (amount : Nat) :
    (Verity.EVM.Uint256.add a (Verity.Core.Uint256.ofNat amount)).val =
      (a.val + amount) % Verity.Core.Uint256.modulus := by
  cases a with
  | mk aval hlt =>
      have haval : aval % Verity.Core.Uint256.modulus = aval := Nat.mod_eq_of_lt hlt
      calc
        (Verity.EVM.Uint256.add (Verity.Core.Uint256.mk aval hlt)
              (Verity.Core.Uint256.ofNat amount)).val
            = (aval + amount % Verity.Core.Uint256.modulus) % Verity.Core.Uint256.modulus := by
                simp [Verity.EVM.Uint256.add, Verity.Core.Uint256.add,
                  Verity.Core.Uint256.val_ofNat, -Verity.Core.Uint256.ofNat_add]
        _ = ((aval % Verity.Core.Uint256.modulus) + (amount % Verity.Core.Uint256.modulus))
              % Verity.Core.Uint256.modulus := by
                simp [haval]
        _ = (aval + amount) % Verity.Core.Uint256.modulus := by
                exact (Nat.add_mod _ _ _).symm

-- Helper: EVM sub (Uint256) matches the EDSL modular subtraction formula.
theorem uint256_sub_val (a : Verity.Core.Uint256) (amount : Nat) :
    (Verity.EVM.Uint256.sub a (Verity.Core.Uint256.ofNat amount)).val =
      (if amount % Verity.Core.Uint256.modulus ≤ a.val then
        a.val - amount % Verity.Core.Uint256.modulus
      else
        Verity.Core.Uint256.modulus -
          (amount % Verity.Core.Uint256.modulus - a.val)) := by
  have h_amount_lt : amount % Verity.Core.Uint256.modulus < Verity.Core.Uint256.modulus := by
    exact Nat.mod_lt _ Verity.Core.Uint256.modulus_pos
  by_cases h_le : amount % Verity.Core.Uint256.modulus ≤ a.val
  · have h_lt : a.val - amount % Verity.Core.Uint256.modulus < Verity.Core.Uint256.modulus := by
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
    simp [Verity.EVM.Uint256.sub, Verity.Core.Uint256.sub, h_le,
      Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_lt]
  · have h_not_le : ¬ amount % Verity.Core.Uint256.modulus ≤ a.val := h_le
    have h_pos : 0 < amount % Verity.Core.Uint256.modulus - a.val := by
      exact Nat.sub_pos_of_lt (Nat.lt_of_not_ge h_not_le)
    have h_le_x : amount % Verity.Core.Uint256.modulus - a.val ≤ Verity.Core.Uint256.modulus := by
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_amount_lt)
    have h_lt_add :
        Verity.Core.Uint256.modulus <
          (amount % Verity.Core.Uint256.modulus - a.val) + Verity.Core.Uint256.modulus := by
      exact Nat.lt_add_of_pos_left h_pos
    have h_lt :
        Verity.Core.Uint256.modulus - (amount % Verity.Core.Uint256.modulus - a.val) <
          Verity.Core.Uint256.modulus := by
      exact Nat.sub_lt_left_of_lt_add h_le_x h_lt_add
    simp [Verity.EVM.Uint256.sub, Verity.Core.Uint256.sub, h_not_le,
      Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_lt]

-- Helper: EVM sub (Uint256) matches Nat subtraction when no underflow.
theorem uint256_sub_val_of_le (a : Verity.Core.Uint256) (amount : Nat)
    (h : a.val ≥ amount) :
    (Verity.EVM.Uint256.sub a (Verity.Core.Uint256.ofNat amount)).val =
      a.val - amount := by
  have h_amount_lt : amount < Verity.Core.Uint256.modulus := by
    exact Nat.lt_of_le_of_lt h a.isLt
  have h_le : (Verity.Core.Uint256.ofNat amount : Nat) ≤ (a : Nat) := by
    simp [Nat.mod_eq_of_lt h_amount_lt, h]
  have h_sub : ((Verity.EVM.Uint256.sub a (Verity.Core.Uint256.ofNat amount)
      : Verity.Core.Uint256) : Nat) = (a : Nat) - (Verity.Core.Uint256.ofNat amount : Nat) := by
    exact Verity.EVM.Uint256.sub_eq_of_le h_le
  simp [Nat.mod_eq_of_lt h_amount_lt] at h_sub
  simpa using h_sub

/-!
## Safe Arithmetic Lemmas

Helper lemmas for reasoning about safe arithmetic operations (safeAdd, safeSub).
-/

-- safeSub returns Some iff no underflow
theorem safeSub_some_iff_ge (a b : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.safeSub a b).isSome ↔ (a : Nat) ≥ (b : Nat) := by
  unfold Verity.Stdlib.Math.safeSub
  split
  · simp; rename_i h; omega
  · simp; rename_i h; omega

-- safeSub returns None iff underflow
theorem safeSub_none_iff_lt (a b : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.safeSub a b).isNone ↔ (a : Nat) < (b : Nat) := by
  unfold Verity.Stdlib.Math.safeSub
  split
  · simp; rename_i h; omega
  · simp; rename_i h; omega

-- When safeSub succeeds, it returns the correct value
theorem safeSub_some_val (a b : Verity.Core.Uint256) (h : (a : Nat) ≥ (b : Nat)) :
    Verity.Stdlib.Math.safeSub a b = some (a - b) := by
  unfold Verity.Stdlib.Math.safeSub
  have h_not : ¬((b : Nat) > (a : Nat)) := by omega
  simp [h_not]

-- safeAdd returns Some iff no overflow
theorem safeAdd_some_iff_le (a b : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.safeAdd a b).isSome ↔
    (a : Nat) + (b : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256 := by
  unfold Verity.Stdlib.Math.safeAdd
  by_cases h : (a : Nat) + (b : Nat) > Verity.Stdlib.Math.MAX_UINT256
  case pos =>
    constructor
    · intro h_some
      simp [h] at h_some
    · intro h_le
      omega
  case neg =>
    constructor
    · intro _
      omega
    · intro _
      simp [h]

-- safeAdd returns None iff overflow
theorem safeAdd_none_iff_gt (a b : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.safeAdd a b).isNone ↔
    (a : Nat) + (b : Nat) > Verity.Stdlib.Math.MAX_UINT256 := by
  unfold Verity.Stdlib.Math.safeAdd
  by_cases h : (a : Nat) + (b : Nat) > Verity.Stdlib.Math.MAX_UINT256
  case pos =>
    constructor
    · intro _; exact h
    · intro _; simp [h]
  case neg =>
    constructor
    · intro h_none
      simp [h] at h_none
    · intro h_gt
      exact absurd h_gt h

-- When safeAdd succeeds, it returns the correct value
theorem safeAdd_some_val (a b : Verity.Core.Uint256)
    (h : (a : Nat) + (b : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256) :
    Verity.Stdlib.Math.safeAdd a b = some (a + b) := by
  unfold Verity.Stdlib.Math.safeAdd
  have h_not : ¬((a : Nat) + (b : Nat) > Verity.Stdlib.Math.MAX_UINT256) := by omega
  simp [h_not]

-- safeMul returns Some iff no overflow
theorem safeMul_some_iff_le (a b : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.safeMul a b).isSome ↔
    (a : Nat) * (b : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256 := by
  unfold Verity.Stdlib.Math.safeMul
  by_cases h : (a : Nat) * (b : Nat) > Verity.Stdlib.Math.MAX_UINT256
  · constructor
    · intro h_some
      simp [h] at h_some
    · intro h_le
      omega
  · constructor
    · intro _
      omega
    · intro _
      simp [h]

-- safeMul returns None iff overflow
theorem safeMul_none_iff_gt (a b : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.safeMul a b).isNone ↔
    (a : Nat) * (b : Nat) > Verity.Stdlib.Math.MAX_UINT256 := by
  unfold Verity.Stdlib.Math.safeMul
  by_cases h : (a : Nat) * (b : Nat) > Verity.Stdlib.Math.MAX_UINT256
  · constructor
    · intro _
      exact h
    · intro _
      simp [h]
  · constructor
    · intro h_none
      simp [h] at h_none
    · intro h_gt
      exact absurd h_gt h

-- Full-precision floor mulDiv succeeds iff the divisor is nonzero and the quotient fits.
theorem mulDiv512Down?_some_iff (a b c : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.mulDiv512Down? a b c).isSome ↔
    (c : Nat) ≠ 0 ∧
      ((a : Nat) * (b : Nat)) / (c : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256 := by
  unfold Verity.Stdlib.Math.mulDiv512Down?
  by_cases hC : (c : Nat) = 0
  · simp [hC]
  · by_cases hOverflow : ((a : Nat) * (b : Nat)) / (c : Nat) > Verity.Stdlib.Math.MAX_UINT256
    · constructor
      · intro h_some
        simp [hC, hOverflow] at h_some
      · intro h_fit
        omega
    · constructor
      · intro _
        exact ⟨hC, Nat.le_of_not_gt hOverflow⟩
      · intro _
        simp [hC, hOverflow]

-- Full-precision floor mulDiv rejects iff the divisor is zero or the quotient overflows.
theorem mulDiv512Down?_none_iff (a b c : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.mulDiv512Down? a b c).isNone ↔
    (c : Nat) = 0 ∨
      Verity.Stdlib.Math.MAX_UINT256 <
        ((a : Nat) * (b : Nat)) / (c : Nat) := by
  unfold Verity.Stdlib.Math.mulDiv512Down?
  by_cases hC : (c : Nat) = 0
  · simp [hC]
  · by_cases hOverflow : ((a : Nat) * (b : Nat)) / (c : Nat) > Verity.Stdlib.Math.MAX_UINT256
    · simp [hC, hOverflow]
    · constructor
      · intro h_none
        simp [hC, hOverflow] at h_none
      · intro h_reject
        rcases h_reject with h_zero | h_gt
        · exact False.elim (hC h_zero)
        · exact False.elim (hOverflow h_gt)

-- Full-precision ceil mulDiv succeeds iff the divisor is nonzero and the rounded quotient fits.
theorem mulDiv512Up?_some_iff (a b c : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.mulDiv512Up? a b c).isSome ↔
    (c : Nat) ≠ 0 ∧
      (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) ≤
        Verity.Stdlib.Math.MAX_UINT256 := by
  unfold Verity.Stdlib.Math.mulDiv512Up?
  by_cases hC : (c : Nat) = 0
  · simp [hC]
  · by_cases hOverflow :
      (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) >
        Verity.Stdlib.Math.MAX_UINT256
    · constructor
      · intro h_some
        simp [hC, hOverflow] at h_some
      · intro h_fit
        omega
    · constructor
      · intro _
        exact ⟨hC, Nat.le_of_not_gt hOverflow⟩
      · intro _
        simp [hC, hOverflow]

-- Full-precision ceil mulDiv rejects iff the divisor is zero or the rounded quotient overflows.
theorem mulDiv512Up?_none_iff (a b c : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.mulDiv512Up? a b c).isNone ↔
    (c : Nat) = 0 ∨
      Verity.Stdlib.Math.MAX_UINT256 <
        (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) := by
  unfold Verity.Stdlib.Math.mulDiv512Up?
  by_cases hC : (c : Nat) = 0
  · simp [hC]
  · by_cases hOverflow :
      (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) >
        Verity.Stdlib.Math.MAX_UINT256
    · simp [hC, hOverflow]
    · constructor
      · intro h_none
        simp [hC, hOverflow] at h_none
      · intro h_reject
        rcases h_reject with h_zero | h_gt
        · exact False.elim (hC h_zero)
        · exact False.elim (hOverflow h_gt)

example (a b c : Verity.Core.Uint256)
    (hC : (c : Nat) ≠ 0)
    (hFit : ((a : Nat) * (b : Nat)) / (c : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256) :
    (Verity.Stdlib.Math.mulDiv512Down? a b c).isSome := by
  exact (mulDiv512Down?_some_iff a b c).mpr ⟨hC, hFit⟩

example (a b c : Verity.Core.Uint256)
    (hOverflow : Verity.Stdlib.Math.MAX_UINT256 <
      (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat)) :
    (Verity.Stdlib.Math.mulDiv512Up? a b c).isNone := by
  exact (mulDiv512Up?_none_iff a b c).mpr (Or.inr hOverflow)

/-!
## Modular Arithmetic Wraparound Lemmas

These lemmas handle the case where modular addition causes wraparound at MAX_UINT256.
-/

-- Addition by 1 preserves order iff no overflow occurs
theorem add_one_preserves_order_iff_no_overflow (a : Verity.Core.Uint256) :
    ((Verity.Core.Uint256.add a 1) : Nat) > (a : Nat) ↔
    (a : Nat) < Verity.Core.MAX_UINT256 := by
  have hm := Verity.Core.Uint256.max_uint256_succ_eq_modulus
  have hlt : (a : Nat) < Verity.Core.Uint256.modulus := a.isLt
  have hval : ((Verity.Core.Uint256.add a 1) : Nat) =
      ((a : Nat) + 1) % Verity.Core.Uint256.modulus := by
    simp [Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat]
  rw [hval]
  by_cases h : (a : Nat) + 1 < Verity.Core.Uint256.modulus
  · rw [Nat.mod_eq_of_lt h]
    omega
  · rw [show (a : Nat) + 1 = Verity.Core.Uint256.modulus by omega, Nat.mod_self]
    omega

/-!
## Well-Formedness Preservation
-/

/-- Generic: any state predicate is preserved when the operation does not change state.
    Eliminates the repeated 3-line pattern:
    `have h_pres := op_preserves_state s; rw [h_pres]; exact h`
    found in every read-only `*_preserves_wellformedness` proof. -/
theorem wf_of_state_eq (P : ContractState → Prop)
    (s s' : ContractState) (h_eq : s' = s) (h : P s) : P s' := by
  rw [h_eq]; exact h

/-- Generic frame-preservation helper for nonzero context/owner fields.
    This captures the common write-case pattern used to rebuild
    `WellFormedState`-style invariants after proving frame equalities. -/
theorem wf_preservation_of_frame
    (s s' : ContractState)
    (h_sender_nz : s.sender ≠ 0)
    (h_this_nz : s.thisAddress ≠ 0)
    (h_owner_nz : s.storageAddr 0 ≠ 0)
    (h_sender : s'.sender = s.sender)
    (h_this : s'.thisAddress = s.thisAddress)
    (h_owner : s'.storageAddr 0 = s.storageAddr 0) :
    s'.sender ≠ 0 ∧ s'.thisAddress ≠ 0 ∧ s'.storageAddr 0 ≠ 0 := by
  constructor
  · exact h_sender ▸ h_sender_nz
  constructor
  · exact h_this ▸ h_this_nz
  · exact h_owner ▸ h_owner_nz

/-!
## Generic setStorage Preservation

Facts about `setStorage` that hold for ANY slot — not specific to a named slot
like `count` or `storedData`. These eliminate per-contract duplication of
`setStorage_preserves_addr_storage`, `setStorage_preserves_map_storage`, etc.
-/

/-- setStorage on any uint256 slot preserves the address storage. -/
theorem setStorage_preserves_storageAddr (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.storageAddr = state.storageAddr := by
  change (state.writeSlot slot.slot value).storageAddr = state.storageAddr
  exact ContractState.storageAddr_writeSlot state slot.slot value

/-- setStorage on any uint256 slot preserves the mapping storage. -/
theorem setStorage_preserves_storageMap (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.storageMap = state.storageMap := by
  change (state.writeSlot slot.slot value).storageMap = state.storageMap
  exact ContractState.storageMap_writeSlot state slot.slot value

/-- setStorage on any uint256 slot preserves the sender. -/
theorem setStorage_preserves_sender (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.sender = state.sender := by
  simp [ContractState.writeSlot]

/-- setStorage on any uint256 slot preserves the contract address. -/
theorem setStorage_preserves_thisAddress (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.thisAddress = state.thisAddress := by
  simp [ContractState.writeSlot]

/-- setStorage on any uint256 slot preserves other uint256 slots. -/
theorem setStorage_preserves_other_storage (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) (n : Nat) (h : n ≠ slot.slot) :
    ((setStorage slot value).run state).snd.storage n = state.storage n := by
  simp [ContractState.writeSlot, ContractState.storage, h]

/-- setStorageAddr on any address slot preserves the uint256 storage. -/
theorem setStorageAddr_preserves_storage (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.storage = state.storage := by
  change (state.writeAddrSlot slot.slot value).storage = state.storage
  exact ContractState.storage_writeAddrSlot state slot.slot value

/-- setStorageAddr on any address slot preserves the mapping storage. -/
theorem setStorageAddr_preserves_storageMap (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.storageMap = state.storageMap := by
  change (state.writeAddrSlot slot.slot value).storageMap = state.storageMap
  exact ContractState.storageMap_writeAddrSlot state slot.slot value

/-- setStorageAddr on any address slot preserves the sender. -/
theorem setStorageAddr_preserves_sender (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.sender = state.sender := by
  simp [ContractState.writeAddrSlot]

/-- setStorageAddr on any address slot preserves the contract address. -/
theorem setStorageAddr_preserves_thisAddress (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.thisAddress = state.thisAddress := by
  simp [ContractState.writeAddrSlot]

/-!
## Generic setMapping Preservation
-/

/-- setMapping preserves the uint256 storage. -/
theorem setMapping_preserves_storage (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.storage = state.storage := by
  change (state.writeMap slot.slot key value).storage = state.storage
  exact ContractState.storage_writeMap state slot.slot key value

/-- setMapping preserves the address storage. -/
theorem setMapping_preserves_storageAddr (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.storageAddr = state.storageAddr := by
  change (state.writeMap slot.slot key value).storageAddr = state.storageAddr
  exact ContractState.storageAddr_writeMap state slot.slot key value

/-- setMapping preserves the sender. -/
theorem setMapping_preserves_sender (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.sender = state.sender := by
  simp [ContractState.writeMap]

/-- setMapping preserves the contract address. -/
theorem setMapping_preserves_thisAddress (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.thisAddress = state.thisAddress := by
  simp [ContractState.writeMap]

/-!
## Generic msgValue / blockTimestamp / blockNumber / knownAddresses Preservation

Storage mutations never touch context fields or (for non-mapping ops) knownAddresses.
-/

/-- setStorage preserves msgValue. -/
theorem setStorage_preserves_msgValue (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.msgValue = state.msgValue := by
  simp [ContractState.writeSlot]

/-- setStorageAddr preserves msgValue. -/
theorem setStorageAddr_preserves_msgValue (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.msgValue = state.msgValue := by
  simp [ContractState.writeAddrSlot]

/-- setMapping preserves msgValue. -/
theorem setMapping_preserves_msgValue (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.msgValue = state.msgValue := by
  simp [ContractState.writeMap]

/-- setStorage preserves blockTimestamp. -/
theorem setStorage_preserves_blockTimestamp (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.blockTimestamp = state.blockTimestamp := by
  simp [ContractState.writeSlot]

/-- setStorageAddr preserves blockTimestamp. -/
theorem setStorageAddr_preserves_blockTimestamp (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.blockTimestamp = state.blockTimestamp := by
  simp [ContractState.writeAddrSlot]

/-- setMapping preserves blockTimestamp. -/
theorem setMapping_preserves_blockTimestamp (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.blockTimestamp = state.blockTimestamp := by
  simp [ContractState.writeMap]

/-- setStorage preserves blockNumber. -/
theorem setStorage_preserves_blockNumber (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.blockNumber = state.blockNumber := by
  simp [ContractState.writeSlot]

/-- setStorageAddr preserves blockNumber. -/
theorem setStorageAddr_preserves_blockNumber (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.blockNumber = state.blockNumber := by
  simp [ContractState.writeAddrSlot]

/-- setMapping preserves blockNumber. -/
theorem setMapping_preserves_blockNumber (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.blockNumber = state.blockNumber := by
  simp [ContractState.writeMap]

/-- setStorage preserves knownAddresses. -/
theorem setStorage_preserves_knownAddresses (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.knownAddresses = state.knownAddresses := by
  simp [ContractState.writeSlot]

/-- setStorageAddr preserves knownAddresses. -/
theorem setStorageAddr_preserves_knownAddresses (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.knownAddresses = state.knownAddresses := by
  simp [ContractState.writeAddrSlot]

/-!
## Generic Event Preservation

Storage mutations never touch the `events` append-only log.
-/

/-- setStorage on any uint256 slot preserves the event log. -/
theorem setStorage_preserves_events (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.events = state.events := by
  simp [ContractState.writeSlot]

/-- setStorageAddr on any address slot preserves the event log. -/
theorem setStorageAddr_preserves_events (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.events = state.events := by
  simp [ContractState.writeAddrSlot]

/-- setMapping preserves the event log. -/
theorem setMapping_preserves_events (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.events = state.events := by
  simp [ContractState.writeMap]

/-!
## Event Emission Helpers

Direct automation lemmas for `emitEvent`.
-/

/-- Emitting an event always succeeds. -/
@[simp] theorem emitEvent_isSuccess (name : String) (args indexedArgs : List Uint256)
    (state : ContractState) :
    ((emitEvent name args indexedArgs).run state).isSuccess = true := by
  simp

/-- Emitting an event returns unit. -/
@[simp] theorem emitEvent_runValue (name : String) (args indexedArgs : List Uint256)
    (state : ContractState) :
    (emitEvent name args indexedArgs).runValue state = () := by
  simp [emitEvent, Contract.runValue]

/-- Emitting an event updates only the event log by appending one entry. -/
@[simp] theorem emitEvent_runState (name : String) (args indexedArgs : List Uint256)
    (state : ContractState) :
    (emitEvent name args indexedArgs).runState state =
      { state with events := state.events ++ [{ name := name, args := args, indexedArgs := indexedArgs }] } := by
  simp [emitEvent, Contract.runState]

/-- Event log append view of emitEvent. -/
@[simp] theorem emitEvent_events_append (name : String) (args indexedArgs : List Uint256)
    (state : ContractState) :
    ((emitEvent name args indexedArgs).run state).snd.events =
      state.events ++ [{ name := name, args := args, indexedArgs := indexedArgs }] := by
  simp

/-- Sequential event emission appends in order. -/
theorem emitEvent_emitEvent_events (name1 : String) (args1 indexedArgs1 : List Uint256)
    (name2 : String) (args2 indexedArgs2 : List Uint256) (state : ContractState) :
    ((Verity.bind (emitEvent name1 args1 indexedArgs1)
        (fun _ => emitEvent name2 args2 indexedArgs2)).run state).snd.events =
      state.events ++
        [{ name := name1, args := args1, indexedArgs := indexedArgs1 },
         { name := name2, args := args2, indexedArgs := indexedArgs2 }] := by
  simp [Contract.run, Verity.bind, emitEvent, List.append_assoc]

/-!
## MAX_UINT256 / modulus Helper Lemmas

Convenience lemmas that eliminate the repeated inline derivation of
`MAX_UINT256 < modulus` and `n ≤ MAX_UINT256 → n < modulus`.
-/

/-- modulus = MAX_UINT256 + 1. Useful for omega-based proofs. -/
theorem modulus_eq_max_uint256_succ :
    Verity.Core.Uint256.modulus = Verity.Stdlib.Math.MAX_UINT256 + 1 :=
  Verity.Core.Uint256.max_uint256_succ_eq_modulus.symm

/-- MAX_UINT256 is strictly less than modulus (= 2^256). -/
theorem max_uint256_lt_modulus :
    Verity.Stdlib.Math.MAX_UINT256 < Verity.Core.Uint256.modulus := by
  rw [modulus_eq_max_uint256_succ]; exact Nat.lt_succ_of_le (Nat.le_refl _)

/-- Any value ≤ MAX_UINT256 is strictly less than modulus. -/
theorem lt_modulus_of_le_max_uint256 (n : Nat)
    (h : n ≤ Verity.Stdlib.Math.MAX_UINT256) :
    n < Verity.Core.Uint256.modulus :=
  Nat.lt_of_le_of_lt h max_uint256_lt_modulus

/-- Convert `a ≥ b` on Uint256 to `b.val ≤ a.val` on Nat.
    Eliminates the repeated 3-4 line pattern found in transfer proofs:
    `have h' : b.val ≤ a.val := by have h'' : b ≤ a := ...; simpa [Uint256.le_def] using h''` -/
theorem uint256_ge_val_le {a b : Verity.Core.Uint256} (h : a ≥ b) : b.val ≤ a.val := by
  simpa [Verity.Core.Uint256.le_def] using h

/-- `amount < modulus` when `bal.val ≥ amount` (amount fits in a Uint256 because balance does).
    Eliminates the repeated 3-line pattern:
    `have hlt := bal.isLt; exact Nat.lt_of_le_of_lt h hlt` -/
theorem amount_lt_modulus_of_val_ge (bal : Verity.Core.Uint256) (amount : Nat)
    (h : bal.val ≥ amount) : amount < Verity.Core.Uint256.modulus :=
  Nat.lt_of_le_of_lt h bal.isLt

/-- `bal ≥ ofNat amount` when `bal.val ≥ amount` (lift Nat comparison to Uint256).
    Eliminates the repeated 3-line `simp [le_def, val_ofNat, mod_eq_of_lt ...]` block. -/
theorem uint256_ofNat_le_of_val_ge (bal : Verity.Core.Uint256) (amount : Nat)
    (h : bal.val ≥ amount) : bal ≥ Verity.Core.Uint256.ofNat amount := by
  have h_lt := amount_lt_modulus_of_val_ge bal amount h
  simp [Verity.Core.Uint256.le_def, Verity.Core.Uint256.val_ofNat,
    Nat.mod_eq_of_lt h_lt, h]

/-- If `require (a == b) msg` succeeds, then `a = b`.
    Composes `require_success_implies_cond` with `address_beq_eq_true_iff_eq`. -/
theorem require_beq_success_implies_eq (a b : Address) (msg : String)
    (s : ContractState)
    (h : ((Verity.require (a == b) msg).run s).isSuccess = true) :
    a = b :=
  (address_beq_eq_true_iff_eq a b).1 (require_success_implies_cond (cond := a == b) (msg := msg) (state := s) h)

/-- `require (a == b) msg` succeeds exactly when `a = b`. -/
theorem require_beq_isSuccess_true_iff_eq (a b : Address) (msg : String) (s : ContractState) :
    ((Verity.require (a == b) msg).run s).isSuccess = true ↔ a = b := by
  constructor
  · intro h
    exact require_beq_success_implies_eq a b msg s h
  · intro h_eq
    subst h_eq
    simp

/-- `require (a == b) msg` fails exactly when `a ≠ b`. -/
theorem require_beq_isSuccess_false_iff_ne (a b : Address) (msg : String) (s : ContractState) :
    ((Verity.require (a == b) msg).run s).isSuccess = false ↔ a ≠ b := by
  constructor
  · intro h_false h_eq
    subst h_eq
    simp at h_false
  · intro h_ne
    have h_beq_false : (a == b) = false := address_beq_false_of_ne a b h_ne
    simp [h_beq_false]

/-- Common owner-check pattern:
    if `msgSender >>= getStorageAddr slot >>= require (sender == owner)` succeeds,
    then the storage owner at `slot` equals the caller (`state.sender`). -/
theorem owner_guard_success_implies_storageAddr_eq_sender
    (slot : StorageSlot Address) (msg : String) (state : ContractState)
    (h :
      ((Verity.bind msgSender (fun sender =>
          Verity.bind (getStorageAddr slot) (fun ownerAddr =>
            Verity.require (sender == ownerAddr) msg))).run state).isSuccess = true) :
    state.storageAddr slot.slot = state.sender := by
  have h_req :
      ((Verity.require (state.sender == state.storageAddr slot.slot) msg).run state).isSuccess = true := by
    simpa [msgSender, getStorageAddr, Verity.bind, Contract.run, ContractState.readAddrSlot] using h
  exact (require_beq_isSuccess_true_iff_eq state.sender (state.storageAddr slot.slot) msg state).1 h_req |>.symm

/-!
## View-Frame Algebraic Preservation & Automation (#2422, #1994, #1895)

Compositional `.snd`-state preservation and `viewPreservesState` lemmas that
discharge storage/context preservation across `require`, `let` bindings, and
conditional branches without manual case-splitting on revert paths.
-/

@[simp]
theorem pure_run_snd {α : Type} (a : α) (s : ContractState) :
    ((Verity.pure a).run s).snd = s :=
  rfl

@[simp]
theorem require_run_snd (cond : Bool) (msg : String) (s : ContractState) :
    ((Verity.require cond msg).run s).snd = s := by
  cases cond <;> rfl

@[simp]
theorem getStorage_run_snd (slot : StorageSlot Uint256) (s : ContractState) :
    ((getStorage slot).run s).snd = s :=
  rfl

@[simp]
theorem getStorageAddr_run_snd (slot : StorageSlot Address) (s : ContractState) :
    ((getStorageAddr slot).run s).snd = s :=
  rfl

@[simp]
theorem getMapping_run_snd (slot : StorageSlot (Address → Uint256)) (key : Address)
    (s : ContractState) :
    ((getMapping slot key).run s).snd = s :=
  rfl

@[simp]
theorem getMappingUint_run_snd (slot : StorageSlot (Uint256 → Uint256)) (key : Uint256)
    (s : ContractState) :
    ((getMappingUint slot key).run s).snd = s :=
  rfl

@[simp]
theorem getMapping2_run_snd (slot : StorageSlot (Address → Address → Uint256))
    (k1 k2 : Address) (s : ContractState) :
    ((getMapping2 slot k1 k2).run s).snd = s :=
  rfl

@[simp]
theorem msgSender_run_snd (s : ContractState) :
    (msgSender.run s).snd = s :=
  rfl

/-- Algebraic monadic state preservation: if `m` preserves `s` on both success
and revert paths (`(m.run s).snd = s`), and every continuation `k a` preserves
`s`, then `Verity.bind m k` preserves `s` (`#2422`). -/
theorem bind_run_snd_of_preserve {α β : Type}
    (m : Contract α) (k : α → Contract β) (s : ContractState)
    (hm : (m.run s).snd = s)
    (hk : ∀ a, ((k a).run s).snd = s) :
    ((Verity.bind m k).run s).snd = s := by
  cases h : m s with
  | success a s' =>
      have hs' : s' = s := by simpa [Contract.run, h, ContractResult.snd] using hm
      subst hs'
      simpa [Verity.bind, Contract.run, h] using hk a
  | revert msg s' =>
      simp [Verity.bind, Contract.run, h, ContractResult.snd]

@[simp]
theorem bind_require_run_snd {α : Type}
    (cond : Bool) (msg : String) (k : Unit → Contract α) (s : ContractState) :
    ((Verity.bind (Verity.require cond msg) k).run s).snd =
      if cond then ((k ()).run s).snd else s := by
  cases cond <;> rfl

theorem ite_run_snd_of_preserve {α : Type}
    (c : Prop) [Decidable c] (t e : Contract α) (s : ContractState)
    (ht : (t.run s).snd = s) (he : (e.run s).snd = s) :
    ((if c then t else e).run s).snd = s := by
  split <;> assumption

/-- Lift `(m.run s).snd = s` directly to `Verity.Specs.viewPreservesState s (m.run s).snd` (`#2422`). -/
theorem viewPreservesState_of_run_snd_eq {α : Type}
    (m : Contract α) (s : ContractState)
    (h : (m.run s).snd = s) :
    Verity.Specs.viewPreservesState s (m.run s).snd := by
  rw [h]
  exact Verity.Specs.viewPreservesState_rfl s

/-- Compositional `viewPreservesState` across `Verity.bind` when both stages
preserve the pre-state `s` (`#2422`). -/
theorem viewPreservesState_bind_of_preserve {α β : Type}
    (m : Contract α) (k : α → Contract β) (s : ContractState)
    (hm : (m.run s).snd = s)
    (hk : ∀ a, ((k a).run s).snd = s) :
    Verity.Specs.viewPreservesState s ((Verity.bind m k).run s).snd :=
  viewPreservesState_of_run_snd_eq (Verity.bind m k) s
    (bind_run_snd_of_preserve m k s hm hk)

@[simp]
theorem viewPreservesState_require (cond : Bool) (msg : String) (s : ContractState) :
    Verity.Specs.viewPreservesState s ((Verity.require cond msg).run s).snd :=
  viewPreservesState_of_run_snd_eq (Verity.require cond msg) s (require_run_snd cond msg s)

/-- `require` followed by any view-preserving continuation `k` preserves state on both
the success and revert branches without manual `by_cases` (`#2422`, `#1994`, `#1895`). -/
theorem viewPreservesState_bind_require {α : Type}
    (cond : Bool) (msg : String) (k : Unit → Contract α) (s : ContractState)
    (hk : Verity.Specs.viewPreservesState s ((k ()).run s).snd) :
    Verity.Specs.viewPreservesState s
      ((Verity.bind (Verity.require cond msg) k).run s).snd := by
  cases cond
  · exact Verity.Specs.viewPreservesState_rfl s
  · exact hk

theorem sameStorage_of_viewPreservesState {s s' : ContractState}
    (h : Verity.Specs.viewPreservesState s s') :
    Verity.Specs.sameStorage s s' :=
  h.1.1

theorem sameStorageAddr_of_viewPreservesState {s s' : ContractState}
    (h : Verity.Specs.viewPreservesState s s') :
    Verity.Specs.sameStorageAddr s s' :=
  h.1.2.1

theorem sameStorageMap_of_viewPreservesState {s s' : ContractState}
    (h : Verity.Specs.viewPreservesState s s') :
    Verity.Specs.sameStorageMap s s' :=
  h.1.2.2.1

theorem sameContext_of_viewPreservesState {s s' : ContractState}
    (h : Verity.Specs.viewPreservesState s s') :
    Verity.Specs.sameContext s s' :=
  h.2.1

/-!
## Wave 3 Monadic Step & Frame Automation (`verity_step` / `verity_frame`)

Compositional monadic step and revert characterization lemmas plus tactic macros
for stepping through `Contract.run` / `Verity.bind` / `require` computations and
discharging storage-frame / context equality obligations.
-/

/-- `Verity.pure` immediately succeeds without modifying contract state. -/
@[simp]
theorem Contract.run_pure_eq {α : Type} (x : α) (s : ContractState) :
    (Verity.pure x).run s = ContractResult.success x s :=
  rfl

/-- Compositional `Verity.bind` step when the prefix computation succeeds on `s`. -/
@[simp]
theorem Contract.run_bind_success {α β : Type} (m : Contract α) (f : α → Contract β)
    (s : ContractState) (a : α)
    (h : m.run s = ContractResult.success a s) :
    (Verity.bind m f).run s = (f a).run s :=
  Verity.bind_run_success m f s a h

/-- Compositional `Verity.bind` step when the prefix computation succeeds with state `s₁`
    and the continuation succeeds on `s₁`. -/
theorem Contract.run_bind_success_of_isSuccess {α β : Type} (m : Contract α) (f : α → Contract β)
    (s s₁ : ContractState) (a : α)
    (hm : m.run s = ContractResult.success a s₁)
    (hf : ((f a).run s₁).isSuccess = true) :
    (Verity.bind m f).run s = (f a).run s₁ := by
  have hm_eq : m s = ContractResult.success a s₁ := Contract.eq_of_run_success hm
  unfold Contract.run at hf ⊢
  cases hfa : f a s₁ with
  | success b s₂ =>
      simp [Verity.bind, hm_eq, hfa]
  | revert msg s₂ =>
      simp [hfa, ContractResult.isSuccess] at hf

/-- Compositional `Verity.bind` step chaining two successful `Contract.run` evaluations. -/
theorem Contract.run_bind_success_chain {α β : Type} (m : Contract α) (f : α → Contract β)
    (s s₁ s₂ : ContractState) (a : α) (b : β)
    (hm : m.run s = ContractResult.success a s₁)
    (hf : (f a).run s₁ = ContractResult.success b s₂) :
    (Verity.bind m f).run s = ContractResult.success b s₂ := by
  have hm_eq : m s = ContractResult.success a s₁ := Contract.eq_of_run_success hm
  have hf_eq : f a s₁ = ContractResult.success b s₂ := Contract.eq_of_run_success hf
  simp [Verity.bind, Contract.run, hm_eq, hf_eq]

/-- Compositional `Verity.bind` short-circuit lemma when the prefix computation reverts. -/
@[simp]
theorem Contract.run_bind_revert {α β : Type} (m : Contract α) (f : α → Contract β)
    (s s₁ : ContractState) (msg : String)
    (h : m.run s = ContractResult.revert msg s₁) :
    (Verity.bind m f).run s = ContractResult.revert msg s₁ := by
  unfold Contract.run at h
  cases hm : m s with
  | success a s' =>
      simp [hm] at h
  | revert msg' s' =>
      simp [hm] at h
      rcases h with ⟨hmsg, hs⟩
      subst hmsg
      subst hs
      simp [Verity.bind, Contract.run, hm]

/-- `require` with a satisfied guard steps directly to its continuation under `Contract.run`. -/
@[simp]
theorem Contract.run_require_true_bind {α : Type} (cond : Bool) (msg : String)
    (k : Unit → Contract α) (s : ContractState)
    (h : cond = true) :
    (Verity.bind (require cond msg) k).run s = (k ()).run s := by
  subst h
  rfl

/-- `require` with a violated guard short-circuits `Verity.bind` to `ContractResult.revert`. -/
@[simp]
theorem Contract.run_require_false_bind {α : Type} (cond : Bool) (msg : String)
    (k : Unit → Contract α) (s : ContractState)
    (h : cond = false) :
    (Verity.bind (require cond msg) k).run s = ContractResult.revert msg s := by
  subst h
  rfl

/-- Any computation whose `Contract.run` produces `ContractResult.success` has `isSuccess = true`. -/
@[simp]
theorem Contract.isSuccess_of_run_success {α : Type} {m : Contract α}
    {s s' : ContractState} {v : α}
    (h : m.run s = ContractResult.success v s') :
    (m.run s).isSuccess = true := by
  rw [h]
  rfl

/-- Any computation whose `Contract.run` produces `ContractResult.revert` has `isSuccess = false`. -/
@[simp]
theorem Contract.isSuccess_of_run_revert {α : Type} {m : Contract α}
    {s s' : ContractState} {msg : String}
    (h : m.run s = ContractResult.revert msg s') :
    (m.run s).isSuccess = false := by
  rw [h]
  rfl

/-!
## Primitive `Contract.run` Reduction & Conditional Lemmas (`verity_prove_spec`)

Direct `@[simp]` reduction lemmas for primitive storage, context, and conditional
`Contract.run` evaluations, paired with the `verity_prove_spec` tactic macro.
-/

/-- `getStorage` reads the `Uint256` word at `slot.slot` without modifying state. -/
@[simp]
theorem Contract.run_getStorage_eq (slot : StorageSlot Uint256) (s : ContractState) :
    (getStorage slot).run s = ContractResult.success (s.storage slot.slot) s :=
  rfl

/-- `setStorage` writes `val` to `slot.slot` via `ContractState.writeSlot`. -/
@[simp]
theorem Contract.run_setStorage_eq (slot : StorageSlot Uint256) (val : Uint256)
    (s : ContractState) :
    (setStorage slot val).run s = ContractResult.success () (s.writeSlot slot.slot val) :=
  rfl

/-- `getStorageAddr` reads the `Address` at `slot.slot` without modifying state. -/
@[simp]
theorem Contract.run_getStorageAddr_eq (slot : StorageSlot Address) (s : ContractState) :
    (getStorageAddr slot).run s = ContractResult.success (s.storageAddr slot.slot) s :=
  rfl

/-- `setStorageAddr` writes `val` to `slot.slot` via `ContractState.writeAddrSlot`. -/
@[simp]
theorem Contract.run_setStorageAddr_eq (slot : StorageSlot Address) (val : Address)
    (s : ContractState) :
    (setStorageAddr slot val).run s = ContractResult.success () (s.writeAddrSlot slot.slot val) :=
  rfl

/-- `getMapping` reads the `Uint256` entry at `(slot.slot, k)` without modifying state. -/
@[simp]
theorem Contract.run_getMapping_eq (slot : StorageSlot (Address → Uint256))
    (k : Address) (s : ContractState) :
    (getMapping slot k).run s = ContractResult.success (s.storageMap slot.slot k) s :=
  rfl

/-- `setMapping` writes `val` at `(slot.slot, k)` via `ContractState.writeMap` and records `k` in `knownAddresses`. -/
@[simp]
theorem Contract.run_setMapping_eq (slot : StorageSlot (Address → Uint256))
    (k : Address) (val : Uint256) (s : ContractState) :
    (setMapping slot k val).run s =
      ContractResult.success () { s.writeMap slot.slot k val with
        knownAddresses := fun slotIdx =>
          if slotIdx == slot.slot then
            (s.knownAddresses slotIdx).insert k
          else
            s.knownAddresses slotIdx
      } :=
  rfl

/-- `msgSender` returns `s.sender` without modifying state. -/
@[simp]
theorem Contract.run_msgSender_eq (s : ContractState) :
    msgSender.run s = ContractResult.success s.sender s :=
  rfl

/-- Conditional `Contract.run` steps to the `then` branch when `c` holds. -/
@[simp]
theorem Contract.run_ite_true {α : Type} {c : Prop} [Decidable c]
    (t e : Contract α) (s : ContractState) (hc : c) :
    (if c then t else e).run s = t.run s := by
  rw [if_pos hc]

/-- Conditional `Contract.run` steps to the `else` branch when `¬c` holds. -/
@[simp]
theorem Contract.run_ite_false {α : Type} {c : Prop} [Decidable c]
    (t e : Contract α) (s : ContractState) (hc : ¬c) :
    (if c then t else e).run s = e.run s := by
  rw [if_neg hc]

/-- Simplify one monadic `Contract.run` / `Verity.bind` / `require` step. -/
syntax (name := verity_step)
  "verity_step" : tactic

/-- Discharge storage frame / context equality goals via reflexivity, decidability, or `storage_simps`. -/
syntax (name := verity_frame_goal)
  "verity_frame" : tactic

/-- Chain `verity_step` and `verity_frame` to discharge straight-line contract function
    specifications without `simp_all`. -/
syntax (name := verity_prove_spec)
  "verity_prove_spec" : tactic

/-- Unfold one or more definitions/specs and discharge via `verity_prove_spec`. -/
syntax (name := verity_prove_spec_with)
  "verity_prove_spec " simpLemma,+ : tactic

macro_rules
  | `(tactic| verity_step) =>
      `(tactic|
        ((try simp only [
            Contract.run_pure_eq,
            Contract.run_bind_success,
            Contract.run_bind_revert,
            Contract.run_require_true_bind,
            Contract.run_require_false_bind,
            Contract.run_getStorage_eq,
            Contract.run_setStorage_eq,
            Contract.run_getStorageAddr_eq,
            Contract.run_setStorageAddr_eq,
            Contract.run_getMapping_eq,
            Contract.run_setMapping_eq,
            Contract.run_msgSender_eq,
            Contract.run_ite_true,
            Contract.run_ite_false
          ])
         (try simp only [
            Contract.run_pure_eq,
            Contract.run_bind_success,
            Contract.run_bind_revert,
            Contract.run_require_true_bind,
            Contract.run_require_false_bind,
            Contract.run_getStorage_eq,
            Contract.run_setStorage_eq,
            Contract.run_getStorageAddr_eq,
            Contract.run_setStorageAddr_eq,
            Contract.run_getMapping_eq,
            Contract.run_setMapping_eq,
            Contract.run_msgSender_eq,
            Contract.run_ite_true,
            Contract.run_ite_false,
            getStorage,
            setStorage,
            getStorageAddr,
            setStorageAddr,
            getMapping,
            setMapping,
            msgSender,
            ContractState.readSlot,
            ContractState.readAddrSlot,
            ContractState.readMap,
            Verity.require,
            Verity.bind,
            Verity.pure,
            Bind.bind,
            Pure.pure,
            Contract.run,
            ContractResult.snd,
            ContractResult.fst,
            ContractResult.isSuccess,
            ContractResult.getState,
            ite_true,
            ite_false
          ])))
  | `(tactic| verity_frame) =>
      `(tactic|
        first
          | rfl
          | decide
          | simp only [
              storage_simps,
              ContractState.storage_writeSlot_same,
              ContractState.storage_writeSlot_other,
              ContractState.storageAddr_writeSlot,
              ContractState.storageMap_writeSlot,
              ContractState.storageMapUint_writeSlot,
              ContractState.storageMap2_writeSlot,
              ContractState.storageAddr_writeAddrSlot_same,
              ContractState.storageAddr_writeAddrSlot_other,
              ContractState.storage_writeAddrSlot,
              ContractState.storageMap_writeAddrSlot,
              ContractState.storageMapUint_writeAddrSlot,
              ContractState.storageMap2_writeAddrSlot,
              ContractState.storageMap_writeMap_same,
              ContractState.storageMap_writeMap_other_key,
              ContractState.storage_writeMap,
              ContractState.storageAddr_writeMap,
              ContractState.storageMapUint_writeMap,
              ContractState.storageMap2_writeMap,
              ContractState.sender_writeSlot,
              ContractState.thisAddress_writeSlot,
              ContractState.msgValue_writeSlot,
              ContractState.selfBalance_writeSlot,
              ContractState.blockTimestamp_writeSlot,
              ContractState.blockNumber_writeSlot,
              ContractState.chainId_writeSlot,
              ContractState.blobBaseFee_writeSlot,
              ContractState.calldataSize_writeSlot,
              ContractState.events_writeSlot,
              ContractState.knownAddresses_writeSlot,
              ContractState.sender_writeAddrSlot,
              ContractState.thisAddress_writeAddrSlot,
              ContractState.storageArray_writeAddrSlot,
              ContractState.msgValue_writeAddrSlot,
              ContractState.selfBalance_writeAddrSlot,
              ContractState.blockTimestamp_writeAddrSlot,
              ContractState.blockNumber_writeAddrSlot,
              ContractState.chainId_writeAddrSlot,
              ContractState.blobBaseFee_writeAddrSlot,
              ContractState.calldataSize_writeAddrSlot,
              ContractState.sender_writeMap,
              ContractState.thisAddress_writeMap,
              ContractState.msgValue_writeMap,
              ContractState.selfBalance_writeMap,
              ContractState.blockTimestamp_writeMap,
              ContractState.blockNumber_writeMap,
              ContractState.chainId_writeMap,
              ContractState.blobBaseFee_writeMap,
              ContractState.calldataSize_writeMap,
              ContractState.events_writeMap,
              ContractState.knownAddresses_writeMap,
              Verity.Specs.unchangedExcept_rfl,
              Verity.Specs.unchangedExcept_with_events,
              Verity.Specs.unchangedExcept_with_knownAddresses,
              Verity.Specs.unchangedExcept_writeSlot_of_mem,
              Verity.Specs.unchangedExcept_writeAddrSlot_of_mem,
              Verity.Specs.unchangedExcept_writeMap_of_mem,
              Verity.Specs.unchangedExcept_writeMapUint_of_mem,
              Verity.Specs.unchangedExcept_writeMap2_of_mem,
              Verity.Specs.unchangedExcept_writeArray_of_mem,
              Verity.Specs.sameContext_rfl,
              Verity.Specs.sameStorage_rfl,
              Verity.Specs.sameStorageAddr_rfl,
              Verity.Specs.sameStorageMap_rfl,
              Verity.Specs.sameAddrMapContext_rfl,
              Verity.Specs.sameStorageMapContext_rfl,
              Verity.Specs.viewPreservesState_rfl,
              List.mem_cons,
              List.mem_singleton,
              List.not_mem_nil,
              or_true,
              true_or,
              and_self,
              true_and,
              and_true
            ])
  | `(tactic| verity_prove_spec) =>
      `(tactic|
        (try intros
         try simp only [Verity.Specs.FnSpec.Satisfies, Verity.Specs.fnUpdateSpec]
         verity_step
         try verity_frame))
  | `(tactic| verity_prove_spec $lems,*) =>
      `(tactic|
        (try intros
         simp only [$lems,*, Verity.Specs.FnSpec.Satisfies, Verity.Specs.fnUpdateSpec]
         verity_step
         try verity_frame))

example (msg : String) (x : Uint256) (s : ContractState) :
    (Verity.bind (require true msg) (fun _ => Verity.pure x)).run s =
      ContractResult.success x s := by
  verity_step

example (s : ContractState) (slot : Nat) (v : Uint256) :
    (s.writeSlot slot v).readSlot slot = v := by
  verity_frame

example (slot : StorageSlot Uint256) (val : Uint256) (s : ContractState) :
    (Verity.bind (setStorage slot val) (fun _ => getStorage slot)).run s =
      ContractResult.success val (s.writeSlot slot.slot val) := by
  verity_prove_spec

example (slot : StorageSlot Uint256) (val : Uint256) (s : ContractState) :
    Verity.Specs.FnSpec.Satisfies (setStorage slot val) s
      { pre := True
        post := fun _ s' => s'.storage slot.slot = val
        writes := [.slot slot.slot] } := by
  verity_prove_spec

-- All lemmas in this file are fully proven with zero sorry, zero axioms.

end Verity.Proofs.Stdlib.Automation
