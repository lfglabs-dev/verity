import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness.Preservation

import Lean

namespace Compiler.Proofs.YulGeneration.Backends.Native

open Compiler.Yul

open Compiler.Proofs.YulGeneration

open Compiler.Proofs.YulGeneration.Backends.StateBridge

open Lean Elab Tactic Meta

open Compiler.Proofs.IRGeneration

  (IRResult IRState IRStorageSlot IRStorageWord IRTransaction)

/-- Project the account storage for the current contract back to Verity's
    `IRStorageSlot → IRStorageWord` storage view. -/
def projectStorageFromState (tx : YulTransaction) (state : EvmYul.Yul.State) :
    IRStorageSlot → IRStorageWord :=
  extractStorage state.sharedState (natToAddress tx.thisAddress)

/-- Lean 4.31 exposes TreeMap insertion lookup through `getElem?`, rather
than the removed `get?_insert_of_eq` compatibility lemma. -/
private theorem treeMap_get?_insert_self
    {α β : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : Std.TreeMap α β cmp) (key : α) (value : β) :
    (m.insert key value).get? key = some value := by
  rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert_self]

private theorem treeMap_getD_of_get?
    {α β : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : Std.TreeMap α β cmp) (key : α) (value fallback : β)
    (h : m.get? key = some value) : m.getD key fallback = value := by
  rw [Std.TreeMap.getD_eq_getD_getElem?, ← Std.TreeMap.get?_eq_getElem?, h]
  rfl

private theorem treeMap_getD_of_get?_none
    {α β : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : Std.TreeMap α β cmp) (key : α) (fallback : β)
    (h : m.get? key = none) : m.getD key fallback = fallback := by
  rw [Std.TreeMap.getD_eq_getD_getElem?, ← Std.TreeMap.get?_eq_getElem?, h]
  rfl

/-- Transport an absent `get?` lookup to Lean 4.31's `getElem?` syntax. -/
private theorem treeMap_getElem?_none_of_get?
    {α β : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : Std.TreeMap α β cmp) (key : α)
    (h : m.get? key = none) : m[key]? = none := by
  rw [← Std.TreeMap.get?_eq_getElem?]
  exact h

/-- A nonzero `SSTORE` inserts its value at the written key.  The remaining
branches in `State.sstore` compute gas and refunds only. -/
private theorem account_updateStorage_get?_self_of_nonzero
    {τ : EvmYul.OperationType} (account : EvmYul.Account τ)
    (slot value : EvmYul.UInt256)
    (hValueNonzero : (value == (⟨0⟩ : EvmYul.UInt256)) = false) :
    (account.updateStorage slot value).storage.get? slot = some value := by
  unfold EvmYul.Account.updateStorage
  change (value == EvmYul.UInt256.ofNat 0) = false at hValueNonzero
  split
  · next hZero =>
    change (value == EvmYul.UInt256.ofNat 0) = true at hZero
    rw [hValueNonzero] at hZero
    contradiction
  · simp [treeMap_get?_insert_self]

private theorem account_updateStorage_storage_of_nonzero
    {τ : EvmYul.OperationType} (account : EvmYul.Account τ)
    (slot value : EvmYul.UInt256)
    (hValueNonzero : (value == (⟨0⟩ : EvmYul.UInt256)) = false) :
    (account.updateStorage slot value).storage = account.storage.insert slot value := by
  unfold EvmYul.Account.updateStorage
  change (value == EvmYul.UInt256.ofNat 0) = false at hValueNonzero
  split
  · next hZero =>
    change (value == EvmYul.UInt256.ofNat 0) = true at hZero
    rw [hValueNonzero] at hZero
    contradiction
  · rfl

private theorem account_updateStorage_storage_of_zero
    {τ : EvmYul.OperationType} (account : EvmYul.Account τ)
    (slot value : EvmYul.UInt256)
    (hValueZero : (value == (⟨0⟩ : EvmYul.UInt256)) = true) :
    (account.updateStorage slot value).storage = account.storage.erase slot := by
  unfold EvmYul.Account.updateStorage
  change (value == EvmYul.UInt256.ofNat 0) = true at hValueZero
  split
  · rfl
  · next hNonzero =>
    simp only [Bool.not_eq_true] at hNonzero
    change (value == EvmYul.UInt256.ofNat 0) = false at hNonzero
    rw [hValueZero] at hNonzero
    contradiction

/-- A zero `SSTORE` erases its written key. -/
private theorem account_updateStorage_get?_self_of_zero
    {τ : EvmYul.OperationType} (account : EvmYul.Account τ)
    (slot value : EvmYul.UInt256)
    (hValueZero : (value == (⟨0⟩ : EvmYul.UInt256)) = true) :
    (account.updateStorage slot value).storage.get? slot = none := by
  unfold EvmYul.Account.updateStorage
  change (value == EvmYul.UInt256.ofNat 0) = true at hValueZero
  split
  · simp [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_erase]
  · next hNonzero =>
    simp only [Bool.not_eq_true] at hNonzero
    change (value == EvmYul.UInt256.ofNat 0) = false at hNonzero
    rw [hValueZero] at hNonzero
    contradiction

/-- Machine-state updates do not affect the account storage projection. -/
private theorem projectStorageFromState_setMachineState
    (tx : YulTransaction) (state : EvmYul.Yul.State) (machine : EvmYul.MachineState) :
    projectStorageFromState tx (state.setMachineState machine) =
      projectStorageFromState tx state := by
  cases state <;> rfl

private theorem projectStorageFromState_withMachineState
    (tx : YulTransaction) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (machine : EvmYul.MachineState) :
    projectStorageFromState tx (.Ok { shared with toMachineState := machine } store) =
      projectStorageFromState tx (.Ok shared store) := by
  rfl

/-- Projecting final native storage reads the current contract account storage
    entry for the requested slot. -/
@[simp] theorem projectStorageFromState_accountStorageSlot
    (tx : YulTransaction)
    (state : EvmYul.Yul.State)
    (slot : Nat)
    (account : EvmYul.Account .Yul)
    (value : EvmYul.UInt256)
    (hAccount :
      state.sharedState.accountMap.get? (natToAddress tx.thisAddress) =
        some account)
    (hSlot : account.storage.get? (natToUInt256 slot) = some value) :
    projectStorageFromState tx state (IRStorageSlot.ofNat slot) = value := by
  have hAccount' :
      state.sharedState.accountMap[natToAddress tx.thisAddress]? = some account := by
    rw [← Std.TreeMap.get?_eq_getElem?]
    exact hAccount
  have hSlot' : account.storage[natToUInt256 slot]? = some value := by
    rw [← Std.TreeMap.get?_eq_getElem?]
    exact hSlot
  simp [projectStorageFromState, extractStorage, hAccount', hSlot']

/-- Projecting final native storage defaults to zero when the current contract
    account has no native storage entry for the requested slot. -/
@[simp] theorem projectStorageFromState_missingAccountStorageSlot
    (tx : YulTransaction)
    (state : EvmYul.Yul.State)
    (slot : Nat)
    (account : EvmYul.Account .Yul)
    (hAccount :
      state.sharedState.accountMap.get? (natToAddress tx.thisAddress) =
        some account)
    (hSlot : account.storage.get? (natToUInt256 slot) = none) :
    projectStorageFromState tx state (IRStorageSlot.ofNat slot) = 0 := by
  have hAccount' :
      state.sharedState.accountMap[natToAddress tx.thisAddress]? = some account := by
    rw [← Std.TreeMap.get?_eq_getElem?]
    exact hAccount
  have hSlot' : account.storage[natToUInt256 slot]? = none := by
    rw [← Std.TreeMap.get?_eq_getElem?]
    exact hSlot
  simp [projectStorageFromState, extractStorage, hAccount', hSlot']

/-- Projecting final native storage defaults to zero when the current contract
    account is absent from the native account map. -/
@[simp] theorem projectStorageFromState_missingAccount
    (tx : YulTransaction)
    (state : EvmYul.Yul.State)
    (slot : Nat)
    (hAccount :
      state.sharedState.accountMap.get? (natToAddress tx.thisAddress) =
        none) :
    projectStorageFromState tx state (IRStorageSlot.ofNat slot) = 0 := by
  have hAccount' :
      state.sharedState.accountMap[natToAddress tx.thisAddress]? = none := by
    rw [← Std.TreeMap.get?_eq_getElem?]
    exact hAccount
  simp [projectStorageFromState, extractStorage, hAccount']

/-- Native initial-state storage materialization agrees with Verity storage on
    every explicit observable slot. Slots and values are interpreted in the
    EVM word domain, so the result is modulo `UInt256.size`. -/
theorem initialState_observableStorageSlot
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot : Nat)
    (hSlot : slot ∈ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    projectStorageFromState tx
      (initialState contract tx storage observableSlots) (IRStorageSlot.ofNat slot) =
      storage (IRStorageSlot.ofNat slot) := by
  simp only [projectStorageFromState, extractStorage, initialState,
    EvmYul.Yul.State.sharedState, YulState.initial, toSharedState]
  rw [treeMap_get?_insert_self]
  rw [treeMap_get?_insert_self]
  have h := storageLookup_projectStorage storage observableSlots slot hSlot hRange
  unfold storageLookup at h
  exact h

/-- Native initial-state storage materialization agrees with Verity storage on
    every explicitly materialized slot. This is the range-free form used by the
    generated native dispatcher path, whose materialization list is already in
    bounded `IRStorageSlot` space. -/
theorem initialState_materializedStorageSlot
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat)
    (slot : Nat)
    (hSlot : slot ∈ slots) :
    projectStorageFromState tx
      (initialState contract tx storage slots) (IRStorageSlot.ofNat slot) =
      storage (IRStorageSlot.ofNat slot) := by
  simp only [projectStorageFromState, extractStorage, initialState,
    EvmYul.Yul.State.sharedState, YulState.initial, toSharedState]
  rw [treeMap_get?_insert_self]
  rw [treeMap_get?_insert_self]
  have h := storageLookup_projectStorage_projected storage slots slot hSlot
  unfold storageLookup at h
  exact h

/-- The generated selector-hit marked-prefix state only changes native local
    variables. Projected contract storage still agrees with every materialized
    Verity storage slot. -/
theorem nativeSwitchStoreMarkedPrefixStateForId_materializedStorageSlot
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (slot : Nat)
    (hSlot : slot ∈ slots) :
    projectStorageFromState tx
      (nativeSwitchStoreMarkedPrefixStateForId contract tx storage slots
        switchId store)
      (IRStorageSlot.ofNat slot) =
      storage (IRStorageSlot.ofNat slot) := by
  simpa [nativeSwitchStoreMarkedPrefixStateForId,
    nativeSwitchStorePrefixStateForId, nativeSwitchStoreInitialState,
    EvmYul.Yul.State.insert, projectStorageFromState,
    EvmYul.Yul.State.sharedState, projectStorageFromState_setMachineState,
    projectStorageFromState_withMachineState] using
    (initialState_materializedStorageSlot contract tx storage slots slot hSlot)

theorem nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId_materializedStorageSlot
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (slot : Nat)
    (hSlot : slot ∈ slots) :
    projectStorageFromState tx
      (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
        storage slots switchId store)
      (IRStorageSlot.ofNat slot) =
      storage (IRStorageSlot.ofNat slot) := by
  simp only [nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
    nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
    nativeSwitchPostInitFreeMemoryState,
    nativeSwitchPostInitFreeMemorySharedState,
    EvmYul.Yul.State.insert]
  rw [projectStorageFromState_withMachineState]
  exact initialState_materializedStorageSlot contract tx storage slots slot hSlot

/-- Native `sload` from an initially materialized observable slot returns the
    exact EVM word projected from Verity storage. The range hypothesis keeps
    the slot key word-canonical, so the finite native storage map cannot alias
    another observed slot. -/
theorem initialState_sload_observableSlot_value
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot : Nat)
    (hSlot : slot ∈ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    (EvmYul.State.sload
      (initialState contract tx storage observableSlots).toState
      (natToUInt256 slot)).2 =
      storage (IRStorageSlot.ofNat slot) := by
  have hFindStorage :
      (projectStorage storage observableSlots).get? (natToUInt256 slot) =
        some (storage (IRStorageSlot.ofNat slot)) := by
    simpa [projectStorage, IRStorageWord.toUInt256] using
      foldl_insert_find storage observableSlots slot hSlot hRange
        (Std.TreeMap.empty : EvmYul.Storage)
  simp only [EvmYul.State.sload, EvmYul.State.lookupAccount,
    EvmYul.Yul.State.toState, initialState, toSharedState, YulState.initial]
  rw [treeMap_get?_insert_self]
  rw [treeMap_get?_insert_self]
  simp only [EvmYul.Account.lookupStorage]
  change (projectStorage storage observableSlots).getD (natToUInt256 slot) ⟨0⟩ =
    storage (IRStorageSlot.ofNat slot)
  exact treeMap_getD_of_get? _ _ _ _ hFindStorage

/-- Native `sload` from an initially materialized slot returns the exact bounded
    IR storage word. This is the range-free version used after IR storage keys
    moved to `IRStorageSlot`: Nat aliases modulo 2^256 carry the same bounded
    key and therefore the same projected value. -/
theorem initialState_sload_materializedSlot_value
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat)
    (slot : Nat)
    (hSlot : slot ∈ slots) :
    (EvmYul.State.sload
      (initialState contract tx storage slots).toState
      (natToUInt256 slot)).2 =
      storage (IRStorageSlot.ofNat slot) := by
  have hFindStorage :
      (projectStorage storage slots).get? (natToUInt256 slot) =
        some (storage (IRStorageSlot.ofNat slot)) := by
    simpa [projectStorage, IRStorageWord.toUInt256] using
      foldl_insert_find_projected storage slots slot hSlot
        (Std.TreeMap.empty : EvmYul.Storage)
  simp only [EvmYul.State.sload, EvmYul.State.lookupAccount,
    EvmYul.Yul.State.toState, initialState, toSharedState, YulState.initial]
  rw [treeMap_get?_insert_self]
  rw [treeMap_get?_insert_self]
  simp only [EvmYul.Account.lookupStorage]
  change (projectStorage storage slots).getD (natToUInt256 slot) ⟨0⟩ =
    storage (IRStorageSlot.ofNat slot)
  exact treeMap_getD_of_get? _ _ _ _ hFindStorage

/-- Projected storage is unchanged by the generated retrieve core
    `sload(0); mstore(0, _); return(0, 32)`. The only `sload` state effect is
    recording an accessed storage key, and `mstore`/`return` update only the
    machine-state fields used for returndata. -/
theorem projectStorageFromState_retrieveHit_initialState_materialized
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot : Nat)
    (hSlot : slot ∈ slots) :
    let shared := (initialState contract tx storage slots).sharedState
    let p := shared.sload (EvmYul.UInt256.ofNat 0)
    let shared1 : EvmYul.SharedState .Yul := { shared with toState := p.1 }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) p.2 }
    let shared3 : EvmYul.SharedState .Yul :=
      { shared2 with
        toMachineState :=
          shared2.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    projectStorageFromState tx (EvmYul.Yul.State.Ok shared3 store)
        (IRStorageSlot.ofNat slot) =
      storage (IRStorageSlot.ofNat slot) := by
  intro shared p shared1 shared2 shared3
  have hAccountMap :
      shared3.accountMap =
        (initialState contract tx storage slots).sharedState.accountMap := by
    simp [shared3, shared2, shared1, p, shared, EvmYul.State.sload,
      EvmYul.State.addAccessedStorageKey, EvmYul.Substate.addAccessedStorageKey]
  simp only [projectStorageFromState, extractStorage,
    EvmYul.Yul.State.sharedState, hAccountMap, initialState, YulState.initial,
    toSharedState]
  rw [treeMap_get?_insert_self]
  rw [treeMap_get?_insert_self]
  have h := storageLookup_projectStorage_projected storage slots slot hSlot
  unfold storageLookup at h
  exact h

/-- Native `sload` from an initially omitted materialized slot returns the EVM
    zero word. The range hypotheses rule out modular aliasing between the omitted
    slot and any materialized storage key. -/
theorem initialState_sload_omittedSlot_value
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot : Nat)
    (hNotSlot : slot ∉ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size)
    (hSlotRange : slot < EvmYul.UInt256.size) :
    (EvmYul.State.sload
      (initialState contract tx storage observableSlots).toState
      (natToUInt256 slot)).2 =
      natToUInt256 0 := by
  have hFindStorage :
      (projectStorage storage observableSlots).get? (natToUInt256 slot) = none := by
    simpa [projectStorage] using
      foldl_insert_find_not_mem storage observableSlots slot hNotSlot hRange
        hSlotRange (Std.TreeMap.empty : EvmYul.Storage)
  simp only [EvmYul.State.sload, EvmYul.State.lookupAccount,
    EvmYul.Yul.State.toState, initialState, toSharedState, YulState.initial]
  rw [treeMap_get?_insert_self]
  rw [treeMap_get?_insert_self]
  simp only [EvmYul.Account.lookupStorage]
  change (projectStorage storage observableSlots).getD (natToUInt256 slot) ⟨0⟩ =
    natToUInt256 0
  exact treeMap_getD_of_get?_none _ _ _ hFindStorage

/-- Native primitive execution of `sload(slot)` on an initially materialized,
    word-canonical observable slot returns exactly the projected storage word. -/
theorem primCall_sload_initialState_observableSlot_ok
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot : Nat)
    (hSlot : slot ∈ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    EvmYul.Yul.primCall (fuel + 1)
        (initialState contract tx storage observableSlots)
        EvmYul.Operation.SLOAD [natToUInt256 slot] =
      match EvmYul.State.sload
          (initialState contract tx storage observableSlots).toState
          (natToUInt256 slot) with
      | (state', _) =>
          .ok ((initialState contract tx storage observableSlots).setSharedState
              { (initialState contract tx storage observableSlots).toSharedState with
                toState := state' },
            [storage (IRStorageSlot.ofNat slot)]) := by
  rw [primCall_sload_ok]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 slot) = loaded
  cases loaded with
  | mk state' value =>
      have hvalue :=
        initialState_sload_observableSlot_value contract tx storage
          observableSlots slot hSlot hRange
      rw [hload] at hvalue
      simp only at hvalue
      simp [hvalue]

/-- Native primitive execution of `sload(slot)` on an initially omitted,
    word-canonical materialization slot returns the EVM zero word. -/
theorem primCall_sload_initialState_omittedSlot_ok
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot : Nat)
    (hNotSlot : slot ∉ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size)
    (hSlotRange : slot < EvmYul.UInt256.size) :
    EvmYul.Yul.primCall (fuel + 1)
        (initialState contract tx storage observableSlots)
        EvmYul.Operation.SLOAD [natToUInt256 slot] =
      match EvmYul.State.sload
          (initialState contract tx storage observableSlots).toState
          (natToUInt256 slot) with
      | (state', _) =>
          .ok ((initialState contract tx storage observableSlots).setSharedState
              { (initialState contract tx storage observableSlots).toSharedState with
                toState := state' },
            [natToUInt256 0]) := by
  rw [primCall_sload_ok]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 slot) = loaded
  cases loaded with
  | mk state' value =>
      have hvalue :=
        initialState_sload_omittedSlot_value contract tx storage
          observableSlots slot hNotSlot hRange hSlotRange
      rw [hload] at hvalue
      simp only at hvalue
      simp [hvalue]

/-- Native primitive execution of `sload(slot)` is independent of the current
    Yul local-variable store when reading an initially materialized,
    word-canonical observable slot. This is the selected-body shape left after
    the lowered dispatcher inserts switch temporaries. -/
theorem primCall_sload_initialState_observableSlot_ok_withStore
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot : Nat)
    (hSlot : slot ∈ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    EvmYul.Yul.primCall (fuel + 1)
        (.Ok (initialState contract tx storage observableSlots).sharedState store)
        EvmYul.Operation.SLOAD [natToUInt256 slot] =
      match EvmYul.State.sload
          (initialState contract tx storage observableSlots).toState
          (natToUInt256 slot) with
      | (state', _) =>
          .ok (((.Ok (initialState contract tx storage observableSlots).sharedState
                store : EvmYul.Yul.State).setSharedState
              { (.Ok (initialState contract tx storage observableSlots).sharedState
                  store : EvmYul.Yul.State).toSharedState with
                toState := state' }),
            [storage (IRStorageSlot.ofNat slot)]) := by
  rw [primCall_sload_ok]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 slot) = loaded
  cases loaded with
  | mk state' value =>
      have hloadShared :
          (initialState contract tx storage observableSlots).sharedState.sload
              (natToUInt256 slot) = (state', value) := by
        simpa [initialState, YulState.initial, toSharedState,
          EvmYul.Yul.State.sharedState, EvmYul.Yul.State.toState] using hload
      have hvalue :=
        initialState_sload_observableSlot_value contract tx storage
          observableSlots slot hSlot hRange
      rw [hload] at hvalue
      simp only at hvalue
      simp [hloadShared, hvalue, EvmYul.Yul.State.toState]

/-- Native primitive execution of `sload(slot)` is independent of the current
    Yul local-variable store when reading an omitted word-canonical slot. -/
theorem primCall_sload_initialState_omittedSlot_ok_withStore
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot : Nat)
    (hNotSlot : slot ∉ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size)
    (hSlotRange : slot < EvmYul.UInt256.size) :
    EvmYul.Yul.primCall (fuel + 1)
        (.Ok (initialState contract tx storage observableSlots).sharedState store)
        EvmYul.Operation.SLOAD [natToUInt256 slot] =
      match EvmYul.State.sload
          (initialState contract tx storage observableSlots).toState
          (natToUInt256 slot) with
      | (state', _) =>
          .ok (((.Ok (initialState contract tx storage observableSlots).sharedState
                store : EvmYul.Yul.State).setSharedState
              { (.Ok (initialState contract tx storage observableSlots).sharedState
                  store : EvmYul.Yul.State).toSharedState with
                toState := state' }),
            [natToUInt256 0]) := by
  rw [primCall_sload_ok]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 slot) = loaded
  cases loaded with
  | mk state' value =>
      have hloadShared :
          (initialState contract tx storage observableSlots).sharedState.sload
              (natToUInt256 slot) = (state', value) := by
        simpa [initialState, YulState.initial, toSharedState,
          EvmYul.Yul.State.sharedState, EvmYul.Yul.State.toState] using hload
      have hvalue :=
        initialState_sload_omittedSlot_value contract tx storage
          observableSlots slot hNotSlot hRange hSlotRange
      rw [hload] at hvalue
      simp only at hvalue
      simp [hloadShared, hvalue, EvmYul.Yul.State.toState]

/-- Native primitive execution of `sstore(slot, value)` on an initial runtime
    state succeeds with the exact EVMYulLean `State.sstore` successor. The
    range hypothesis records the word-canonical slot condition needed by the
    dispatcher proof when this lemma is connected to projected storage. -/
theorem primCall_sstore_initialState_wordSlot_ok
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot value : Nat)
    (_hSlotRange : slot < EvmYul.UInt256.size) :
    EvmYul.Yul.primCall (fuel + 1)
        (initialState contract tx storage observableSlots)
        EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
      .ok (((initialState contract tx storage observableSlots).setState
          ((initialState contract tx storage observableSlots).toState.sstore
            (natToUInt256 slot) (natToUInt256 value))), []) := by
  rw [primCall_sstore_ok]
  simp [initialState, EvmYul.Yul.State.executionEnv]

/-- Native primitive execution of `sstore(slot, value)` from an initial runtime
    shared state is independent of the current Yul local-variable store. This
    packages the word-slot storage write in the shape produced after dispatcher
    switch temporaries have been inserted. -/
theorem primCall_sstore_initialState_wordSlot_ok_withStore
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot value : Nat)
    (_hSlotRange : slot < EvmYul.UInt256.size) :
    EvmYul.Yul.primCall (fuel + 1)
        (.Ok (initialState contract tx storage observableSlots).sharedState store)
        EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
      .ok (((.Ok (initialState contract tx storage observableSlots).sharedState store :
          EvmYul.Yul.State).setState
          ((.Ok (initialState contract tx storage observableSlots).sharedState store :
              EvmYul.Yul.State).toState.sstore
            (natToUInt256 slot) (natToUInt256 value))), []) := by
  rw [primCall_sstore_ok]
  simp [initialState, EvmYul.Yul.State.sharedState,
    EvmYul.Yul.State.executionEnv, YulState.initial, toSharedState]

/-- Native primitive execution of the generated `store(uint256)` core:
    `calldataload(4)` decodes the first ABI argument and the following
    `sstore(0, value)` writes that word to slot zero. This is the real native
    primitive sequence under the emitted SimpleStorage setter body, before the
    terminating `stop`. -/
theorem primCall_calldataload4_then_sstore0_initialState_arg0_ok
    (loadFuel storeFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    (do
      let (state', values) ←
        EvmYul.Yul.primCall (loadFuel + 1)
          (initialState contract tx storage observableSlots)
          EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
      match values with
      | [value] =>
          EvmYul.Yul.primCall (storeFuel + 1) state'
            EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
      | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
      .ok (((initialState contract tx storage observableSlots).setState
        ((initialState contract tx storage observableSlots).toState.sstore
          (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))), []) := by
  rw [primCall_calldataload4_initialState_arg0_ok loadFuel contract tx storage
    observableSlots arg rest hArgs]
  change EvmYul.Yul.primCall (storeFuel + 1)
      (initialState contract tx storage observableSlots)
      EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, natToUInt256 arg] =
    .ok (((initialState contract tx storage observableSlots).setState
      ((initialState contract tx storage observableSlots).toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))), [])
  exact primCall_sstore_initialState_wordSlot_ok storeFuel contract tx storage
    observableSlots 0 arg (by norm_num [EvmYul.UInt256.size])

/-- Native primitive execution of the `return(0, 32)` half of the generated
    scalar-return sequence after `mstore(0, value)`. EVMYulLean models `RETURN`
    as a Yul halt carrying the post-`evmReturn` state; the halt literal is the
    default nonzero marker produced by `binaryMachineStateOp`, while the actual
    returned bytes live in the state's `H_return` buffer. -/
theorem primCall_return32_after_mstore0_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1)
        (state.setMachineState
          (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value))
        EvmYul.Operation.RETURN
        [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32] =
      .error (EvmYul.Yul.Exception.YulHalt
        ((state.setMachineState
            (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)).setMachineState
          ((state.setMachineState
              (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)).toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32)))
        ⟨1⟩) := by
  rw [primCall_return_ok]
  simp [EvmYul.Yul.binaryMachineStateOp]

/-- Native primitive execution of the generated scalar-return instruction pair
    through EVMYulLean's actual `MSTORE` and `RETURN` primitive relation. This
    exposes the exact halt state that remains to be connected to Verity's
    single-word `returnValue` projection. -/
theorem primCall_mstore0_then_return32_ok
    (mstoreFuel returnFuel : Nat)
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    (do
      let (state', values) ←
        EvmYul.Yul.primCall (mstoreFuel + 1) state
          EvmYul.Operation.MSTORE
          [EvmYul.UInt256.ofNat 0, value]
      match values with
      | [] =>
          EvmYul.Yul.primCall (returnFuel + 1) state'
            EvmYul.Operation.RETURN
            [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
      | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
      .error (EvmYul.Yul.Exception.YulHalt
        ((state.setMachineState
            (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)).setMachineState
          ((state.setMachineState
              (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)).toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32)))
        ⟨1⟩) := by
  rw [primCall_mstore_ok]
  exact primCall_return32_after_mstore0_ok returnFuel state value

/-- The native return buffer produced by `mstore(0, value); return(0, 32)` is
    exactly one EVM word wide. -/
theorem mstore0_then_return32_hReturn_size
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256) :
    let state : EvmYul.Yul.State := .Ok sharedState store
    let stored :=
      state.setMachineState
        (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)
    let returned :=
      stored.setMachineState
        (stored.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32))
    returned.sharedState.H_return.size = 32 := by
  dsimp
  have hZero : (EvmYul.UInt256.ofNat 0).toNat = 0 := by
    rfl
  have hLen : (EvmYul.UInt256.ofNat 32).toNat = 32 := by
    rfl
  simp [EvmYul.MachineState.evmReturn, readWithPadding_32_size,
    EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes,
    EvmYul.UInt256.toByteArray, EvmYul.Yul.State.setMachineState,
    EvmYul.Yul.State.sharedState, EvmYul.Yul.State.toMachineState, hZero, hLen]

/-- If the generated scalar-return sequence starts from empty memory and the
    value word is represented by exactly 32 bytes, then the native `RETURN`
    halt buffer is byte-for-byte the word written by `MSTORE`. -/
theorem mstore0_then_return32_emptyMemory_hReturn_eq
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256)
    (hMemory : sharedState.memory = ByteArray.empty)
    (hValueSize : value.toByteArray.size = 32) :
    let state : EvmYul.Yul.State := .Ok sharedState store
    let stored :=
      state.setMachineState
        (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)
    let returned :=
      stored.setMachineState
        (stored.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32))
    returned.sharedState.H_return = value.toByteArray := by
  dsimp
  simp only [EvmYul.Yul.State.toMachineState, EvmYul.Yul.State.setMachineState,
    EvmYul.Yul.State.sharedState]
  simp only [EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
    EvmYul.writeBytes, EvmYul.MachineState.evmReturn]
  simp only [hMemory]
  exact byteArray_write_empty_zero_32_readWithPadding_eq_of_size
    value.toByteArray hValueSize

/-- The generated scalar-return sequence started from empty memory returns
    exactly the 32-byte representation of the word written at offset zero. -/
theorem mstore0_then_return32_emptyMemory_hReturn_eq_toByteArray
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256)
    (hMemory : sharedState.memory = ByteArray.empty) :
    let state : EvmYul.Yul.State := .Ok sharedState store
    let stored :=
      state.setMachineState
        (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)
    let returned :=
      stored.setMachineState
        (stored.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32))
    returned.sharedState.H_return = value.toByteArray :=
  mstore0_then_return32_emptyMemory_hReturn_eq sharedState store value hMemory
    (uint256_toByteArray_size value)

/-- The concrete native primitive execution theorem for the generated scalar
    return sequence carries a one-word return buffer when started from an
    executable `Ok` Yul state. -/
theorem primCall_mstore0_then_return32_ok_hReturn_size
    (mstoreFuel returnFuel : Nat)
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256) :
    ∃ haltState haltValue,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (mstoreFuel + 1) (.Ok sharedState store)
            EvmYul.Operation.MSTORE
            [EvmYul.UInt256.ofNat 0, value]
        match values with
        | [] =>
            EvmYul.Yul.primCall (returnFuel + 1) state'
              EvmYul.Operation.RETURN
              [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      haltState.sharedState.H_return.size = 32 := by
  refine ⟨
    ((EvmYul.Yul.State.Ok sharedState store).setMachineState
        ((EvmYul.Yul.State.Ok sharedState store).toMachineState.mstore
          (EvmYul.UInt256.ofNat 0) value)).setMachineState
      (((EvmYul.Yul.State.Ok sharedState store).setMachineState
          ((EvmYul.Yul.State.Ok sharedState store).toMachineState.mstore
            (EvmYul.UInt256.ofNat 0) value)).toMachineState.evmReturn
        (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32)),
    ⟨1⟩, ?_⟩
  constructor
  · exact primCall_mstore0_then_return32_ok mstoreFuel returnFuel
      (.Ok sharedState store) value
  · exact mstore0_then_return32_hReturn_size sharedState store value

/-- Native initial-state storage materialization defaults omitted observable
    pre-state slots to zero. The in-range hypotheses rule out modular aliasing
    through the EVM word key used by the finite native storage map. -/
theorem initialState_omittedStorageSlot
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot : Nat)
    (hNotSlot : slot ∉ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size)
    (hSlotRange : slot < EvmYul.UInt256.size) :
    projectStorageFromState tx
      (initialState contract tx storage observableSlots) (IRStorageSlot.ofNat slot) = 0 := by
  simp only [projectStorageFromState, extractStorage, initialState,
    EvmYul.Yul.State.sharedState, YulState.initial, toSharedState]
  rw [treeMap_get?_insert_self]
  rw [treeMap_get?_insert_self]
  simp only
  have h := foldl_insert_find_not_mem storage observableSlots slot hNotSlot
    hRange hSlotRange (Std.TreeMap.empty : EvmYul.Storage)
  have hNone :
      (projectStorage storage observableSlots).get? (natToUInt256 slot) = none := by
    simpa [projectStorage] using h
  have hNone' :
      (projectStorage storage observableSlots)[EvmYul.UInt256.ofNat slot]? = none :=
    treeMap_getElem?_none_of_get? _ _ hNone
  simp [IRStorageSlot.toUInt256, IRStorageSlot.ofNat, hNone']

/-- Decode one 32-byte big-endian word from an EVMYulLean byte array. -/
def byteArrayWord (bytes : ByteArray) (offset : Nat) : Nat :=
  (List.range 32).foldl
    (fun acc i => (acc * 256 + ((byteArrayGet? bytes (offset + i)).getD 0).toNat) %
      Compiler.Constants.evmModulus)
    0

private def listByteArrayWordNoMod (bytes : List UInt8) (n : Nat) : Nat :=
  (List.range n).foldl
    (fun acc i => acc * 256 + ((bytes[i]?).getD 0).toNat) 0

private def listByteArrayWordMod (bytes : List UInt8) (n : Nat) : Nat :=
  (List.range n).foldl
    (fun acc i => (acc * 256 + ((bytes[i]?).getD 0).toNat) %
      Compiler.Constants.evmModulus) 0

private theorem fromBytes'_reverse_append_single (xs : List UInt8) (b : UInt8) :
    EvmYul.fromBytes' ((xs ++ [b]).reverse) =
      EvmYul.fromBytes' xs.reverse * 256 + b.toNat := by
  simp [EvmYul.fromBytes']
  omega

private theorem listByteArrayWordNoMod_eq_fromBytes'_take_reverse
    (bytes : List UInt8) (n : Nat)
    (hn : n ≤ bytes.length) :
    listByteArrayWordNoMod bytes n =
      EvmYul.fromBytes' (bytes.take n).reverse := by
  induction n with
  | zero =>
      simp [listByteArrayWordNoMod, EvmYul.fromBytes']
  | succ n ih =>
      have hn' : n ≤ bytes.length := by omega
      have hlt : n < bytes.length := by omega
      unfold listByteArrayWordNoMod at ih ⊢
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih hn']
      rw [List.take_succ]
      rw [List.getElem?_eq_getElem hlt]
      simp only [Option.getD_some, Option.toList_some]
      rw [fromBytes'_reverse_append_single]

private theorem listByteArrayWordNoMod_lt
    (bytes : List UInt8) (n : Nat)
    (hn : n ≤ bytes.length) :
    listByteArrayWordNoMod bytes n < 2 ^ (8 * n) := by
  rw [listByteArrayWordNoMod_eq_fromBytes'_take_reverse bytes n hn]
  have h := fromBytes'_lt (bytes.take n).reverse
  have hlen : (bytes.take n).reverse.length = n := by
    simp [List.length_take, hn]
  simpa [hlen] using h

private theorem listByteArrayWordMod_eq_noMod
    (bytes : List UInt8) (n : Nat)
    (hnLen : n ≤ bytes.length) (hnWord : n ≤ 32) :
    listByteArrayWordMod bytes n = listByteArrayWordNoMod bytes n := by
  induction n with
  | zero =>
      simp [listByteArrayWordMod, listByteArrayWordNoMod]
  | succ n ih =>
      have hnLen' : n ≤ bytes.length := by omega
      have hnWord' : n ≤ 32 := by omega
      unfold listByteArrayWordMod listByteArrayWordNoMod at ih ⊢
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih hnLen' hnWord']
      have hNoMod :
          (List.foldl (fun acc i => acc * 256 + (bytes[i]?.getD 0).toNat) 0
                (List.range n) *
              256 +
            (bytes[n]?.getD 0).toNat) < Compiler.Constants.evmModulus := by
        rw [show
            List.foldl (fun acc i => acc * 256 + (bytes[i]?.getD 0).toNat)
                0 (List.range n) =
              listByteArrayWordNoMod bytes n by rfl]
        have hprev := listByteArrayWordNoMod_lt bytes n hnLen'
        have hb : (bytes[n]?.getD 0).toNat < 256 := by
          cases hopt : bytes[n]?
          · simp
          · simp
            exact UInt8.toNat_lt _
        have hpow : 2 ^ (8 * n) * 256 = 2 ^ (8 * (n + 1)) := by
          rw [Nat.mul_add, Nat.pow_add]
        have hle : 2 ^ (8 * (n + 1)) ≤ Compiler.Constants.evmModulus := by
          have : 8 * (n + 1) ≤ 256 := by omega
          unfold Compiler.Constants.evmModulus
          exact Nat.pow_le_pow_right (by norm_num) this
        nlinarith
      rw [Nat.mod_eq_of_lt hNoMod]

private theorem byteArray_get?_data_toList (bytes : ByteArray) (i : Nat) :
    byteArrayGet? bytes i = bytes.data.toList[i]? := by
  simp [byteArrayGet?, Array.getElem?_toList]

theorem byteArrayWord_eq_fromBytes'_reverse_of_size
    (bytes : ByteArray)
    (hSize : bytes.size = 32) :
    byteArrayWord bytes 0 = EvmYul.fromBytes' bytes.data.toList.reverse := by
  have hLen : bytes.data.toList.length = 32 := by
    rw [Array.length_toList]
    exact hSize
  unfold byteArrayWord
  rw [show
      List.foldl
          (fun acc i => (acc * 256 + ((byteArrayGet? bytes (0 + i)).getD 0).toNat) %
            Compiler.Constants.evmModulus)
          0 (List.range 32) =
        listByteArrayWordMod bytes.data.toList 32 by
      unfold listByteArrayWordMod
      congr 3
      funext acc i
      simp only [byteArray_get?_data_toList, Nat.zero_add]]
  rw [listByteArrayWordMod_eq_noMod bytes.data.toList 32 (by omega) (by omega)]
  have hNoMod :=
    listByteArrayWordNoMod_eq_fromBytes'_take_reverse bytes.data.toList 32
      (by omega)
  rw [hNoMod]
  rw [show bytes.data.toList.take 32 = bytes.data.toList by
    rw [← hLen, List.take_length]]

private theorem fromBytes'_replicate_zero (n : Nat) :
    EvmYul.fromBytes' (List.replicate n (0 : UInt8)) = 0 := by
  induction n with
  | zero =>
      simp [EvmYul.fromBytes']
  | succ n ih =>
      simp [List.replicate, EvmYul.fromBytes', ih]

private theorem fromBytes'_append_replicate_zero (xs : List UInt8) (n : Nat) :
    EvmYul.fromBytes' (xs ++ List.replicate n (0 : UInt8)) =
      EvmYul.fromBytes' xs := by
  rw [fromBytes'_append]
  simp [fromBytes'_replicate_zero]

theorem byteArrayWord_uint256_toByteArray
    (value : EvmYul.UInt256) :
    byteArrayWord value.toByteArray 0 = value.toNat := by
  rw [byteArrayWord_eq_fromBytes'_reverse_of_size
    value.toByteArray (uint256_toByteArray_size value)]
  unfold EvmYul.UInt256.toByteArray BE
  simp [ByteArray.data_append, ffi.ByteArray.zeroes,
    list_toByteArray_data_toList]
  simp [EvmYul.toBytesBigEndian]

/-- Decode the word-granular payload used by Verity's proof-side log model. -/
def byteArrayLogWords (bytes : ByteArray) : List Nat :=
  (List.range (bytes.size / 32)).map (fun i => byteArrayWord bytes (i * 32))

/-- Project native EVMYulLean logs to the current Verity observable event shape:
    topics followed by word-aligned log data. -/
def projectLogEntry (entry : EvmYul.LogEntry) : List Nat :=
  entry.topics.toList.map uint256ToNat ++ byteArrayLogWords entry.data

def projectLogsFromState (state : EvmYul.Yul.State) : List (List Nat) :=
  state.sharedState.substate.logSeries.toList.map projectLogEntry

@[simp] theorem projectLogEntry_topicsAndWordData
    (entry : EvmYul.LogEntry) :
    projectLogEntry entry =
      entry.topics.toList.map uint256ToNat ++ byteArrayLogWords entry.data := by
  rfl

@[simp] theorem projectLogsFromState_logSeries
    (state : EvmYul.Yul.State) :
    projectLogsFromState state =
      state.sharedState.substate.logSeries.toList.map projectLogEntry := by
  rfl

@[simp] theorem projectLogsFromState_initialState
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) :
    projectLogsFromState (initialState contract tx storage slots) = [] := by
  simp [projectLogsFromState, initialState, EvmYul.Yul.State.sharedState,
    YulState.initial, toSharedState, mkBlockHeader]
  rfl

@[simp] theorem projectLogsFromState_reviveJump
    (state : EvmYul.Yul.State) :
    projectLogsFromState state.reviveJump = projectLogsFromState state := by
  cases state <;> rfl

@[simp] theorem projectLogsFromState_nativeSwitchStoreMarkedPrefixStateForId
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore) :
    projectLogsFromState
      (nativeSwitchStoreMarkedPrefixStateForId contract tx storage slots
        switchId store) = [] := by
  change projectLogsFromState (initialState contract tx storage slots) = []
  exact projectLogsFromState_initialState contract tx storage slots

@[simp] theorem projectLogsFromState_nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore) :
    projectLogsFromState
      (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
        storage slots switchId store) = [] := by
  simp [projectLogsFromState,
    nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
    nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
    nativeSwitchPostInitFreeMemoryState,
    nativeSwitchPostInitFreeMemorySharedState,
    initialState, EvmYul.Yul.State.insert, EvmYul.Yul.State.sharedState,
    YulState.initial, toSharedState, mkBlockHeader]
  rfl

theorem projectStorageFromState_setStore_ok_left
    (tx : YulTransaction)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (initial : EvmYul.Yul.State) :
    projectStorageFromState tx
        (((EvmYul.Yul.State.Ok shared store) : EvmYul.Yul.State).setStore
          initial) =
      projectStorageFromState tx (EvmYul.Yul.State.Ok shared store) := by
  funext slot
  cases initial <;>
    simp [EvmYul.Yul.State.setStore, projectStorageFromState,
      EvmYul.Yul.State.sharedState]

theorem projectLogsFromState_setStore_ok_left
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (initial : EvmYul.Yul.State) :
    projectLogsFromState
        (((EvmYul.Yul.State.Ok shared store) : EvmYul.Yul.State).setStore
          initial) =
      projectLogsFromState (EvmYul.Yul.State.Ok shared store) := by
  cases initial <;>
    simp [EvmYul.Yul.State.setStore, projectLogsFromState,
      EvmYul.Yul.State.sharedState]

/-- Project a native Yul halt produced by `return`/`stop` to Verity's single-word
    return observable. EVMYulLean represents `stop` as `YulHalt _ 0`; `return`
    goes through `H_return`, matching the proof oracle's 32-byte return case. -/
def projectHaltReturn (state : EvmYul.Yul.State) (haltValue : EvmYul.Yul.Ast.Literal) :
    Option Nat :=
  if haltValue = ⟨0⟩ then
    none
  else if state.sharedState.H_return.size = 32 then
    some (byteArrayWord state.sharedState.H_return 0)
  else
    some 0

@[simp] theorem projectHaltReturn_stop
    (state : EvmYul.Yul.State) :
    projectHaltReturn state ⟨0⟩ = none := by
  simp [projectHaltReturn]

@[simp] theorem projectHaltReturn_32ByteReturn
    (state : EvmYul.Yul.State)
    (haltValue : EvmYul.Yul.Ast.Literal)
    (hHalt : haltValue ≠ ⟨0⟩)
    (hSize : state.sharedState.H_return.size = 32) :
    projectHaltReturn state haltValue =
      some (byteArrayWord state.sharedState.H_return 0) := by
  simp [projectHaltReturn, hHalt, hSize]

/-- Until wider returndata support lands, a non-`stop` halt with a native return
    buffer whose size is not exactly one ABI word projects to the conservative
    single-word fallback used by the current proof-side observable model. -/
@[simp] theorem projectHaltReturn_non32ByteReturn
    (state : EvmYul.Yul.State)
    (haltValue : EvmYul.Yul.Ast.Literal)
    (hHalt : haltValue ≠ ⟨0⟩)
    (hSize : state.sharedState.H_return.size ≠ 32) :
    projectHaltReturn state haltValue = some 0 := by
  simp [projectHaltReturn, hHalt, hSize]

theorem primCall_mstore0_then_return32_emptyMemory_projectHaltReturn
    (mstoreFuel returnFuel : Nat)
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256)
    (hMemory : sharedState.memory = ByteArray.empty) :
    ∃ haltState haltValue,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (mstoreFuel + 1) (.Ok sharedState store)
            EvmYul.Operation.MSTORE
            [EvmYul.UInt256.ofNat 0, value]
        match values with
        | [] =>
            EvmYul.Yul.primCall (returnFuel + 1) state'
              EvmYul.Operation.RETURN
              [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectHaltReturn haltState haltValue = some value.toNat := by
  let state : EvmYul.Yul.State := .Ok sharedState store
  let stored :=
    state.setMachineState
      (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)
  let returned :=
    stored.setMachineState
      (stored.toMachineState.evmReturn
        (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32))
  refine ⟨returned, ⟨1⟩, ?_⟩
  constructor
  · exact primCall_mstore0_then_return32_ok mstoreFuel returnFuel
      (.Ok sharedState store) value
  · have hHalt : (⟨1⟩ : EvmYul.Yul.Ast.Literal) ≠ ⟨0⟩ := by
      intro h
      norm_num [EvmYul.UInt256.size] at h
    have hSize : returned.sharedState.H_return.size = 32 := by
      exact mstore0_then_return32_hReturn_size sharedState store value
    have hReturn : returned.sharedState.H_return = value.toByteArray := by
      exact mstore0_then_return32_emptyMemory_hReturn_eq_toByteArray
        sharedState store value hMemory
    rw [projectHaltReturn_32ByteReturn returned ⟨1⟩ hHalt hSize]
    rw [hReturn, byteArrayWord_uint256_toByteArray]

/-- The dispatcher-block execution that `EvmYul.Yul.callDispatcher` performs
    after its initial fuel check and empty-argument call-frame setup.

Keeping this expression named lets the native/EVMYulLean bridge target
statement execution of the lowered dispatcher body directly, instead of
re-opening the full `callDispatcher` wrapper at each EndToEnd proof site. -/
def callDispatcherBlockResult
    (fuel' : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (initial : EvmYul.Yul.State) :
    Except EvmYul.Yul.Exception
      (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal) :=
  let dispatcherDef :=
    EvmYul.Yul.Ast.FunctionDefinition.Def [] []
      [initial.executionEnv.code.dispatcher]
  let callState := EvmYul.Yul.State.mkOk (initial.initcall dispatcherDef.params [])
  match EvmYul.Yul.exec fuel' (.Block dispatcherDef.body) (some contract) callState with
  | .error err => .error err
  | .ok finalState =>
      let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
      .ok (restored, List.map finalState.lookup! dispatcherDef.rets)

/-- Dispatcher-block execution specialized to the lowered contract dispatcher
    rather than the state-installed dispatcher lookup.

For states built by `initialState`, this is definitionally the next proof
target after `callDispatcherBlockResult`: native execution of the lowered
contract's dispatcher statement. -/
def contractDispatcherBlockResult
    (fuel' : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (initial : EvmYul.Yul.State) :
    Except EvmYul.Yul.Exception
      (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal) :=
  let dispatcherDef :=
    EvmYul.Yul.Ast.FunctionDefinition.Def [] [] [contract.dispatcher]
  let callState := EvmYul.Yul.State.mkOk (initial.initcall dispatcherDef.params [])
  match EvmYul.Yul.exec fuel' (.Block dispatcherDef.body) (some contract) callState with
  | .error err => .error err
  | .ok finalState =>
      let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
      .ok (restored, List.map finalState.lookup! dispatcherDef.rets)

/-- Raw native execution of the lowered contract dispatcher block, before the
    `callDispatcher`-style state restoration and return-list projection. -/
def contractDispatcherExecResult
    (fuel' : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (initial : EvmYul.Yul.State) :
    Except EvmYul.Yul.Exception EvmYul.Yul.State :=
  let dispatcherDef :=
    EvmYul.Yul.Ast.FunctionDefinition.Def [] [] [contract.dispatcher]
  let callState := EvmYul.Yul.State.mkOk (initial.initcall dispatcherDef.params [])
  EvmYul.Yul.exec fuel' (.Block dispatcherDef.body) (some contract) callState

/-- Executing a singleton block whose only statement is another block is the
    same as executing the inner block, after the outer block consumes its fuel
    step. This is the structural wrapper around lowered contract dispatchers:
    `contractDispatcherExecResult` installs `[contract.dispatcher]` as the
    function body, while generated dispatcher lemmas reason about the lowered
    block itself. -/
theorem exec_singleton_block_eq_exec_block
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (Nat.succ (Nat.succ fuel)) (.Block [.Block body])
        codeOverride state =
      EvmYul.Yul.exec (Nat.succ fuel) (.Block body) codeOverride state := by
  cases hInner :
      EvmYul.Yul.exec (Nat.succ fuel) (.Block body) codeOverride state with
  | error err =>
      exact
        exec_block_cons_error (Nat.succ fuel) (.Block body) [] codeOverride
          state err hInner
  | ok middle =>
      have hRight :
          EvmYul.Yul.exec (Nat.succ fuel) (.Block []) codeOverride middle =
            .ok middle := by
        simp [EvmYul.Yul.exec]
      exact
        exec_block_cons_ok (Nat.succ fuel) (.Block body) [] codeOverride
          state middle middle hInner hRight

/-- Raw dispatcher execution for a lowered contract whose dispatcher is already
    a block reduces to direct execution of that block from the native initial
    switch state. This removes the function-call-frame wrapper from later
    SimpleStorage dispatcher case proofs. -/
theorem contractDispatcherExecResult_block_dispatcher_eq_exec_block
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    contractDispatcherExecResult (Nat.succ (Nat.succ fuel))
        { dispatcher := .Block body, functions := functions }
        (initialState { dispatcher := .Block body, functions := functions } tx
          storage observableSlots) =
      EvmYul.Yul.exec (Nat.succ fuel) (.Block body)
        (some { dispatcher := .Block body, functions := functions })
        (nativeSwitchInitialOkState
          { dispatcher := .Block body, functions := functions } tx storage
          observableSlots) := by
  have hCallState :
      EvmYul.Yul.State.mkOk
          ((initialState { dispatcher := .Block body, functions := functions } tx
            storage observableSlots).initcall [] []) =
        nativeSwitchInitialOkState
          { dispatcher := .Block body, functions := functions } tx storage
          observableSlots := by
    simp [nativeSwitchInitialOkState, initialState, EvmYul.Yul.State.initcall,
      EvmYul.Yul.State.setStore, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.mkOk]
    constructor <;> rfl
  unfold contractDispatcherExecResult
  change
    EvmYul.Yul.exec (Nat.succ (Nat.succ fuel)) (.Block [.Block body])
        (some { dispatcher := .Block body, functions := functions })
        (EvmYul.Yul.State.mkOk
          ((initialState { dispatcher := .Block body, functions := functions } tx
            storage observableSlots).initcall [] [])) =
      EvmYul.Yul.exec (Nat.succ fuel) (.Block body)
        (some { dispatcher := .Block body, functions := functions })
        (nativeSwitchInitialOkState
          { dispatcher := .Block body, functions := functions } tx storage
          observableSlots)
  rw [hCallState]
  exact exec_singleton_block_eq_exec_block fuel body
    (some { dispatcher := .Block body, functions := functions })
    (nativeSwitchInitialOkState
      { dispatcher := .Block body, functions := functions } tx storage
      observableSlots)

/-- The projected dispatcher-block result is just raw lowered-dispatcher
    execution followed by the same restoration/projection used by
    `callDispatcher`. -/
theorem contractDispatcherBlockResult_eq_execResult
    (fuel' : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (initial : EvmYul.Yul.State) :
    contractDispatcherBlockResult fuel' contract initial =
      let dispatcherDef :=
        EvmYul.Yul.Ast.FunctionDefinition.Def [] [] [contract.dispatcher]
      match contractDispatcherExecResult fuel' contract initial with
      | .error err => .error err
      | .ok finalState =>
          let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
          .ok (restored, List.map finalState.lookup! dispatcherDef.rets) := by
  simp [contractDispatcherBlockResult, contractDispatcherExecResult]

/-- `initialState` installs the lowered contract as the execution contract, so
    the dispatcher-block target can be rewritten to the lowered contract's own
    dispatcher. -/
theorem callDispatcherBlockResult_initialState_eq_contractDispatcherBlockResult
    (fuel' : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    callDispatcherBlockResult fuel' contract
        (initialState contract tx storage observableSlots) =
      contractDispatcherBlockResult fuel' contract
        (initialState contract tx storage observableSlots) := by
  have hcode :
      (initialState contract tx storage observableSlots).executionEnv.code =
        contract := by
    simp [initialState, EvmYul.Yul.State.executionEnv]
  simp [callDispatcherBlockResult, contractDispatcherBlockResult, hcode]

@[simp] theorem callDispatcher_zero
    (contract : EvmYul.Yul.Ast.YulContract)
    (initial : EvmYul.Yul.State) :
    EvmYul.Yul.callDispatcher 0 (some contract) initial =
      .error EvmYul.Yul.Exception.OutOfFuel := by
  simp [EvmYul.Yul.callDispatcher]

/-- `callDispatcher` is exactly execution of the installed dispatcher block
    once fuel and call-frame setup have been peeled away. -/
theorem callDispatcher_succ_eq_callDispatcherBlockResult
    (fuel' : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (initial : EvmYul.Yul.State) :
    EvmYul.Yul.callDispatcher (Nat.succ fuel') (some contract) initial =
      callDispatcherBlockResult fuel' contract initial := by
  simp [EvmYul.Yul.callDispatcher, callDispatcherBlockResult]
  cases
    EvmYul.Yul.exec fuel'
      (.Block
        (EvmYul.Yul.Ast.FunctionDefinition.Def [] []
          [initial.executionEnv.code.dispatcher]).body)
      (some contract)
      (EvmYul.Yul.State.mkOk
        (initial.initcall
          (EvmYul.Yul.Ast.FunctionDefinition.Def [] []
            [initial.executionEnv.code.dispatcher]).params [])) <;> rfl

/-- Convert a native `callDispatcher` result to the current Verity observable
    result shape. Reverts and hard native errors conservatively roll storage
    back to the supplied initial storage function. -/
def projectResult
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (result :
      Except EvmYul.Yul.Exception
        (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal)) :
    YulResult :=
  match result with
  | .ok (state, values) =>
      let finalStorage := projectStorageFromState tx state
      { success := true
        returnValue := values.head?.map uint256ToNat
        finalStorage := finalStorage
        finalMappings := Compiler.Proofs.storageAsMappings finalStorage
        events := initialEvents ++ projectLogsFromState state }
  | .error (.YulHalt state value) =>
      let finalStorage := projectStorageFromState tx state
      { success := true
        returnValue := projectHaltReturn state value
        finalStorage := finalStorage
        finalMappings := Compiler.Proofs.storageAsMappings finalStorage
        events := initialEvents ++ projectLogsFromState state }
  | .error _ =>
      { success := false
        returnValue := none
        finalStorage := initialStorage
        finalMappings := Compiler.Proofs.storageAsMappings initialStorage
        events := initialEvents }

@[simp] theorem projectResult_ok
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    projectResult tx initialStorage initialEvents (.ok (state, values)) =
    { success := true
      returnValue := values.head?.map uint256ToNat
      finalStorage := projectStorageFromState tx state
      finalMappings :=
        Compiler.Proofs.storageAsMappings (projectStorageFromState tx state)
      events := initialEvents ++ projectLogsFromState state } := by
  rfl

theorem projectResult_ok_nativeSwitchStoreMarkedPrefixStateForId_success
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (slots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore) :
    (projectResult tx storage initialEvents
      (.ok
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage slots
          switchId store, []))).success = true := by
  rfl

theorem projectResult_ok_nativeSwitchStoreMarkedPrefixStateForId_returnValue
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (slots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore) :
    (projectResult tx storage initialEvents
      (.ok
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage slots
          switchId store, []))).returnValue = none := by
  rfl

theorem projectResult_ok_nativeSwitchStoreMarkedPrefixStateForId_events
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (slots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore) :
    (projectResult tx storage initialEvents
      (.ok
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage slots
          switchId store, []))).events = initialEvents := by
  change initialEvents ++ projectLogsFromState
      (nativeSwitchStoreMarkedPrefixStateForId contract tx storage slots
        switchId store) = initialEvents
  rw [projectLogsFromState_nativeSwitchStoreMarkedPrefixStateForId]
  simp

theorem projectResult_ok_nativeSwitchStoreMarkedPrefixStateForId_storageSlot
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (slots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (slot : Nat)
    (hSlot : slot ∈ slots) :
    (projectResult tx storage initialEvents
      (.ok
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage slots
          switchId store, []))).finalStorage (IRStorageSlot.ofNat slot) =
      storage (IRStorageSlot.ofNat slot) := by
  simpa [projectResult] using
    (nativeSwitchStoreMarkedPrefixStateForId_materializedStorageSlot contract tx
      storage slots switchId store slot hSlot)

theorem projectResult_ok_nativeSwitchStoreMarkedPrefixStateForId_observableStorageSlot
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (runtimeCode : List YulStmt)
    (observableSlots : List Nat)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (slot : Nat)
    (hSlot : slot ∈ observableSlots) :
    (projectResult tx storage initialEvents
      (.ok
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          (materializedStorageSlots runtimeCode observableSlots)
          switchId store, []))).finalStorage (IRStorageSlot.ofNat slot) =
      storage (IRStorageSlot.ofNat slot) := by
  exact
    projectResult_ok_nativeSwitchStoreMarkedPrefixStateForId_storageSlot
      contract tx storage initialEvents
      (materializedStorageSlots runtimeCode observableSlots) switchId store slot
      (observableSlot_mem_materializedStorageSlots runtimeCode observableSlots
        slot hSlot)

theorem projectResult_ok_setStore_ok_left
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (initial : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    projectResult tx initialStorage initialEvents
        (.ok
          ((((EvmYul.Yul.State.Ok shared store) : EvmYul.Yul.State).setStore
            initial), values)) =
      projectResult tx initialStorage initialEvents
        (.ok (EvmYul.Yul.State.Ok shared store, values)) := by
  cases initial <;>
    simp [projectResult, EvmYul.Yul.State.setStore, projectStorageFromState,
      EvmYul.Yul.State.sharedState, projectLogsFromState]

theorem projectResult_ok_restoreCallFrame_of_reviveJump_ok
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (final initial : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hRevive :
      final.reviveJump = EvmYul.Yul.State.Ok shared store)
    (hInitialOk :
      ∃ initialShared initialStore,
        initial = EvmYul.Yul.State.Ok initialShared initialStore) :
    projectResult tx initialStorage initialEvents
        (.ok (((final.reviveJump.overwrite? initial).setStore initial), values)) =
      projectResult tx initialStorage initialEvents
        (.ok (final.reviveJump, values)) := by
  rcases hInitialOk with ⟨initialShared, initialStore, rfl⟩
  rw [hRevive]
  simpa [EvmYul.Yul.State.overwrite?] using
    (projectResult_ok_setStore_ok_left tx initialStorage initialEvents shared
      store (EvmYul.Yul.State.Ok initialShared initialStore) values)

/-- Exact projected result for native primitive execution of
    `sstore(slot, value)` from an initial runtime shared state and arbitrary
    dispatcher local-variable store.

This is the generic word-canonical `SSTORE` primitive result shape needed by
the dispatcher proof before the SimpleStorage setter composes it with
`CALLDATALOAD` and `STOP`. -/
theorem primCall_sstore_initialState_wordSlot_withStore_projectResult_eq
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (.Ok (initialState contract tx storage observableSlots).sharedState store)
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      projectResult tx storage initialEvents (.ok (finalState, [])) =
        { success := true
          returnValue := none
          finalStorage := projectStorageFromState tx finalState
          finalMappings :=
            Compiler.Proofs.storageAsMappings (projectStorageFromState tx finalState)
          events := initialEvents ++ projectLogsFromState finalState } := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  refine ⟨initialWithStore.setState
    (initialWithStore.toState.sstore (natToUInt256 slot) (natToUInt256 value)),
    ?_, ?_⟩
  · exact primCall_sstore_initialState_wordSlot_ok_withStore fuel contract tx
      storage observableSlots store slot value hSlotRange
  · simp [projectResult]

@[simp] theorem projectResult_yulHalt
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value)) =
    { success := true
      returnValue := projectHaltReturn state value
      finalStorage := projectStorageFromState tx state
      finalMappings :=
        Compiler.Proofs.storageAsMappings (projectStorageFromState tx state)
      events := initialEvents ++ projectLogsFromState state } := by
  rfl

@[simp] theorem projectResult_ok_events
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents (.ok (state, values))).events =
      initialEvents ++ projectLogsFromState state := by
  rfl

@[simp] theorem projectResult_ok_success
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).success = true := by
  rfl

@[simp] theorem projectResult_ok_returnValue
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).returnValue =
      values.head?.map uint256ToNat := by
  rfl

@[simp] theorem projectResult_ok_finalMappings
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).finalMappings =
      Compiler.Proofs.storageAsMappings (projectStorageFromState tx state) := by
  rfl

@[simp] theorem projectResult_ok_finalStorageSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (account : EvmYul.Account .Yul)
    (value : EvmYul.UInt256)
    (hAccount :
      state.sharedState.accountMap.get? (natToAddress tx.thisAddress) =
        some account)
    (hSlot : account.storage.get? (natToUInt256 slot) = some value) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).finalStorage (IRStorageSlot.ofNat slot) = value := by
  change projectStorageFromState tx state (IRStorageSlot.ofNat slot) = value
  exact projectStorageFromState_accountStorageSlot tx state slot account value hAccount hSlot

@[simp] theorem projectResult_ok_missingFinalStorageAccountSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (hAccount :
      state.sharedState.accountMap.get? (natToAddress tx.thisAddress) =
        none) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).finalStorage (IRStorageSlot.ofNat slot) = 0 := by
  change projectStorageFromState tx state (IRStorageSlot.ofNat slot) = 0
  exact projectStorageFromState_missingAccount tx state slot hAccount

@[simp] theorem projectResult_ok_missingFinalStorageSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (account : EvmYul.Account .Yul)
    (hAccount :
      state.sharedState.accountMap.get? (natToAddress tx.thisAddress) =
        some account)
    (hSlot : account.storage.get? (natToUInt256 slot) = none) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).finalStorage (IRStorageSlot.ofNat slot) = 0 := by
  change projectStorageFromState tx state (IRStorageSlot.ofNat slot) = 0
  exact projectStorageFromState_missingAccountStorageSlot tx state slot account hAccount hSlot

/-- Native primitive execution of `sstore(slot, value)` on a word-canonical
    initial runtime slot, lifted through Verity's projected native result
    boundary for a nonzero write.

This is the generic storage-projection form of the SimpleStorage slot-zero
setter lemma: it proves that the actual EVMYulLean `SSTORE` primitive writes
the projected final storage word for any canonical slot, as long as the EVM
storage update takes the insertion branch rather than the zero-value erasure
branch. -/
theorem primCall_sstore_initialState_wordSlot_projectResult_slot
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size)
    (hValueNonzero :
      (natToUInt256 value == (⟨0⟩ : EvmYul.UInt256)) = false) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (initialState contract tx storage observableSlots)
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat slot) =
        natToUInt256 value := by
  refine ⟨(initialState contract tx storage observableSlots).setState
    ((initialState contract tx storage observableSlots).toState.sstore
      (natToUInt256 slot) (natToUInt256 value)), ?_, ?_⟩
  · exact primCall_sstore_initialState_wordSlot_ok fuel contract tx storage
      observableSlots slot value hSlotRange
  · simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      YulState.initial, toSharedState]
    have hUpdate := account_updateStorage_storage_of_nonzero
      ({ nonce := (⟨0⟩ : EvmYul.UInt256), balance := (⟨0⟩ : EvmYul.UInt256),
         storage := projectStorage storage observableSlots, code := contract,
         tstorage := Std.TreeMap.empty } :
        EvmYul.Account .Yul)
      (natToUInt256 slot) (natToUInt256 value) hValueNonzero
    simp only [Option.option, treeMap_get?_insert_self]
    rw [hUpdate]
    simp [treeMap_get?_insert_self]

/-- Native primitive execution of `sstore(slot, 0)` on a word-canonical
    initial runtime slot, lifted through Verity's projected native result
    boundary with the EVMYulLean zero-write erasure lookup isolated.

This is the zero-write companion to
`primCall_sstore_initialState_wordSlot_projectResult_slot`: it proves the
actual native `SSTORE` primitive path and leaves only the map-level fact that
erasing a key makes the projected lookup miss. -/
theorem primCall_sstore_initialState_wordSlot_projectResult_slot_zero_of_erase
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size)
    (hValueZero :
      (natToUInt256 value == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (initialState contract tx storage observableSlots)
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat slot) =
        0 := by
  refine ⟨(initialState contract tx storage observableSlots).setState
    ((initialState contract tx storage observableSlots).toState.sstore
      (natToUInt256 slot) (natToUInt256 value)), ?_, ?_⟩
  · exact primCall_sstore_initialState_wordSlot_ok fuel contract tx storage
      observableSlots slot value hSlotRange
  · simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      YulState.initial, toSharedState, natToUInt256]
    have hUpdate := account_updateStorage_storage_of_zero
      ({ nonce := (⟨0⟩ : EvmYul.UInt256), balance := (⟨0⟩ : EvmYul.UInt256),
         storage := projectStorage storage observableSlots, code := contract,
         tstorage := Std.TreeMap.empty } : EvmYul.Account .Yul)
      (natToUInt256 slot) (natToUInt256 value) hValueZero
    simp only [Option.option, treeMap_get?_insert_self]
    rw [hUpdate]
    simp [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_erase_self]

/-- Native primitive execution of `sstore(slot, 0)` on a word-canonical
    initial runtime slot with no observable slots materialized. The zero-write
    erasure lookup is discharged by computation at the generic `SSTORE`
    projection boundary. -/
theorem primCall_sstore_initialState_wordSlot_projectResult_slot_zero_emptyObservable
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size)
    (hValueZero :
      (natToUInt256 value == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (initialState contract tx storage [])
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat slot) =
        0 := by
  exact
    primCall_sstore_initialState_wordSlot_projectResult_slot_zero_of_erase
      fuel contract tx storage initialEvents [] slot value hSlotRange hValueZero

/-- Native primitive execution of `sstore(slot, value)` from an initial runtime
    shared state and arbitrary local-variable store, lifted through Verity's
    projected native result boundary for a nonzero word-canonical write. This is
    the generic dispatcher-local-store companion to
    `primCall_sstore_initialState_wordSlot_projectResult_slot`. -/
theorem primCall_sstore_initialState_wordSlot_withStore_projectResult_slot
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size)
    (hValueNonzero :
      (natToUInt256 value == (⟨0⟩ : EvmYul.UInt256)) = false) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (.Ok (initialState contract tx storage observableSlots).sharedState store)
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat slot) =
        natToUInt256 value := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  refine ⟨initialWithStore.setState
    (initialWithStore.toState.sstore (natToUInt256 slot) (natToUInt256 value)),
    ?_, ?_⟩
  · exact primCall_sstore_initialState_wordSlot_ok_withStore fuel contract tx
      storage observableSlots store slot value hSlotRange
  · dsimp [initialWithStore]
    simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      YulState.initial, toSharedState]
    have hUpdate := account_updateStorage_storage_of_nonzero
      ({ nonce := (⟨0⟩ : EvmYul.UInt256), balance := (⟨0⟩ : EvmYul.UInt256),
         storage := projectStorage storage observableSlots, code := contract,
         tstorage := Std.TreeMap.empty } : EvmYul.Account .Yul)
      (natToUInt256 slot) (natToUInt256 value) hValueNonzero
    simp only [Option.option, treeMap_get?_insert_self]
    rw [hUpdate]
    simp [treeMap_get?_insert_self]

/-- Native primitive execution of `sstore(slot, 0)` from an initial runtime
    shared state and arbitrary local-variable store, lifted through Verity's
    projected native result boundary with the zero-write erasure lookup
    isolated. -/
theorem primCall_sstore_initialState_wordSlot_withStore_projectResult_slot_zero_of_erase
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size)
    (hValueZero :
      (natToUInt256 value == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (.Ok (initialState contract tx storage observableSlots).sharedState store)
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat slot) =
        0 := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  refine ⟨initialWithStore.setState
    (initialWithStore.toState.sstore (natToUInt256 slot) (natToUInt256 value)),
    ?_, ?_⟩
  · exact primCall_sstore_initialState_wordSlot_ok_withStore fuel contract tx
      storage observableSlots store slot value hSlotRange
  · dsimp [initialWithStore]
    simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      YulState.initial, toSharedState, natToUInt256]
    have hUpdate := account_updateStorage_storage_of_zero
      ({ nonce := (⟨0⟩ : EvmYul.UInt256), balance := (⟨0⟩ : EvmYul.UInt256),
         storage := projectStorage storage observableSlots, code := contract,
         tstorage := Std.TreeMap.empty } : EvmYul.Account .Yul)
      (natToUInt256 slot) (natToUInt256 value) hValueZero
    simp only [Option.option, treeMap_get?_insert_self]
    rw [hUpdate]
    simp [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_erase_self]

/-- Native primitive execution of `sstore(slot, 0)` from an arbitrary local
    store when no observable storage (IRStorageSlot.ofNat slot)s were materialized. -/
theorem primCall_sstore_initialState_wordSlot_withStore_projectResult_slot_zero_emptyObservable
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (store : EvmYul.Yul.VarStore)
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size)
    (hValueZero :
      (natToUInt256 value == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (.Ok (initialState contract tx storage []).sharedState store)
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat slot) =
        0 := by
  exact
    primCall_sstore_initialState_wordSlot_withStore_projectResult_slot_zero_of_erase
      fuel contract tx storage initialEvents [] store slot value hSlotRange
      hValueZero

/-- Native primitive execution of the generated `store(uint256)` core, lifted
    through Verity's projected native result boundary for call success and
    absence of a return word. Storage-slot agreement remains the next setter
    projection obligation, but callers no longer need to inspect the raw
    `calldataload(4); sstore(0, arg0)` result shape for these fields. -/
theorem primCall_calldataload4_then_sstore0_initialState_arg0_projectResult_ok
    (loadFuel storeFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    ∃ finalState,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (loadFuel + 1)
            (initialState contract tx storage observableSlots)
            EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
        match values with
        | [value] =>
            EvmYul.Yul.primCall (storeFuel + 1) state'
              EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).success = true ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).returnValue =
        none := by
  refine ⟨(initialState contract tx storage observableSlots).setState
    ((initialState contract tx storage observableSlots).toState.sstore
      (EvmYul.UInt256.ofNat 0) (natToUInt256 arg)), ?_, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_initialState_arg0_ok
      loadFuel storeFuel contract tx storage observableSlots arg rest hArgs
  · rfl
  · rfl

/-- The native primitive sequence used by the generated SimpleStorage setter
    body after dispatcher selection. -/
def primCall_calldataload4_then_sstore0_stop_initialState_arg0
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    Except EvmYul.Yul.Exception
      (EvmYul.Yul.State × List EvmYul.Literal) := do
  let (state', values) ←
    EvmYul.Yul.primCall (loadFuel + 1)
      (initialState contract tx storage observableSlots)
      EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
  match values with
  | [value] =>
      (do
        let (state'', values') ←
          EvmYul.Yul.primCall (storeFuel + 1) state'
            EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
        match values' with
        | [] =>
            EvmYul.Yul.primCall (stopFuel + 1) state''
              EvmYul.Operation.STOP []
        | _ => .error EvmYul.Yul.Exception.InvalidArguments)
  | _ => .error EvmYul.Yul.Exception.InvalidArguments

/-- Store-parametric form of the native primitive sequence used by the
    generated SimpleStorage setter body. The lowered dispatcher executes the
    selected body after adding switch temporaries to the Yul `VarStore`, while
    calldata and storage effects are carried entirely by the shared state. -/
def primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore) :
    Except EvmYul.Yul.Exception
      (EvmYul.Yul.State × List EvmYul.Literal) := do
  let (state', values) ←
    EvmYul.Yul.primCall (loadFuel + 1)
      (.Ok (initialState contract tx storage observableSlots).sharedState store)
      EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
  match values with
  | [value] =>
      (do
        let (state'', values') ←
          EvmYul.Yul.primCall (storeFuel + 1) state'
            EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
        match values' with
        | [] =>
            EvmYul.Yul.primCall (stopFuel + 1) state''
              EvmYul.Operation.STOP []
        | _ => .error EvmYul.Yul.Exception.InvalidArguments)
  | _ => .error EvmYul.Yul.Exception.InvalidArguments

/-- Exact native primitive execution shape for the generated SimpleStorage setter
    body after dispatcher selection. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_eq
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    let finalState :=
      (initialState contract tx storage observableSlots).setState
        ((initialState contract tx storage observableSlots).toState.sstore
          (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
    primCall_calldataload4_then_sstore0_stop_initialState_arg0
      loadFuel storeFuel stopFuel contract tx storage observableSlots =
      .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
  dsimp
  unfold primCall_calldataload4_then_sstore0_stop_initialState_arg0
  rw [primCall_calldataload4_initialState_arg0_ok loadFuel contract tx
    storage observableSlots arg rest hArgs]
  change
    (do
      let (state'', values') ←
        EvmYul.Yul.primCall (storeFuel + 1)
          (initialState contract tx storage observableSlots)
          EvmYul.Operation.SSTORE
          [EvmYul.UInt256.ofNat 0, natToUInt256 arg]
      match values' with
      | [] =>
          EvmYul.Yul.primCall (stopFuel + 1) state''
            EvmYul.Operation.STOP []
      | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
    .error (EvmYul.Yul.Exception.YulHalt
      ((initialState contract tx storage observableSlots).setState
        ((initialState contract tx storage observableSlots).toState.sstore
          (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))) ⟨0⟩)
  rw [primCall_sstore_initialState_wordSlot_ok storeFuel contract tx storage
    observableSlots 0 arg (by norm_num [EvmYul.UInt256.size])]
  exact primCall_stop_ok stopFuel _

/-- Exact native primitive execution shape for the generated SimpleStorage
    setter body when the selected body starts with an arbitrary Yul
    local-variable store. This removes the empty-store side condition left
    around the dispatcher-selected setter path. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_eq
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    let initialWithStore : EvmYul.Yul.State :=
      .Ok (initialState contract tx storage observableSlots).sharedState store
    let finalState :=
      initialWithStore.setState
        (initialWithStore.toState.sstore
          (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
    primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
      loadFuel storeFuel stopFuel contract tx storage observableSlots store =
      .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
  dsimp
  unfold primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
  rw [primCall_calldataload4_initialState_arg0_ok_withStore loadFuel contract
    tx storage observableSlots store arg rest hArgs]
  change
    (do
      let (state'', values') ←
        EvmYul.Yul.primCall (storeFuel + 1)
          (.Ok (initialState contract tx storage observableSlots).sharedState store)
          EvmYul.Operation.SSTORE
          [EvmYul.UInt256.ofNat 0, natToUInt256 arg]
      match values' with
      | [] =>
          EvmYul.Yul.primCall (stopFuel + 1) state''
            EvmYul.Operation.STOP []
      | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
    .error (EvmYul.Yul.Exception.YulHalt
      ((.Ok (initialState contract tx storage observableSlots).sharedState store :
          EvmYul.Yul.State).setState
        ((.Ok (initialState contract tx storage observableSlots).sharedState store :
            EvmYul.Yul.State).toState.sstore
          (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))) ⟨0⟩)
  rw [primCall_sstore_initialState_wordSlot_ok_withStore storeFuel contract tx
    storage observableSlots store 0 arg (by norm_num [EvmYul.UInt256.size])]
  exact primCall_stop_ok stopFuel _

/-- Native primitive execution of the full generated `store(uint256)` selected
    body from an arbitrary local store, lifted through the terminating `STOP`
    halt and Verity's projected native result boundary for call success and
    absence of a return word. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_ok
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
        loadFuel storeFuel stopFuel contract tx storage observableSlots store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).success =
        true ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        none := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  let finalState :=
    initialWithStore.setState
      (initialWithStore.toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots store arg
      rest hArgs
  · rfl
  · rfl

/-- Exact projected result for the generated `store(uint256)` selected body
    from an arbitrary dispatcher local store. This packages the
    `CALLDATALOAD; SSTORE; STOP` native primitive sequence as one full
    `YulResult` equality, rather than only exposing success and return-value
    field facts. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_eq
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
        loadFuel storeFuel stopFuel contract tx storage observableSlots store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        { success := true
          returnValue := none
          finalStorage := projectStorageFromState tx haltState
          finalMappings :=
            Compiler.Proofs.storageAsMappings (projectStorageFromState tx haltState)
          events := initialEvents ++ projectLogsFromState haltState } := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  let finalState :=
    initialWithStore.setState
      (initialWithStore.toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots store arg
      rest hArgs
  · simp [projectResult]

/-- Exact projected result for the generated `store(uint256)` selected body at
    the IR transaction boundary used by the end-to-end native theorem. This is
    the `YulTransaction.ofIR` specialization of the dispatcher-local
    `CALLDATALOAD; SSTORE; STOP` native primitive sequence. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_ofIR_arg0_withStore_projectResult_eq
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
        loadFuel storeFuel stopFuel contract (YulTransaction.ofIR tx) storage
        observableSlots store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult (YulTransaction.ofIR tx) storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        { success := true
          returnValue := none
          finalStorage := projectStorageFromState (YulTransaction.ofIR tx) haltState
          finalMappings :=
            Compiler.Proofs.storageAsMappings
              (projectStorageFromState (YulTransaction.ofIR tx) haltState)
          events := initialEvents ++ projectLogsFromState haltState } := by
  exact
    primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_eq
      loadFuel storeFuel stopFuel contract (YulTransaction.ofIR tx) storage
      initialEvents observableSlots store arg rest (by simpa using hArgs)

/-- Native primitive execution of the full generated `store(uint256)` selected
    body from an arbitrary local store, lifted through `STOP` and Verity's
    projected native result boundary for a nonzero slot-zero write. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_slot0
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueNonzero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = false) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
        loadFuel storeFuel stopFuel contract tx storage observableSlots store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).finalStorage (IRStorageSlot.ofNat 0) =
        natToUInt256 arg := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  let finalState :=
    initialWithStore.setState
      (initialWithStore.toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots store arg
      rest hArgs
  · dsimp [finalState, initialWithStore]
    simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      YulState.initial, toSharedState]
    have hUpdate := account_updateStorage_storage_of_nonzero
      ({ nonce := (⟨0⟩ : EvmYul.UInt256), balance := (⟨0⟩ : EvmYul.UInt256),
         storage := projectStorage storage observableSlots, code := contract,
         tstorage := Std.TreeMap.empty } : EvmYul.Account .Yul)
      (EvmYul.UInt256.ofNat 0) (natToUInt256 arg) hValueNonzero
    simp only [Option.option, treeMap_get?_insert_self]
    rw [hUpdate]
    simp [treeMap_get?_insert_self]

/-- Zero-write storage projection for the full generated `store(uint256)`
    selected body from an arbitrary local store, through the terminating
    `STOP`, with the remaining RBMap erasure fact isolated. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_slot0_zero_of_erase
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueZero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
        loadFuel storeFuel stopFuel contract tx storage observableSlots store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).finalStorage (IRStorageSlot.ofNat 0) =
        0 := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  let finalState :=
    initialWithStore.setState
      (initialWithStore.toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots store arg
      rest hArgs
  · dsimp [finalState, initialWithStore]
    simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      YulState.initial, toSharedState, natToUInt256]
    have hUpdate := account_updateStorage_storage_of_zero
      ({ nonce := (⟨0⟩ : EvmYul.UInt256), balance := (⟨0⟩ : EvmYul.UInt256),
         storage := projectStorage storage observableSlots, code := contract,
         tstorage := Std.TreeMap.empty } : EvmYul.Account .Yul)
      (EvmYul.UInt256.ofNat 0) (natToUInt256 arg) hValueZero
    simp only [Option.option, treeMap_get?_insert_self]
    rw [hUpdate]
    simp [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_erase_self]

/-- Zero-write storage projection for the full generated `store(uint256)`
    selected body from an arbitrary local store when no observable slots were
    materialized. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_slot0_zero_emptyObservable
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueZero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
        loadFuel storeFuel stopFuel contract tx storage [] store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).finalStorage (IRStorageSlot.ofNat 0) =
        0 := by
  exact
    primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_slot0_zero_of_erase
      loadFuel storeFuel stopFuel contract tx storage initialEvents [] store arg
      rest hArgs hValueZero

/-- Native primitive execution of the full generated `store(uint256)` selected
    body tail: `calldataload(4); sstore(0, arg0); stop`. The terminating
    `STOP` travels through EVMYulLean's Yul-halt channel and projects as a
    successful call with no return word. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_projectResult_ok
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0
        loadFuel storeFuel stopFuel contract tx storage observableSlots =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).success =
        true ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        none := by
  let finalState :=
    (initialState contract tx storage observableSlots).setState
      ((initialState contract tx storage observableSlots).toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots arg rest
      hArgs
  · rfl
  · rfl

/-- Native primitive execution of the full generated `store(uint256)` selected
    body, lifted through the terminating `STOP` halt and Verity's projected
    native result boundary for a nonzero slot-zero write. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_projectResult_slot0
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueNonzero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = false) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0
        loadFuel storeFuel stopFuel contract tx storage observableSlots =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).finalStorage (IRStorageSlot.ofNat 0) =
        natToUInt256 arg := by
  let finalState :=
    (initialState contract tx storage observableSlots).setState
      ((initialState contract tx storage observableSlots).toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots arg rest
      hArgs
  · dsimp [finalState]
    simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      YulState.initial, toSharedState]
    have hUpdate := account_updateStorage_storage_of_nonzero
      ({ nonce := (⟨0⟩ : EvmYul.UInt256), balance := (⟨0⟩ : EvmYul.UInt256),
         storage := projectStorage storage observableSlots, code := contract,
         tstorage := Std.TreeMap.empty } : EvmYul.Account .Yul)
      (EvmYul.UInt256.ofNat 0) (natToUInt256 arg) hValueNonzero
    simp only [Option.option, treeMap_get?_insert_self]
    rw [hUpdate]
    simp [treeMap_get?_insert_self]

/-- Zero-write storage projection for the full generated `store(uint256)` selected
    body through the terminating `STOP`, with the remaining RBMap erasure fact
    isolated at the same boundary as the non-terminating setter-core lemma. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_projectResult_slot0_zero_of_erase
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueZero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0
        loadFuel storeFuel stopFuel contract tx storage observableSlots =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).finalStorage (IRStorageSlot.ofNat 0) =
        0 := by
  let finalState :=
    (initialState contract tx storage observableSlots).setState
      ((initialState contract tx storage observableSlots).toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots arg rest
      hArgs
  · dsimp [finalState]
    simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      YulState.initial, toSharedState, natToUInt256]
    have hUpdate := account_updateStorage_storage_of_zero
      ({ nonce := (⟨0⟩ : EvmYul.UInt256), balance := (⟨0⟩ : EvmYul.UInt256),
         storage := projectStorage storage observableSlots, code := contract,
         tstorage := Std.TreeMap.empty } : EvmYul.Account .Yul)
      (EvmYul.UInt256.ofNat 0) (natToUInt256 arg) hValueZero
    simp only [Option.option, treeMap_get?_insert_self]
    rw [hUpdate]
    simp [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_erase_self]

/-- Zero-write storage projection for the full generated `store(uint256)` selected
    body through `STOP` when no observable slots were materialized. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_projectResult_slot0_zero_emptyObservable
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueZero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0
        loadFuel storeFuel stopFuel contract tx storage [] =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).finalStorage (IRStorageSlot.ofNat 0) =
        0 := by
  exact
    primCall_calldataload4_then_sstore0_stop_initialState_arg0_projectResult_slot0_zero_of_erase
      loadFuel storeFuel stopFuel contract tx storage initialEvents [] arg rest
      hArgs hValueZero

/-- Native primitive execution of the generated `store(uint256)` core, lifted
    through Verity's projected native result boundary for a nonzero slot-zero
    write. The remaining zero-write case goes through `Account.updateStorage`'s
    key-erasure branch and needs the corresponding `RBMap.erase` lookup fact. -/
theorem primCall_calldataload4_then_sstore0_initialState_arg0_projectResult_slot0
    (loadFuel storeFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueNonzero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = false) :
    ∃ finalState,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (loadFuel + 1)
            (initialState contract tx storage observableSlots)
            EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
        match values with
        | [value] =>
            EvmYul.Yul.primCall (storeFuel + 1) state'
              EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat 0) =
        natToUInt256 arg := by
  refine ⟨(initialState contract tx storage observableSlots).setState
    ((initialState contract tx storage observableSlots).toState.sstore
      (EvmYul.UInt256.ofNat 0) (natToUInt256 arg)), ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_initialState_arg0_ok
      loadFuel storeFuel contract tx storage observableSlots arg rest hArgs
  · simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      YulState.initial, toSharedState]
    have hUpdate := account_updateStorage_storage_of_nonzero
      ({ nonce := (⟨0⟩ : EvmYul.UInt256), balance := (⟨0⟩ : EvmYul.UInt256),
         storage := projectStorage storage observableSlots, code := contract,
         tstorage := Std.TreeMap.empty } : EvmYul.Account .Yul)
      (EvmYul.UInt256.ofNat 0) (natToUInt256 arg) hValueNonzero
    simp only [Option.option, treeMap_get?_insert_self]
    rw [hUpdate]
    simp [treeMap_get?_insert_self]

/-- Zero `sstore` projection, with the remaining RBMap erasure fact isolated. -/
theorem primCall_calldataload4_then_sstore0_initialState_arg0_projectResult_slot0_zero_of_erase
    (loadFuel storeFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueZero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ finalState,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (loadFuel + 1)
            (initialState contract tx storage observableSlots)
            EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
        match values with
        | [value] =>
            EvmYul.Yul.primCall (storeFuel + 1) state'
              EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat 0) =
        0 := by
  refine ⟨(initialState contract tx storage observableSlots).setState
    ((initialState contract tx storage observableSlots).toState.sstore
      (EvmYul.UInt256.ofNat 0) (natToUInt256 arg)), ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_initialState_arg0_ok
      loadFuel storeFuel contract tx storage observableSlots arg rest hArgs
  · simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      YulState.initial, toSharedState, natToUInt256]
    have hUpdate := account_updateStorage_storage_of_zero
      ({ nonce := (⟨0⟩ : EvmYul.UInt256), balance := (⟨0⟩ : EvmYul.UInt256),
         storage := projectStorage storage observableSlots, code := contract,
         tstorage := Std.TreeMap.empty } : EvmYul.Account .Yul)
      (EvmYul.UInt256.ofNat 0) (natToUInt256 arg) hValueZero
    simp only [Option.option, treeMap_get?_insert_self]
    rw [hUpdate]
    simp [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_erase_self]

/-- Zero `sstore` projection with empty observable-slot materialization. -/
theorem primCall_calldataload4_then_sstore0_initialState_arg0_projectResult_slot0_zero_emptyObservable
    (loadFuel storeFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueZero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ finalState,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (loadFuel + 1)
            (initialState contract tx storage [])
            EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
        match values with
        | [value] =>
            EvmYul.Yul.primCall (storeFuel + 1) state'
              EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat 0) =
        0 := by
  exact
    primCall_calldataload4_then_sstore0_initialState_arg0_projectResult_slot0_zero_of_erase
      loadFuel storeFuel contract tx storage initialEvents [] arg rest hArgs
      hValueZero

@[simp] theorem projectResult_yulHalt_events
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).events =
      initialEvents ++ projectLogsFromState state := by
  rfl

@[simp] theorem projectResult_yulHalt_success
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).success = true := by
  rfl

@[simp] theorem projectResult_yulHalt_returnValue
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).returnValue =
      projectHaltReturn state value := by
  rfl

/-- The exact native scalar-return primitive proof lifted through Verity's
    projected native result boundary. This is the shape consumed by dispatcher
    agreement: after native `mstore(0, value); return(0, 32)` halts, the
    projected `YulResult.returnValue` is exactly the returned word. -/
theorem primCall_mstore0_then_return32_emptyMemory_projectResult_returnValue
    (mstoreFuel returnFuel : Nat)
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256)
    (hMemory : sharedState.memory = ByteArray.empty) :
    ∃ haltState haltValue,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (mstoreFuel + 1) (.Ok sharedState store)
            EvmYul.Operation.MSTORE
            [EvmYul.UInt256.ofNat 0, value]
        match values with
        | [] =>
            EvmYul.Yul.primCall (returnFuel + 1) state'
              EvmYul.Operation.RETURN
              [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx initialStorage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        some value.toNat := by
  rcases primCall_mstore0_then_return32_emptyMemory_projectHaltReturn
      mstoreFuel returnFuel sharedState store value hMemory with
    ⟨haltState, haltValue, hExec, hReturn⟩
  refine ⟨haltState, haltValue, hExec, ?_⟩
  simpa using hReturn

/-- Exact projected result for the generated scalar-return primitive sequence.
    Starting from empty native memory, `mstore(0, value); return(0, 32)` halts
    through the actual EVMYulLean primitive relation and projects as a successful
    one-word return containing exactly `value`. -/
theorem primCall_mstore0_then_return32_emptyMemory_projectResult_eq
    (mstoreFuel returnFuel : Nat)
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256)
    (hMemory : sharedState.memory = ByteArray.empty) :
    ∃ haltState haltValue,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (mstoreFuel + 1) (.Ok sharedState store)
            EvmYul.Operation.MSTORE
            [EvmYul.UInt256.ofNat 0, value]
        match values with
        | [] =>
            EvmYul.Yul.primCall (returnFuel + 1) state'
              EvmYul.Operation.RETURN
              [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx initialStorage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        { success := true
          returnValue := some value.toNat
          finalStorage := projectStorageFromState tx haltState
          finalMappings :=
            Compiler.Proofs.storageAsMappings (projectStorageFromState tx haltState)
          events := initialEvents ++ projectLogsFromState haltState } := by
  rcases
    primCall_mstore0_then_return32_emptyMemory_projectResult_returnValue
      mstoreFuel returnFuel tx initialStorage initialEvents sharedState store value
      hMemory with
    ⟨haltState, haltValue, hExec, hReturn⟩
  refine ⟨haltState, haltValue, hExec, ?_⟩
  have hProjectReturn :
      projectHaltReturn haltState haltValue = some value.toNat := by
    simpa [projectResult] using hReturn
  simp [projectResult, hProjectReturn]

/-- The native primitive sequence used by the generated SimpleStorage getter
    body after dispatcher selection. -/
def primCall_sload0_then_mstore0_return32_initialState
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    Except EvmYul.Yul.Exception
      (EvmYul.Yul.State × List EvmYul.Literal) := do
  let (state', values) ←
    EvmYul.Yul.primCall (sloadFuel + 1)
      (initialState contract tx storage observableSlots)
      EvmYul.Operation.SLOAD [EvmYul.UInt256.ofNat 0]
  match values with
  | [value] =>
      (do
        let (state'', values') ←
          EvmYul.Yul.primCall (mstoreFuel + 1) state'
            EvmYul.Operation.MSTORE [EvmYul.UInt256.ofNat 0, value]
        match values' with
        | [] =>
            EvmYul.Yul.primCall (returnFuel + 1) state''
              EvmYul.Operation.RETURN
              [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments)
  | _ => .error EvmYul.Yul.Exception.InvalidArguments

/-- Store-parametric form of the native primitive sequence used by the
    generated SimpleStorage getter body. The lowered dispatcher executes the
    selected body after adding switch temporaries to the Yul `VarStore`, while
    storage and memory effects are carried by the shared state. -/
def primCall_sload0_then_mstore0_return32_initialState_withStore
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore) :
    Except EvmYul.Yul.Exception
      (EvmYul.Yul.State × List EvmYul.Literal) := do
  let (state', values) ←
    EvmYul.Yul.primCall (sloadFuel + 1)
      (.Ok (initialState contract tx storage observableSlots).sharedState store)
      EvmYul.Operation.SLOAD [EvmYul.UInt256.ofNat 0]
  match values with
  | [value] =>
      (do
        let (state'', values') ←
          EvmYul.Yul.primCall (mstoreFuel + 1) state'
            EvmYul.Operation.MSTORE [EvmYul.UInt256.ofNat 0, value]
        match values' with
        | [] =>
            EvmYul.Yul.primCall (returnFuel + 1) state''
              EvmYul.Operation.RETURN
              [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments)
  | _ => .error EvmYul.Yul.Exception.InvalidArguments

/-- Native primitive execution of the generated `retrieve()` scalar-return core:
    `sload(0)` reads the materialized slot-zero word, then `mstore(0, value);
    return(0, 32)` returns that exact word through the projected native result.

This composes the real EVMYulLean `SLOAD`, `MSTORE`, and `RETURN` primitive
relations for the SimpleStorage getter body, leaving only dispatcher selection
and oracle comparison around this selected-body path. -/
theorem primCall_sload0_then_mstore0_return32_initialState_projectResult_returnValue
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSlot : 0 ∈ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        some (uint256ToNat (storage 0)) := by
  unfold primCall_sload0_then_mstore0_return32_initialState
  rw [primCall_sload_initialState_observableSlot_ok sloadFuel contract tx storage
    observableSlots 0 hSlot hRange]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 0) = loaded
  cases loaded with
  | mk stateAfterLoad _ =>
      let sharedAfterLoad : EvmYul.SharedState .Yul :=
        { (initialState contract tx storage observableSlots).toSharedState with
          toState := stateAfterLoad }
      have hMemory : sharedAfterLoad.memory = ByteArray.empty := by
        simp [sharedAfterLoad, initialState, EvmYul.Yul.State.toSharedState,
          YulState.initial, toSharedState]
      rcases
        primCall_mstore0_then_return32_emptyMemory_projectResult_returnValue
          mstoreFuel returnFuel tx storage initialEvents sharedAfterLoad ∅
          (storage 0) hMemory with
        ⟨haltState, haltValue, hExec, hReturn⟩
      refine ⟨haltState, haltValue, ?_, ?_⟩
      · have hSlotZero : IRStorageSlot.ofNat 0 = 0 := by rfl
        simpa [sharedAfterLoad, initialState, EvmYul.Yul.State.setSharedState,
          EvmYul.Yul.State.toSharedState, Bind.bind, Except.bind,
          hSlotZero, hload] using hExec
      · simpa only [uint256ToNat, EvmYul.UInt256.toNat] using hReturn

/-- Native primitive execution of the generated `retrieve()` scalar-return core
    when slot zero was not materialized into the finite native storage map:
    `sload(0)` returns the EVM zero word, and the following
    `mstore(0, 0); return(0, 32)` projects as return value `0`. -/
theorem primCall_sload0_then_mstore0_return32_initialState_omittedSlot_projectResult_returnValue
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hNotSlot : 0 ∉ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        some 0 := by
  unfold primCall_sload0_then_mstore0_return32_initialState
  rw [primCall_sload_initialState_omittedSlot_ok sloadFuel contract tx storage
    observableSlots 0 hNotSlot hRange (by norm_num [EvmYul.UInt256.size])]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 0) = loaded
  cases loaded with
  | mk stateAfterLoad _ =>
      let sharedAfterLoad : EvmYul.SharedState .Yul :=
        { (initialState contract tx storage observableSlots).toSharedState with
          toState := stateAfterLoad }
      have hMemory : sharedAfterLoad.memory = ByteArray.empty := by
        simp [sharedAfterLoad, initialState, EvmYul.Yul.State.toSharedState,
          YulState.initial, toSharedState]
      rcases
        primCall_mstore0_then_return32_emptyMemory_projectResult_returnValue
          mstoreFuel returnFuel tx storage initialEvents sharedAfterLoad ∅
          (natToUInt256 0) hMemory with
        ⟨haltState, haltValue, hExec, hReturn⟩
      refine ⟨haltState, haltValue, ?_, ?_⟩
      · simpa [sharedAfterLoad, initialState, EvmYul.Yul.State.setSharedState,
          EvmYul.Yul.State.toSharedState, Bind.bind, Except.bind,
          IRStorageSlot.ofNat, hload] using hExec
      · have hZero : (natToUInt256 0).toNat = 0 := rfl; rwa [hZero] at hReturn

/-- Native primitive execution of the generated `retrieve()` scalar-return core,
    with the slot-zero materialization split discharged internally.

If slot zero was materialized as observable native storage, the getter returns
    the projected Verity storage word. If it was omitted from materialization,
    EVMYulLean's `SLOAD` default-zero behavior is exposed as return value zero.
    This theorem removes the caller-side `0 ∈ observableSlots`/`0 ∉
    observableSlots` premise split from the selected-body dispatcher proof. -/
theorem primCall_sload0_then_mstore0_return32_initialState_projectResult_returnValue_materialized
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        if 0 ∈ observableSlots then
          some (uint256ToNat (storage 0))
        else
          some 0 := by
  by_cases hSlot : 0 ∈ observableSlots
  · rcases
      primCall_sload0_then_mstore0_return32_initialState_projectResult_returnValue
        sloadFuel mstoreFuel returnFuel contract tx storage initialEvents
        observableSlots hSlot hRange with
      ⟨haltState, haltValue, hExec, hReturn⟩
    refine ⟨haltState, haltValue, hExec, ?_⟩
    rw [if_pos hSlot]
    simpa using hReturn
  · rcases
      primCall_sload0_then_mstore0_return32_initialState_omittedSlot_projectResult_returnValue
        sloadFuel mstoreFuel returnFuel contract tx storage initialEvents
        observableSlots hSlot hRange with
      ⟨haltState, haltValue, hExec, hReturn⟩
    refine ⟨haltState, haltValue, hExec, ?_⟩
    rw [if_neg hSlot]
    simpa using hReturn

/-- Native primitive execution of the generated `retrieve()` scalar-return core
    from an arbitrary local store when slot zero is materialized. -/
theorem primCall_sload0_then_mstore0_return32_initialState_withStore_projectResult_returnValue
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (hSlot : 0 ∈ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState_withStore
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots
        store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        some (uint256ToNat (storage 0)) := by
  unfold primCall_sload0_then_mstore0_return32_initialState_withStore
  rw [primCall_sload_initialState_observableSlot_ok_withStore sloadFuel
    contract tx storage observableSlots store 0 hSlot hRange]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 0) = loaded
  cases loaded with
  | mk stateAfterLoad _ =>
      let initialWithStore : EvmYul.Yul.State :=
        .Ok (initialState contract tx storage observableSlots).sharedState store
      let sharedAfterLoad : EvmYul.SharedState .Yul :=
        { initialWithStore.toSharedState with toState := stateAfterLoad }
      have hMemory : sharedAfterLoad.memory = ByteArray.empty := by
        change initialWithStore.toSharedState.memory = ByteArray.empty
        simp [initialWithStore, initialState, EvmYul.Yul.State.toSharedState,
          EvmYul.Yul.State.sharedState, YulState.initial, toSharedState]
      rcases
        primCall_mstore0_then_return32_emptyMemory_projectResult_returnValue
          mstoreFuel returnFuel tx storage initialEvents sharedAfterLoad store
          (storage 0) hMemory with
        ⟨haltState, haltValue, hExec, hReturn⟩
      refine ⟨haltState, haltValue, ?_, ?_⟩
      · have hSlotZero : IRStorageSlot.ofNat 0 = 0 := by rfl
        simpa [sharedAfterLoad, initialWithStore, initialState,
          EvmYul.Yul.State.setSharedState, EvmYul.Yul.State.toSharedState,
          Bind.bind, Except.bind, hSlotZero, hload] using hExec
      · simpa only [uint256ToNat, EvmYul.UInt256.toNat] using hReturn

/-- Native primitive execution of the generated `retrieve()` scalar-return core
    from an arbitrary local store when slot zero is omitted. -/
theorem primCall_sload0_then_mstore0_return32_initialState_withStore_omittedSlot_projectResult_returnValue
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (hNotSlot : 0 ∉ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState_withStore
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots
        store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        some 0 := by
  unfold primCall_sload0_then_mstore0_return32_initialState_withStore
  rw [primCall_sload_initialState_omittedSlot_ok_withStore sloadFuel
    contract tx storage observableSlots store 0 hNotSlot hRange
    (by norm_num [EvmYul.UInt256.size])]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 0) = loaded
  cases loaded with
  | mk stateAfterLoad _ =>
      let initialWithStore : EvmYul.Yul.State :=
        .Ok (initialState contract tx storage observableSlots).sharedState store
      let sharedAfterLoad : EvmYul.SharedState .Yul :=
        { initialWithStore.toSharedState with toState := stateAfterLoad }
      have hMemory : sharedAfterLoad.memory = ByteArray.empty := by
        change initialWithStore.toSharedState.memory = ByteArray.empty
        simp [initialWithStore, initialState, EvmYul.Yul.State.toSharedState,
          EvmYul.Yul.State.sharedState, YulState.initial, toSharedState]
      rcases
        primCall_mstore0_then_return32_emptyMemory_projectResult_returnValue
          mstoreFuel returnFuel tx storage initialEvents sharedAfterLoad store
          (natToUInt256 0) hMemory with
        ⟨haltState, haltValue, hExec, hReturn⟩
      refine ⟨haltState, haltValue, ?_, ?_⟩
      · simpa [sharedAfterLoad, initialWithStore, initialState,
          EvmYul.Yul.State.setSharedState, EvmYul.Yul.State.toSharedState,
          Bind.bind, Except.bind, IRStorageSlot.ofNat, hload] using hExec
      · have hZero : (natToUInt256 0).toNat = 0 := rfl; rwa [hZero] at hReturn

/-- Native primitive execution of the generated `retrieve()` scalar-return core
    from an arbitrary local store, with materialized/omitted slot zero handled
    internally. -/
theorem primCall_sload0_then_mstore0_return32_initialState_withStore_projectResult_returnValue_materialized
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState_withStore
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots
        store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        if 0 ∈ observableSlots then
          some (uint256ToNat (storage 0))
        else
          some 0 := by
  by_cases hSlot : 0 ∈ observableSlots
  · rcases
      primCall_sload0_then_mstore0_return32_initialState_withStore_projectResult_returnValue
        sloadFuel mstoreFuel returnFuel contract tx storage initialEvents
        observableSlots store hSlot hRange with
      ⟨haltState, haltValue, hExec, hReturn⟩
    refine ⟨haltState, haltValue, hExec, ?_⟩
    rw [if_pos hSlot]
    simpa using hReturn
  · rcases
      primCall_sload0_then_mstore0_return32_initialState_withStore_omittedSlot_projectResult_returnValue
        sloadFuel mstoreFuel returnFuel contract tx storage initialEvents
        observableSlots store hSlot hRange with
      ⟨haltState, haltValue, hExec, hReturn⟩
    refine ⟨haltState, haltValue, hExec, ?_⟩
    rw [if_neg hSlot]
    simpa using hReturn

/-- Exact projected result for the generated `retrieve()` scalar-return core
    from an arbitrary dispatcher local store. This strengthens
    `primCall_sload0_then_mstore0_return32_initialState_withStore_projectResult_returnValue_materialized`
    from a return-value field fact to the full `YulResult` shape produced by the
    native `SLOAD; MSTORE; RETURN` halt. -/
theorem primCall_sload0_then_mstore0_return32_initialState_withStore_projectResult_eq_materialized
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState_withStore
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots
        store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        { success := true
          returnValue :=
            if 0 ∈ observableSlots then
              some (uint256ToNat (storage 0))
            else
              some 0
          finalStorage := projectStorageFromState tx haltState
          finalMappings :=
            Compiler.Proofs.storageAsMappings (projectStorageFromState tx haltState)
          events := initialEvents ++ projectLogsFromState haltState } := by
  rcases
    primCall_sload0_then_mstore0_return32_initialState_withStore_projectResult_returnValue_materialized
      sloadFuel mstoreFuel returnFuel contract tx storage initialEvents
      observableSlots store hRange with
    ⟨haltState, haltValue, hExec, hReturn⟩
  refine ⟨haltState, haltValue, hExec, ?_⟩
  have hProjectReturn :
      projectHaltReturn haltState haltValue =
        if 0 ∈ observableSlots then
          some (uint256ToNat (storage 0))
        else
          some 0 := by
    simpa [projectResult] using hReturn
  simp [projectResult, hProjectReturn]

@[simp] theorem projectResult_yulHalt_finalMappings
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).finalMappings =
      Compiler.Proofs.storageAsMappings (projectStorageFromState tx state) := by
  rfl

@[simp] theorem projectResult_yulHalt_finalStorageSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (account : EvmYul.Account .Yul)
    (slotValue : EvmYul.UInt256)
    (hAccount :
      state.sharedState.accountMap.get? (natToAddress tx.thisAddress) =
        some account)
    (hSlot : account.storage.get? (natToUInt256 slot) = some slotValue) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).finalStorage (IRStorageSlot.ofNat slot) =
        slotValue := by
  change projectStorageFromState tx state (IRStorageSlot.ofNat slot) = slotValue
  exact projectStorageFromState_accountStorageSlot tx state slot account slotValue hAccount hSlot

@[simp] theorem projectResult_yulHalt_missingFinalStorageAccountSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (hAccount :
      state.sharedState.accountMap.get? (natToAddress tx.thisAddress) =
        none) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).finalStorage (IRStorageSlot.ofNat slot) = 0 := by
  change projectStorageFromState tx state (IRStorageSlot.ofNat slot) = 0
  exact projectStorageFromState_missingAccount tx state slot hAccount

@[simp] theorem projectResult_yulHalt_missingFinalStorageSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (account : EvmYul.Account .Yul)
    (hAccount :
      state.sharedState.accountMap.get? (natToAddress tx.thisAddress) =
        some account)
    (hSlot : account.storage.get? (natToUInt256 slot) = none) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).finalStorage (IRStorageSlot.ofNat slot) = 0 := by
  change projectStorageFromState tx state (IRStorageSlot.ofNat slot) = 0
  exact projectStorageFromState_missingAccountStorageSlot tx state slot account hAccount hSlot

@[simp] theorem projectResult_stop
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State) :
    projectResult tx initialStorage initialEvents
      (.error (.YulHalt state ⟨0⟩)) =
    { success := true
      returnValue := none
      finalStorage := projectStorageFromState tx state
      finalMappings :=
        Compiler.Proofs.storageAsMappings (projectStorageFromState tx state)
      events := initialEvents ++ projectLogsFromState state } := by
  simp [projectResult]

@[simp] theorem projectResult_32ByteReturn
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal)
    (hHalt : value ≠ ⟨0⟩)
    (hSize : state.sharedState.H_return.size = 32) :
    projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value)) =
    { success := true
      returnValue := some (byteArrayWord state.sharedState.H_return 0)
      finalStorage := projectStorageFromState tx state
      finalMappings :=
        Compiler.Proofs.storageAsMappings (projectStorageFromState tx state)
      events := initialEvents ++ projectLogsFromState state } := by
  simp [projectResult, hHalt, hSize]

@[simp] theorem projectResult_non32ByteReturn
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal)
    (hHalt : value ≠ ⟨0⟩)
    (hSize : state.sharedState.H_return.size ≠ 32) :
    projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value)) =
    { success := true
      returnValue := some 0
      finalStorage := projectStorageFromState tx state
      finalMappings :=
        Compiler.Proofs.storageAsMappings (projectStorageFromState tx state)
      events := initialEvents ++ projectLogsFromState state } := by
  simp [projectResult, hHalt, hSize]

@[simp] theorem projectResult_revert
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) :
    projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert) =
    { success := false
      returnValue := none
      finalStorage := initialStorage
      finalMappings := Compiler.Proofs.storageAsMappings initialStorage
      events := initialEvents } := by
  rfl

@[simp] theorem projectResult_revert_events
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).events =
      initialEvents := by
  rfl

@[simp] theorem projectResult_revert_success
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).success = false := by
  rfl

@[simp] theorem projectResult_revert_returnValue
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).returnValue = none := by
  rfl

@[simp] theorem projectResult_revert_finalMappings
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).finalMappings =
      Compiler.Proofs.storageAsMappings initialStorage := by
  rfl

@[simp] theorem projectResult_revert_finalStorageSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (slot : Nat) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).finalStorage (IRStorageSlot.ofNat slot) =
      initialStorage (IRStorageSlot.ofNat slot) := by
  rfl

@[simp] theorem projectResult_hardError
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (err : EvmYul.Yul.Exception)
    (hNotHalt : ∀ state value, err ≠ EvmYul.Yul.Exception.YulHalt state value) :
    projectResult tx initialStorage initialEvents (.error err) =
    { success := false
      returnValue := none
      finalStorage := initialStorage
      finalMappings := Compiler.Proofs.storageAsMappings initialStorage
      events := initialEvents } := by
  cases err with
  | YulHalt state value =>
      exact False.elim (hNotHalt state value rfl)
  | InvalidArguments => rfl
  | NotEncodableRLP => rfl
  | InvalidInstruction => rfl
  | OutOfFuel => rfl
  | StaticModeViolation => rfl
  | MissingContract s => rfl
  | MissingContractFunction s => rfl
  | InvalidExpression => rfl
  | YulEXTCODESIZENotImplemented => rfl
  | Revert => rfl

@[simp] theorem projectResult_hardError_success
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (err : EvmYul.Yul.Exception)
    (hNotHalt : ∀ state value, err ≠ EvmYul.Yul.Exception.YulHalt state value) :
    (projectResult tx initialStorage initialEvents (.error err)).success = false := by
  cases err with
  | YulHalt state value =>
      exact False.elim (hNotHalt state value rfl)
  | InvalidArguments => rfl
  | NotEncodableRLP => rfl
  | InvalidInstruction => rfl
  | OutOfFuel => rfl
  | StaticModeViolation => rfl
  | MissingContract s => rfl
  | MissingContractFunction s => rfl
  | InvalidExpression => rfl
  | YulEXTCODESIZENotImplemented => rfl
  | Revert => rfl

@[simp] theorem projectResult_hardError_returnValue
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (err : EvmYul.Yul.Exception)
    (hNotHalt : ∀ state value, err ≠ EvmYul.Yul.Exception.YulHalt state value) :
    (projectResult tx initialStorage initialEvents (.error err)).returnValue = none := by
  cases err with
  | YulHalt state value =>
      exact False.elim (hNotHalt state value rfl)
  | InvalidArguments => rfl
  | NotEncodableRLP => rfl
  | InvalidInstruction => rfl
  | OutOfFuel => rfl
  | StaticModeViolation => rfl
  | MissingContract s => rfl
  | MissingContractFunction s => rfl
  | InvalidExpression => rfl
  | YulEXTCODESIZENotImplemented => rfl
  | Revert => rfl

@[simp] theorem projectResult_hardError_finalStorageSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (err : EvmYul.Yul.Exception)
    (slot : Nat)
    (hNotHalt : ∀ state value, err ≠ EvmYul.Yul.Exception.YulHalt state value) :
    (projectResult tx initialStorage initialEvents (.error err)).finalStorage (IRStorageSlot.ofNat slot) =
      initialStorage (IRStorageSlot.ofNat slot) := by
  cases err with
  | YulHalt state value =>
      exact False.elim (hNotHalt state value rfl)
  | InvalidArguments => rfl
  | NotEncodableRLP => rfl
  | InvalidInstruction => rfl
  | OutOfFuel => rfl
  | StaticModeViolation => rfl
  | MissingContract s => rfl
  | MissingContractFunction s => rfl
  | InvalidExpression => rfl
  | YulEXTCODESIZENotImplemented => rfl
  | Revert => rfl

@[simp] theorem projectResult_hardError_finalMappings
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (err : EvmYul.Yul.Exception)
    (hNotHalt : ∀ state value, err ≠ EvmYul.Yul.Exception.YulHalt state value) :
    (projectResult tx initialStorage initialEvents (.error err)).finalMappings =
      Compiler.Proofs.storageAsMappings initialStorage := by
  cases err with
  | YulHalt state value =>
      exact False.elim (hNotHalt state value rfl)
  | InvalidArguments => rfl
  | NotEncodableRLP => rfl
  | InvalidInstruction => rfl
  | OutOfFuel => rfl
  | StaticModeViolation => rfl
  | MissingContract s => rfl
  | MissingContractFunction s => rfl
  | InvalidExpression => rfl
  | YulEXTCODESIZENotImplemented => rfl
  | Revert => rfl

@[simp] theorem projectResult_hardError_events
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (err : EvmYul.Yul.Exception)
    (hNotHalt : ∀ state value, err ≠ EvmYul.Yul.Exception.YulHalt state value) :
    (projectResult tx initialStorage initialEvents (.error err)).events =
      initialEvents := by
  cases err with
  | YulHalt state value =>
      exact False.elim (hNotHalt state value rfl)
  | InvalidArguments => rfl
  | NotEncodableRLP => rfl
  | InvalidInstruction => rfl
  | OutOfFuel => rfl
  | StaticModeViolation => rfl
  | MissingContract s => rfl
  | MissingContractFunction s => rfl
  | InvalidExpression => rfl
  | YulEXTCODESIZENotImplemented => rfl
  | Revert => rfl

/-- Guarded selector-hit execution for a fully lowered native switch block,
    with the projected selected-body error result exposed at the same switch
    boundary.

Callers prove the selected body reaches the native error or halt and packages
its `projectResult`; this lemma lifts both facts through the generated
selector-switch wrapper. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (nativeYul : YulResult)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        (nativeSwitchMarkedPrefixStateForId contract tx storage
          observableSlots switchId) = .error err)
    (hProject : projectResult tx storage initialEvents (.error err) = nativeYul) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error err ∧
    projectResult tx storage initialEvents (.error err) = nativeYul := by
  refine ⟨?_, hProject⟩
  exact exec_lowerNativeSwitchBlock_selector_find_hit_error_fuel
    fuel selector switchId cases defaultBody tag body contract tx storage
    observableSlots err hSelector hFind hSelectorRange hTagsRange
    (by
      intro pre suffix hCases
      simpa [nativeSwitchMarkedPrefixStateForId, nativeSwitchPrefixStateForId]
        using hBody pre suffix hCases)

/-- Store-parametric selector-hit projection for lowered native switches.

This is the projection form used when a generated dispatcher has already
installed additional local bindings before entering the selector switch. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_error_store_projectResult_eq
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (nativeYul : YulResult)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId store) = .error err)
    (hProject : projectResult tx storage initialEvents (.error err) = nativeYul) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState store) =
      .error err ∧
    projectResult tx storage initialEvents (.error err) = nativeYul := by
  refine ⟨?_, hProject⟩
  exact exec_lowerNativeSwitchBlock_selector_find_hit_error_store_fuel
    fuel selector switchId tag cases defaultBody body contract tx storage
    observableSlots store err hSelector hFind hSelectorRange hTagsRange
    (by
      intro pre suffix hCases
      simpa [initialState, nativeSwitchStoreInitialState,
        nativeSwitchStorePrefixStateForId,
        nativeSwitchStoreMarkedPrefixStateForId]
        using hBody pre suffix hCases)

/-- Store-parametric selector-hit projection after the generated
    `initFreeMemoryPointer` statement has executed. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_error_postInitFreeMemory_store_projectResult_eq
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (nativeYul : YulResult)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        ((((nativeSwitchPostInitFreeMemoryState contract tx storage
                observableSlots store).insert
              (Backends.nativeSwitchDiscrTempName switchId)
              (EvmYul.UInt256.ofNat
                (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 0)).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1)) = .error err)
    (hProject : projectResult tx storage initialEvents (.error err) = nativeYul) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
        (some contract)
        (nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
          store) =
      .error err ∧
    projectResult tx storage initialEvents (.error err) = nativeYul := by
  refine ⟨?_, hProject⟩
  exact exec_lowerNativeSwitchBlock_selector_find_hit_error_postInitFreeMemory_store_fuel
    fuel selector switchId tag cases defaultBody body contract tx storage
    observableSlots store err hSelector hFind hSelectorRange hTagsRange hBody

/-- Store-parametric selector-hit projection for a payable generated case body,
    with the generated comment and calldata-size guard discharged before the
    selected user body premise. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_error_store_projectResult_eq_payable_generated_prefix
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (nativeYul : YulResult)
    (reservedNames : List String) (n0 next : Nat)
    (fn : IRFunction)
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (body, next))
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) ∧
      ((∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots switchId store) =
            .error err) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error err) = nativeYul →
        EvmYul.Yul.exec (fuel + cases.length + 16)
            (Backends.lowerNativeSwitchBlock
              Compiler.Proofs.YulGeneration.selectorExpr switchId cases
              defaultBody)
            (some contract)
            (.Ok
              (initialState contract (YulTransaction.ofIR tx) storage
                observableSlots).sharedState store) =
          .error err ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error err) = nativeYul) := by
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_eq
      reservedNames n0 fn body next hPayable hLower with
    ⟨guardBody, bodyNative, bodyStart, hBodyShape, hBodyLower⟩
  refine ⟨bodyNative, bodyStart, hBodyLower, ?_⟩
  intro hBodyNative hProject
  have hExec :=
    exec_lowerNativeSwitchBlock_selector_find_hit_error_store_projectResult_eq
      (fuel + 4) selector switchId tag cases defaultBody body contract
      (YulTransaction.ofIR tx) storage initialEvents observableSlots store err
      nativeYul hSelector hFind hSelectorRange hTagsRange
      (by
        intro pre suffix hCases
        rw [hBodyShape]
        have hPrefix := exec_switchCaseBody_payable_prefix_eq
          (fuel + suffix.length + 1) guardBody bodyNative contract
          (YulTransaction.ofIR tx) storage observableSlots switchId store
          (4 + fn.params.length * 32)
          (by simpa [YulTransaction.ofIR_args] using hNoWrap)
          (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
          (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hPrefix.trans (hBodyNative pre suffix hCases))
      hProject
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hExec

/-- Store-parametric selector-hit projection for a non-payable generated case
    body, with the generated comment, callvalue guard, and calldata-size guard
    discharged before the selected user body premise. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_error_store_projectResult_eq_nonpayable_generated_prefix
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (nativeYul : YulResult)
    (reservedNames : List String) (n0 next : Nat)
    (fn : IRFunction)
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (body, next))
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) ∧
      ((∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots switchId store) =
            .error err) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error err) = nativeYul →
        EvmYul.Yul.exec (fuel + cases.length + 17)
            (Backends.lowerNativeSwitchBlock
              Compiler.Proofs.YulGeneration.selectorExpr switchId cases
              defaultBody)
            (some contract)
            (.Ok
              (initialState contract (YulTransaction.ofIR tx) storage
                observableSlots).sharedState store) =
          .error err ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error err) = nativeYul) := by
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_eq
      reservedNames n0 fn body next hNonPayable hLower with
    ⟨callvalueGuardBody, calldataGuardBody, bodyNative, bodyStart,
      hBodyShape, hBodyLower⟩
  refine ⟨bodyNative, bodyStart, hBodyLower, ?_⟩
  intro hBodyNative hProject
  have hExec :=
    exec_lowerNativeSwitchBlock_selector_find_hit_error_store_projectResult_eq
      (fuel + 5) selector switchId tag cases defaultBody body contract
      (YulTransaction.ofIR tx) storage initialEvents observableSlots store err
      nativeYul hSelector hFind hSelectorRange hTagsRange
      (by
        intro pre suffix hCases
        rw [hBodyShape]
        have hPrefix := exec_switchCaseBody_nonpayable_prefix_eq
          (fuel + suffix.length + 1) callvalueGuardBody calldataGuardBody
          bodyNative contract (YulTransaction.ofIR tx) storage observableSlots
          switchId store (4 + fn.params.length * 32)
          (DispatchGuardsSafe_msgValue_zero_mod_of_nonpayable fn tx hguards
            hNonPayable)
          (by simpa [YulTransaction.ofIR_args] using hNoWrap)
          (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
          (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hPrefix.trans (hBodyNative pre suffix hCases))
      hProject
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hExec

/-- Store-parametric selector-hit success projection for a payable generated
    case body. The generated prefix is discharged before the lowered user body,
    and matched preservation is required only for that user body. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_ok_store_projectResult_eq_payable_generated_prefix
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (final : EvmYul.Yul.State)
    (nativeYul : YulResult)
    (reservedNames : List String) (n0 next : Nat)
    (fn : IRFunction)
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (body, next))
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) ∧
      ((∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots switchId store) =
            .ok final) →
        (∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
          NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul →
        EvmYul.Yul.exec (fuel + cases.length + 16)
            (Backends.lowerNativeSwitchBlock
              Compiler.Proofs.YulGeneration.selectorExpr switchId cases
              defaultBody)
            (some contract)
            (.Ok
              (initialState contract (YulTransaction.ofIR tx) storage
                observableSlots).sharedState store) =
          .ok final ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul) := by
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_eq
      reservedNames n0 fn body next hPayable hLower with
    ⟨guardBody, bodyNative, bodyStart, hBodyShape, hBodyLower⟩
  refine ⟨bodyNative, bodyStart, hBodyLower, ?_⟩
  intro hBodyNative hPreservesNative hProject
  have hExec :=
    exec_lowerNativeSwitchBlock_selector_find_hit_finalMatched_store_fuel
      (fuel + 4) selector switchId tag cases defaultBody body contract
      (YulTransaction.ofIR tx) storage observableSlots store final hSelector
      hFind hSelectorRange hTagsRange
      (by
        intro pre suffix hCases
        rw [hBodyShape]
        have hPrefix := exec_switchCaseBody_payable_prefix_eq
          (fuel + suffix.length + 1) guardBody bodyNative contract
          (YulTransaction.ofIR tx) storage observableSlots switchId store
          (4 + fn.params.length * 32)
          (by simpa [YulTransaction.ofIR_args] using hNoWrap)
          (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
          (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hPrefix.trans (hBodyNative pre suffix hCases))
      (by
        intro matchedName hMatchedName
        subst matchedName
        rcases nativeSwitch_find_hit_split selector cases tag body hFind with
          ⟨pre, suffix, hCases, _hTag, _hPrefix⟩
        exact hPreservesNative pre suffix hCases
          (fuel + suffix.length + 10)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots switchId store)
          final
          (nativeSwitchStoreMarkedPrefixStateForId_matched contract
            (YulTransaction.ofIR tx) storage observableSlots switchId store
            (Backends.nativeSwitchMatchedTempName switchId) rfl)
          (hBodyNative pre suffix hCases))
  exact ⟨by
    simpa [nativeSwitchStoreInitialState, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hExec, hProject⟩

/-- Store-parametric selector-hit success projection for a non-payable
    generated case body. The generated prefix is discharged before the lowered
    user body, and matched preservation is required only for that user body. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_ok_store_projectResult_eq_nonpayable_generated_prefix
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (final : EvmYul.Yul.State)
    (nativeYul : YulResult)
    (reservedNames : List String) (n0 next : Nat)
    (fn : IRFunction)
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (body, next))
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) ∧
      ((∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots switchId store) =
            .ok final) →
        (∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
          NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul →
        EvmYul.Yul.exec (fuel + cases.length + 17)
            (Backends.lowerNativeSwitchBlock
              Compiler.Proofs.YulGeneration.selectorExpr switchId cases
              defaultBody)
            (some contract)
            (.Ok
              (initialState contract (YulTransaction.ofIR tx) storage
                observableSlots).sharedState store) =
          .ok final ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul) := by
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_eq
      reservedNames n0 fn body next hNonPayable hLower with
    ⟨callvalueGuardBody, calldataGuardBody, bodyNative, bodyStart,
      hBodyShape, hBodyLower⟩
  refine ⟨bodyNative, bodyStart, hBodyLower, ?_⟩
  intro hBodyNative hPreservesNative hProject
  have hExec :=
    exec_lowerNativeSwitchBlock_selector_find_hit_finalMatched_store_fuel
      (fuel + 5) selector switchId tag cases defaultBody body contract
      (YulTransaction.ofIR tx) storage observableSlots store final hSelector
      hFind hSelectorRange hTagsRange
      (by
        intro pre suffix hCases
        rw [hBodyShape]
        have hPrefix := exec_switchCaseBody_nonpayable_prefix_eq
          (fuel + suffix.length + 1) callvalueGuardBody calldataGuardBody
          bodyNative contract (YulTransaction.ofIR tx) storage observableSlots
          switchId store (4 + fn.params.length * 32)
          (DispatchGuardsSafe_msgValue_zero_mod_of_nonpayable fn tx hguards
            hNonPayable)
          (by simpa [YulTransaction.ofIR_args] using hNoWrap)
          (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
          (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hPrefix.trans (hBodyNative pre suffix hCases))
      (by
        intro matchedName hMatchedName
        subst matchedName
        rcases nativeSwitch_find_hit_split selector cases tag body hFind with
          ⟨pre, suffix, hCases, _hTag, _hPrefix⟩
        exact hPreservesNative pre suffix hCases
          (fuel + suffix.length + 10)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots switchId store)
          final
          (nativeSwitchStoreMarkedPrefixStateForId_matched contract
            (YulTransaction.ofIR tx) storage observableSlots switchId store
            (Backends.nativeSwitchMatchedTempName switchId) rfl)
          (hBodyNative pre suffix hCases))
  exact ⟨by
    simpa [nativeSwitchStoreInitialState, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hExec, hProject⟩

/-- Store-parametric selector-miss projection for lowered native switches.

This is the miss-case companion to
`exec_lowerNativeSwitchBlock_selector_find_hit_error_store_projectResult_eq`,
used when earlier dispatcher-local bindings are present before the selector
switch falls through to `revert(0, 0)`. -/
theorem exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_projectResult_eq
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr switchId cases
            [nativeRevertZeroZeroStmt])
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState store) =
      .error EvmYul.Yul.Exception.Revert ∧
    projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert) =
      { success := false
        returnValue := none
        finalStorage := storage
        finalMappings := Compiler.Proofs.storageAsMappings storage
        events := initialEvents } := by
  refine ⟨?_, by simp⟩
  exact exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_fuel
    fuel selector switchId cases contract tx storage observableSlots store
    hSelector hFind hSelectorRange hTagsRange

/-- Bridge-shape selector-miss projection on the post-`__has_selector := 1`
    state. This packages both the block-level native `Revert` endpoint and
    the exact projected rollback result. -/
theorem exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_projectResult_eq
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases
        [nativeRevertZeroZeroStmt]])
      (some contract)
      ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1)) =
      .error EvmYul.Yul.Exception.Revert ∧
    projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert) =
      { success := false
        returnValue := none
        finalStorage := storage
        finalMappings := Compiler.Proofs.storageAsMappings storage
        events := initialEvents } := by
  rcases
    exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_projectResult_eq
      fuel selector switchId cases contract tx storage initialEvents
      observableSlots nativeSwitchHasSelectorStore hSelector hFind
      hSelectorRange hTagsRange with
    ⟨hEndpoint, hProject⟩
  have hFuelEq : fuel + cases.length + 13 = (fuel + cases.length + 12).succ := by
    omega
  rw [nativeSwitchInitialOkState_insert_hasSelector_eq, hFuelEq]
  refine ⟨?_, hProject⟩
  exact exec_block_cons_error (fuel + cases.length + 12) _ [] _ _
    EvmYul.Yul.Exception.Revert hEndpoint

/-- Post-generated-init selector-miss projection on the
    `__has_selector := 1` state. This is the init-prefixed counterpart of
    `exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_projectResult_eq`. -/
theorem exec_block_lowerNativeSwitchBlock_revert_default_postInitFreeMemory_hasSelectorState_projectResult_eq
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases
        [nativeRevertZeroZeroStmt]])
      (some contract)
      ((nativeSwitchPostInitFreeMemoryState contract tx storage
          observableSlots ∅).insert "__has_selector" (EvmYul.UInt256.ofNat 1)) =
      .error EvmYul.Yul.Exception.Revert ∧
    projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert) =
      { success := false
        returnValue := none
        finalStorage := storage
        finalMappings := Compiler.Proofs.storageAsMappings storage
        events := initialEvents } := by
  let store :=
    (∅ : EvmYul.Yul.VarStore).insert "__has_selector"
      (EvmYul.UInt256.ofNat 1)
  have hTail :
      EvmYul.Yul.exec (fuel + cases.length + 10)
        (.Block (nativeSwitchTailStmts switchId cases [nativeRevertZeroZeroStmt]))
        (some contract)
        (((nativeSwitchPostInitFreeMemoryState contract tx storage
              observableSlots store).insert
              (Backends.nativeSwitchDiscrTempName switchId)
              (EvmYul.UInt256.ofNat
                (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 0)) =
        .error EvmYul.Yul.Exception.Revert := by
    let discrName := Backends.nativeSwitchDiscrTempName switchId
    let matchedName := Backends.nativeSwitchMatchedTempName switchId
    let prefixState : EvmYul.Yul.State :=
      (((nativeSwitchPostInitFreeMemoryState contract tx storage
            observableSlots store).insert discrName
            (EvmYul.UInt256.ofNat
              (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
          matchedName (EvmYul.UInt256.ofNat 0))
    have hne := nativeSwitchDiscrTempName_ne_matchedTempName switchId
    have hCases :=
      exec_nativeSwitchCaseIfs_find_none_with_revert_default_fuel
        (fuel + 1) selector cases (some contract) prefixState discrName
        matchedName hFind
        (by
          simpa [prefixState, discrName, matchedName,
            nativeSwitchPostInitFreeMemoryState, EvmYul.Yul.State.insert]
            using
              state_getElem_insert_self_ok
                (nativeSwitchPostInitFreeMemorySharedState contract tx storage
                  observableSlots)
                ((store.insert discrName
                  (EvmYul.UInt256.ofNat
                    (tx.functionSelector % Compiler.Constants.selectorModulus))))
                matchedName (EvmYul.UInt256.ofNat 0))
        (by
          have hDiscr :=
            state_getElem_insert_self_ok
              (nativeSwitchPostInitFreeMemorySharedState contract tx storage
                observableSlots)
              store discrName
              (EvmYul.UInt256.ofNat
                (tx.functionSelector % Compiler.Constants.selectorModulus))
          have hLookup :=
            state_getElem_insert_of_ne
              ((nativeSwitchPostInitFreeMemoryState contract tx storage
                observableSlots store).insert discrName
                (EvmYul.UInt256.ofNat
                  (tx.functionSelector % Compiler.Constants.selectorModulus)))
              discrName matchedName (EvmYul.UInt256.ofNat 0) hne
          rw [hLookup]
          simpa [nativeSwitchPostInitFreeMemoryState, hSelector] using hDiscr)
        hSelectorRange hTagsRange
    simpa [nativeSwitchTailStmts, discrName, matchedName, prefixState,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCases
  have hEndpoint :
      EvmYul.Yul.exec (fuel + cases.length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr switchId cases
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchPostInitFreeMemoryState contract tx storage
          observableSlots store) =
      .error EvmYul.Yul.Exception.Revert :=
    exec_lowerNativeSwitchBlock_postInitFreeMemory_storePrefix_tail_error_fuel
      (fuel + cases.length) switchId cases [nativeRevertZeroZeroStmt] contract tx storage
      observableSlots store EvmYul.Yul.Exception.Revert hTail
  have hFuelEq : fuel + cases.length + 13 = (fuel + cases.length + 12).succ := by
    omega
  refine ⟨?_, by simp⟩
  rw [hFuelEq]
  exact exec_block_cons_error (fuel + cases.length + 12) _ [] _ _
    EvmYul.Yul.Exception.Revert hEndpoint

/-- Bridge-shape selector-hit error projection on the post-`__has_selector := 1`
    state. This packages a selected body halt/error with its projected result
    after the generated dispatcher-local binding has been installed. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (nativeYul : YulResult)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId nativeSwitchHasSelectorStore) =
        .error err)
    (hProject : projectResult tx storage initialEvents (.error err) = nativeYul) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody])
      (some contract)
      ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1)) = .error err ∧
    projectResult tx storage initialEvents (.error err) = nativeYul := by
  rcases exec_lowerNativeSwitchBlock_selector_find_hit_error_store_projectResult_eq
      fuel selector switchId tag cases defaultBody body contract tx storage
      initialEvents observableSlots nativeSwitchHasSelectorStore err nativeYul
      hSelector hFind hSelectorRange hTagsRange hBody hProject with
    ⟨hEndpoint, hProject'⟩
  have hFuelEq : fuel + cases.length + 13 = (fuel + cases.length + 12).succ := by
    omega
  rw [nativeSwitchInitialOkState_insert_hasSelector_eq, hFuelEq]
  exact ⟨exec_block_cons_error (fuel + cases.length + 12) _ [] _ _ err hEndpoint,
    hProject'⟩

/-- Bridge-shape selector-hit error projection on the post-generated-init
    `__has_selector := 1` state. This is the init-aware counterpart of
    `exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq`. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_postInitFreeMemory_hasSelectorState_error_projectResult_eq
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (nativeYul : YulResult)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        ((((nativeSwitchPostInitFreeMemoryState contract tx storage
                observableSlots nativeSwitchHasSelectorStore).insert
              (Backends.nativeSwitchDiscrTempName switchId)
              (EvmYul.UInt256.ofNat
                (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 0)).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1)) =
        .error err)
    (hProject : projectResult tx storage initialEvents (.error err) = nativeYul) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody])
      (some contract)
      ((nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
          ∅).insert "__has_selector" (EvmYul.UInt256.ofNat 1)) =
        .error err ∧
    projectResult tx storage initialEvents (.error err) = nativeYul := by
  rcases exec_lowerNativeSwitchBlock_selector_find_hit_error_postInitFreeMemory_store_projectResult_eq
      fuel selector switchId tag cases defaultBody body contract tx storage
      initialEvents observableSlots nativeSwitchHasSelectorStore err nativeYul
      hSelector hFind hSelectorRange hTagsRange hBody hProject with
    ⟨hEndpoint, hProject'⟩
  have hFuelEq : fuel + cases.length + 13 = (fuel + cases.length + 12).succ := by
    omega
  rw [hFuelEq]
  refine ⟨?_, hProject'⟩
  simpa [nativeSwitchHasSelectorStore, nativeSwitchPostInitFreeMemoryState,
    EvmYul.Yul.State.insert] using
    exec_block_cons_error (fuel + cases.length + 12) _ [] _ _ err hEndpoint

/-- Bridge-shape selector-hit success projection on the post-generated-init
    `__has_selector := 1` state, with the final matched-flag fact supplied
    directly. This is the init-aware counterpart of
    `exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_finalMatched`. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_postInitFreeMemory_hasSelectorState_ok_projectResult_eq_finalMatched
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State)
    (nativeYul : YulResult)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId nativeSwitchHasSelectorStore) =
        .ok final)
    (hFinalMatched :
      ∀ matchedName : EvmYul.Identifier,
        matchedName = Backends.nativeSwitchMatchedTempName switchId →
          final[matchedName]! = EvmYul.UInt256.ofNat 1)
    (hProject : projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody])
      (some contract)
      ((nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
          ∅).insert "__has_selector" (EvmYul.UInt256.ofNat 1)) =
        .ok final ∧
    projectResult tx storage initialEvents (.ok (final, [])) = nativeYul := by
  have hEndpoint :
      EvmYul.Yul.exec (fuel + cases.length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
        (some contract)
        (nativeSwitchPostInitFreeMemoryState contract tx storage
          observableSlots nativeSwitchHasSelectorStore) =
      .ok final :=
    exec_lowerNativeSwitchBlock_selector_find_hit_finalMatched_postInitFreeMemory_store_fuel
      fuel selector switchId tag cases defaultBody body contract tx storage
      observableSlots nativeSwitchHasSelectorStore final hSelector hFind
      hSelectorRange hTagsRange hBody hFinalMatched
  have hFuelEq : fuel + cases.length + 13 =
      (fuel + cases.length + 12).succ := by
    omega
  rw [hFuelEq]
  refine ⟨?_, hProject⟩
  simpa [nativeSwitchHasSelectorStore, nativeSwitchPostInitFreeMemoryState,
    EvmYul.Yul.State.insert] using
    exec_block_cons_ok (fuel + cases.length + 12) _ [] _ _ final final
      hEndpoint (by simp [EvmYul.Yul.exec])

/-- Bridge-shape selector-hit error projection for a payable generated case on
    the post-`__has_selector := 1` state, with generated case guards discharged
    before the selected user body premise. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq_payable_generated_prefix
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (nativeYul : YulResult)
    (reservedNames : List String) (n0 next : Nat)
    (fn : IRFunction)
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (body, next))
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) ∧
      ((∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots switchId
              nativeSwitchHasSelectorStore) =
            .error err) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error err) = nativeYul →
        EvmYul.Yul.exec (fuel + cases.length + 17)
            (.Block [Backends.lowerNativeSwitchBlock
              Compiler.Proofs.YulGeneration.selectorExpr switchId cases
              defaultBody])
            (some contract)
            ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
              storage observableSlots).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1)) =
          .error err ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error err) = nativeYul) := by
  rcases
    exec_lowerNativeSwitchBlock_selector_find_hit_error_store_projectResult_eq_payable_generated_prefix
      fuel selector switchId tag cases defaultBody body contract tx storage
      initialEvents observableSlots nativeSwitchHasSelectorStore err nativeYul
      reservedNames n0 next fn hSelector hFind hSelectorRange hTagsRange
      hLower hPayable hguards hNoWrap hArgs with
    ⟨bodyNative, bodyStart, hBodyLower, hEndpoint⟩
  refine ⟨bodyNative, bodyStart, hBodyLower, ?_⟩
  intro hBody hProject
  rcases hEndpoint hBody hProject with ⟨hExec, hProject'⟩
  have hFuelEq : fuel + cases.length + 17 =
      (fuel + cases.length + 16).succ := by
    omega
  rw [nativeSwitchInitialOkState_insert_hasSelector_eq, hFuelEq]
  exact ⟨exec_block_cons_error (fuel + cases.length + 16) _ [] _ _ err hExec,
    hProject'⟩

/-- Bridge-shape selector-hit error projection for a non-payable generated case
    on the post-`__has_selector := 1` state, with generated case guards
    discharged before the selected user body premise. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq_nonpayable_generated_prefix
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (nativeYul : YulResult)
    (reservedNames : List String) (n0 next : Nat)
    (fn : IRFunction)
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (body, next))
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) ∧
      ((∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots switchId
              nativeSwitchHasSelectorStore) =
            .error err) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error err) = nativeYul →
        EvmYul.Yul.exec (fuel + cases.length + 18)
            (.Block [Backends.lowerNativeSwitchBlock
              Compiler.Proofs.YulGeneration.selectorExpr switchId cases
              defaultBody])
            (some contract)
            ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
              storage observableSlots).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1)) =
          .error err ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error err) = nativeYul) := by
  rcases
    exec_lowerNativeSwitchBlock_selector_find_hit_error_store_projectResult_eq_nonpayable_generated_prefix
      fuel selector switchId tag cases defaultBody body contract tx storage
      initialEvents observableSlots nativeSwitchHasSelectorStore err nativeYul
      reservedNames n0 next fn hSelector hFind hSelectorRange hTagsRange
      hLower hNonPayable hguards hNoWrap hArgs with
    ⟨bodyNative, bodyStart, hBodyLower, hEndpoint⟩
  refine ⟨bodyNative, bodyStart, hBodyLower, ?_⟩
  intro hBody hProject
  rcases hEndpoint hBody hProject with ⟨hExec, hProject'⟩
  have hFuelEq : fuel + cases.length + 18 =
      (fuel + cases.length + 17).succ := by
    omega
  rw [nativeSwitchInitialOkState_insert_hasSelector_eq, hFuelEq]
  exact ⟨exec_block_cons_error (fuel + cases.length + 17) _ [] _ _ err hExec,
    hProject'⟩

/-- Selector-hit success projection for lowered native switches entered from
    the standard empty-store switch state. This is the normal-result companion
    to `exec_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq`. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_ok_projectResult_eq
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hFresh : Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchMarkedPrefixStateForId contract tx
          storage observableSlots switchId) = .ok final)
    (hStmtPreserves : ∀ stmt, stmt ∈ body →
      Backends.nativeSwitchMatchedTempName switchId ∉ Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
          (EvmYul.UInt256.ofNat 1) stmt (some contract))
    (hProject : projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .ok final ∧
    projectResult tx storage initialEvents (.ok (final, [])) = nativeYul := by
  refine ⟨?_, hProject⟩
  exact exec_lowerNativeSwitchBlock_selector_find_hit_fresh_fuel
    fuel selector switchId cases defaultBody tag body contract tx storage
    observableSlots final hSelector hFind hSelectorRange hTagsRange hFresh
    hBody hStmtPreserves

/-- Store-parametric selector-hit success projection for lowered native
    switches. The selected body may finish normally; callers provide the exact
    projection of that final state at the native result boundary. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_ok_store_projectResult_eq
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore) (final : EvmYul.Yul.State)
    (nativeYul : YulResult)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hFresh : Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId store) = .ok final)
    (hStmtPreserves : ∀ stmt, stmt ∈ body →
      Backends.nativeSwitchMatchedTempName switchId ∉ Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
          (EvmYul.UInt256.ofNat 1) stmt (some contract))
    (hProject : projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState store) =
      .ok final ∧
    projectResult tx storage initialEvents (.ok (final, [])) = nativeYul := by
  refine ⟨?_, hProject⟩
  exact exec_lowerNativeSwitchBlock_selector_find_hit_fresh_store_fuel
    fuel selector switchId tag cases defaultBody body contract tx storage
    observableSlots store final hSelector hFind hSelectorRange hTagsRange
    hFresh hBody hStmtPreserves

/-- Bridge-shape selector-hit success projection on the post-`__has_selector`
    state, deriving default-skip freshness and exposing the projected final
    native result in one package. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hFresh : Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId nativeSwitchHasSelectorStore) = .ok final)
    (hStmtPreserves : ∀ stmt, stmt ∈ body →
      Backends.nativeSwitchMatchedTempName switchId ∉ Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
          (EvmYul.UInt256.ofNat 1) stmt (some contract))
    (hProject : projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody])
      (some contract)
      ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1)) = .ok final ∧
    projectResult tx storage initialEvents (.ok (final, [])) = nativeYul := by
  rcases exec_lowerNativeSwitchBlock_selector_find_hit_ok_store_projectResult_eq
      fuel selector switchId tag cases defaultBody body contract tx storage
      initialEvents observableSlots nativeSwitchHasSelectorStore final nativeYul
      hSelector hFind hSelectorRange hTagsRange hFresh hBody hStmtPreserves
      hProject with
    ⟨hEndpoint, hProject'⟩
  have hFuelEq : fuel + cases.length + 13 = (fuel + cases.length + 12).succ := by
    omega
  rw [nativeSwitchInitialOkState_insert_hasSelector_eq, hFuelEq]
  exact ⟨exec_block_cons_ok (fuel + cases.length + 12) _ [] _ _ final final
    hEndpoint (by simp [EvmYul.Yul.exec]), hProject'⟩

/-- Bridge-shape selector-hit success projection on the post-`__has_selector`
    state, with the selected-body matched-flag preservation supplied directly
    as a block-level predicate. This is the same boundary as
    `exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq`,
    but avoids re-exposing per-statement preservation when callers already have
    a `NativeBlockPreservesWord` proof for the selected body. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_preserved
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId nativeSwitchHasSelectorStore) = .ok final)
    (hPreservesMatched : ∀ pre suffix,
      cases = pre ++ (tag, body) :: suffix →
        NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
          (EvmYul.UInt256.ofNat 1) body (some contract))
    (hProject : projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody])
      (some contract)
      ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1)) = .ok final ∧
    projectResult tx storage initialEvents (.ok (final, [])) = nativeYul := by
  refine ⟨?_, hProject⟩
  have hEndpoint :=
    exec_lowerNativeSwitchBlock_selector_find_hit_preserved_store_fuel
      fuel selector switchId tag cases defaultBody body contract tx storage
      observableSlots nativeSwitchHasSelectorStore final hSelector hFind
      hSelectorRange hTagsRange hBody hPreservesMatched
  have hFuelEq : fuel + cases.length + 13 = (fuel + cases.length + 12).succ := by
    omega
  rw [nativeSwitchInitialOkState_insert_hasSelector_eq, hFuelEq]
  exact exec_block_cons_ok (fuel + cases.length + 12) _ [] _ _ final final
    hEndpoint (by simp [EvmYul.Yul.exec])

/-- Bridge-shape selector-hit success projection on the post-`__has_selector`
    state, with the final matched-flag fact supplied directly. This is the
    checkpoint-aware endpoint used when the selected body proves preservation
    through `reviveJump` for the actual final state rather than as a raw
    whole-body preservation predicate. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_finalMatched
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId nativeSwitchHasSelectorStore) = .ok final)
    (hFinalMatched :
      ∀ matchedName : EvmYul.Identifier,
        matchedName = Backends.nativeSwitchMatchedTempName switchId →
          final[matchedName]! = EvmYul.UInt256.ofNat 1)
    (hProject : projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody])
      (some contract)
      ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1)) = .ok final ∧
    projectResult tx storage initialEvents (.ok (final, [])) = nativeYul := by
  refine ⟨?_, hProject⟩
  have hEndpoint :
      EvmYul.Yul.exec (fuel + cases.length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
        (some contract)
        (nativeSwitchHasSelectorInitialState contract tx storage observableSlots) =
      .ok final := by
    exact exec_lowerNativeSwitchBlock_selector_find_hit_finalMatched_store_fuel
      fuel selector switchId tag cases defaultBody body contract tx storage
      observableSlots nativeSwitchHasSelectorStore final hSelector hFind
      hSelectorRange hTagsRange hBody hFinalMatched
  have hFuelEq : fuel + cases.length + 13 = (fuel + cases.length + 12).succ := by
    omega
  rw [nativeSwitchInitialOkState_insert_hasSelector_eq, hFuelEq]
  exact exec_block_cons_ok (fuel + cases.length + 12) _ [] _ _ final final
    hEndpoint (by simp [EvmYul.Yul.exec])

/-- Bridge-shape selector-hit success projection for a payable generated case on
    the post-`__has_selector := 1` state, with generated case guards discharged
    before the selected user body premise. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_payable_generated_prefix
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State)
    (nativeYul : YulResult)
    (reservedNames : List String) (n0 next : Nat)
    (fn : IRFunction)
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (body, next))
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) ∧
      ((∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots switchId
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
          NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul →
        EvmYul.Yul.exec (fuel + cases.length + 17)
            (.Block [Backends.lowerNativeSwitchBlock
              Compiler.Proofs.YulGeneration.selectorExpr switchId cases
              defaultBody])
            (some contract)
            ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
              storage observableSlots).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1)) =
          .ok final ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul) := by
  rcases
    exec_lowerNativeSwitchBlock_selector_find_hit_ok_store_projectResult_eq_payable_generated_prefix
      fuel selector switchId tag cases defaultBody body contract tx storage
      initialEvents observableSlots nativeSwitchHasSelectorStore final
      nativeYul reservedNames n0 next fn hSelector hFind hSelectorRange
      hTagsRange hLower hPayable hguards hNoWrap hArgs with
    ⟨bodyNative, bodyStart, hBodyLower, hEndpoint⟩
  refine ⟨bodyNative, bodyStart, hBodyLower, ?_⟩
  intro hBody hPreserves hProject
  rcases hEndpoint hBody hPreserves hProject with ⟨hExec, hProject'⟩
  have hFuelEq : fuel + cases.length + 17 =
      (fuel + cases.length + 16).succ := by
    omega
  rw [nativeSwitchInitialOkState_insert_hasSelector_eq, hFuelEq]
  exact ⟨exec_block_cons_ok (fuel + cases.length + 16) _ [] _ _
    final final hExec (by simp [EvmYul.Yul.exec]), hProject'⟩

/-- Bridge-shape selector-hit success projection for a non-payable generated
    case on the post-`__has_selector := 1` state, with generated case guards
    discharged before the selected user body premise. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_nonpayable_generated_prefix
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State)
    (nativeYul : YulResult)
    (reservedNames : List String) (n0 next : Nat)
    (fn : IRFunction)
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (body, next))
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) ∧
      ((∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots switchId
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
          NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul →
        EvmYul.Yul.exec (fuel + cases.length + 18)
            (.Block [Backends.lowerNativeSwitchBlock
              Compiler.Proofs.YulGeneration.selectorExpr switchId cases
              defaultBody])
            (some contract)
            ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
              storage observableSlots).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1)) =
          .ok final ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul) := by
  rcases
    exec_lowerNativeSwitchBlock_selector_find_hit_ok_store_projectResult_eq_nonpayable_generated_prefix
      fuel selector switchId tag cases defaultBody body contract tx storage
      initialEvents observableSlots nativeSwitchHasSelectorStore final
      nativeYul reservedNames n0 next fn hSelector hFind hSelectorRange
      hTagsRange hLower hNonPayable hguards hNoWrap hArgs with
    ⟨bodyNative, bodyStart, hBodyLower, hEndpoint⟩
  refine ⟨bodyNative, bodyStart, hBodyLower, ?_⟩
  intro hBody hPreserves hProject
  rcases hEndpoint hBody hPreserves hProject with ⟨hExec, hProject'⟩
  have hFuelEq : fuel + cases.length + 18 =
      (fuel + cases.length + 17).succ := by
    omega
  rw [nativeSwitchInitialOkState_insert_hasSelector_eq, hFuelEq]
  exact ⟨exec_block_cons_ok (fuel + cases.length + 17) _ [] _ _
    final final hExec (by simp [EvmYul.Yul.exec]), hProject'⟩

/-- Contract-dispatcher boundary for a generated lowered selector-switch hit
    whose selected body exits through an EVMYulLean error or halt channel. -/
theorem contractDispatcherExecResult_block_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (dispatcher : EvmYul.Yul.Ast.Stmt) (functions : NativeFunctionMap)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (initialEvents : List (List Nat))
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hDispatcher : dispatcher = Backends.lowerNativeSwitchBlock
      Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
    (hContract : contract = { dispatcher := .Block [dispatcher], functions := functions })
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        (nativeSwitchMarkedPrefixStateForId contract tx storage
          observableSlots switchId) = .error err)
    (hProject : projectResult tx storage initialEvents (.error err) = nativeYul) :
    contractDispatcherExecResult (Nat.succ (Nat.succ (fuel + cases.length + 12)))
        contract (initialState contract tx storage observableSlots) =
      .error err ∧
    projectResult tx storage initialEvents (.error err) = nativeYul := by
  subst hDispatcher
  subst hContract
  let dispatcher' :=
    Backends.lowerNativeSwitchBlock
      Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody
  let contract' : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [dispatcher'], functions := functions }
  rcases exec_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq
      fuel selector switchId cases defaultBody tag body contract' tx storage
      initialEvents observableSlots err nativeYul hSelector hFind hSelectorRange
      hTagsRange hBody hProject with
    ⟨hExec, hProject'⟩
  rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
    (fuel + cases.length + 12) [dispatcher'] functions tx storage observableSlots]
  exact
    ⟨exec_block_cons_error (fuel + cases.length + 12) dispatcher' []
        (some contract') (nativeSwitchInitialOkState contract' tx storage observableSlots)
        err hExec,
      hProject'⟩

/-- Contract-dispatcher boundary for a generated lowered selector-switch hit
    whose selected body finishes normally. -/
theorem contractDispatcherExecResult_block_lowerNativeSwitchBlock_selector_find_hit_ok_projectResult_eq
    (fuel selector switchId tag : Nat) (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (dispatcher : EvmYul.Yul.Ast.Stmt) (functions : NativeFunctionMap)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (initialEvents : List (List Nat))
    (observableSlots : List Nat) (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hDispatcher : dispatcher = Backends.lowerNativeSwitchBlock
      Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
    (hContract : contract = { dispatcher := .Block [dispatcher], functions := functions })
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hFresh : Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchMarkedPrefixStateForId contract tx storage
          observableSlots switchId) = .ok final)
    (hStmtPreserves : ∀ stmt, stmt ∈ body →
      Backends.nativeSwitchMatchedTempName switchId ∉ Backends.nativeStmtWriteNames stmt →
      NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
          (EvmYul.UInt256.ofNat 1) stmt (some contract))
    (hProject : projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) :
    contractDispatcherExecResult (Nat.succ (Nat.succ (fuel + cases.length + 12)))
        contract (initialState contract tx storage observableSlots) = .ok final ∧
    projectResult tx storage initialEvents (.ok (final, [])) = nativeYul := by
  subst hDispatcher
  subst hContract
  let dispatcher' := Backends.lowerNativeSwitchBlock
    Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody
  let contract' : EvmYul.Yul.Ast.YulContract := { dispatcher := .Block [dispatcher'], functions := functions }
  rcases exec_lowerNativeSwitchBlock_selector_find_hit_ok_projectResult_eq
      fuel selector switchId tag cases defaultBody body contract' tx storage
      initialEvents observableSlots final nativeYul hSelector hFind
      hSelectorRange hTagsRange hFresh hBody hStmtPreserves hProject with
    ⟨hExec, hProject'⟩
  rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
    (fuel + cases.length + 12) [dispatcher'] functions tx storage observableSlots]
  exact
    ⟨exec_block_cons_ok (fuel + cases.length + 12) dispatcher' []
        (some contract') (nativeSwitchInitialOkState contract' tx storage observableSlots)
        final final hExec (by simp [EvmYul.Yul.exec]),
      hProject'⟩

/-- Guarded selector-miss execution for a fully lowered native switch block,
    lifted through Verity's projected native result boundary. The generated
    `revert(0, 0)` default both executes through the actual native step
    relation and projects as a failed call with no return word and rolled-back
    observable storage. -/
theorem exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr switchId cases
            [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    (projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert)).success = false ∧
    (projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert)).returnValue = none ∧
    (∀ slot,
      (projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert)).finalStorage (IRStorageSlot.ofNat slot) =
          storage (IRStorageSlot.ofNat slot)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_fuel
      fuel selector switchId cases contract tx storage observableSlots
      hSelector hFind hSelectorRange hTagsRange
  · simp
  · simp
  · intro slot
    simp

/-- Guarded selector-miss execution for a fully lowered native switch block,
    with the projected revert result exposed as one exact `YulResult`.

This generic package is the native dispatcher boundary needed by generated
selector-miss proofs: the lowered switch reaches EVMYulLean's `Revert`, and
Verity's projection rolls storage and events back to the call pre-state. -/
theorem exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult_eq
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr switchId cases
            [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert) =
      { success := false
        returnValue := none
        finalStorage := storage
        finalMappings := Compiler.Proofs.storageAsMappings storage
        events := initialEvents } := by
  rcases
    exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult
      fuel selector switchId cases contract tx storage initialEvents
      observableSlots hSelector hFind hSelectorRange hTagsRange with
    ⟨hExec, _hSuccess, _hReturn, _hStorage⟩
  exact ⟨hExec, by simp⟩

/-- Contract-dispatcher boundary for a generated lowered selector-switch miss.

This lifts the generic `lowerNativeSwitchBlock` selector-miss theorem through
the actual native dispatcher execution wrapper used by the public EndToEnd
target. -/
theorem contractDispatcherExecResult_block_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult_eq
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    let dispatcher :=
      Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases
        [nativeRevertZeroZeroStmt]
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [dispatcher], functions := functions }
    contractDispatcherExecResult (Nat.succ (Nat.succ (fuel + cases.length + 12)))
        contract (initialState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert) =
      { success := false
        returnValue := none
        finalStorage := storage
        finalMappings := Compiler.Proofs.storageAsMappings storage
        events := initialEvents } := by
  intro dispatcher contract
  rcases
    exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult_eq
      fuel selector switchId cases contract tx storage initialEvents
      observableSlots hSelector hFind hSelectorRange hTagsRange with
    ⟨hExec, hProject⟩
  rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
    (fuel + cases.length + 12) [dispatcher] functions tx storage observableSlots]
  exact
    ⟨exec_block_cons_error (fuel + cases.length + 12) dispatcher [] (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots)
        EvmYul.Yul.Exception.Revert hExec,
      hProject⟩

/-- Generic selector-miss native execution package for a no-fallback/no-receive
    generated dispatcher.

This opens the actual native lowering of `buildSwitch funcs none none`, links the
source function-table miss to the lowered lazy-switch miss, and lifts the result
through the real `contractDispatcherExecResult` wrapper. The fuel is still the
structural dispatcher fuel exposed by the current native switch lemmas; the
canonical theorem-facing fuel remains a separate monotonicity/size-bound step. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_none_projectResult_eq
    (fuel selector : Nat)
    (funcs : List IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun fn => fn.selector == selector) = none)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
          (Backends.freshNativeSwitchId reservedNames n0 + 1)
          (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      contractDispatcherExecResult (fuel + cases'.length + 19)
          contract (initialState contract tx storage observableSlots) =
        .error EvmYul.Yul.Exception.Revert ∧
      projectResult tx storage initialEvents
          (.error EvmYul.Yul.Exception.Revert) =
        { success := false
          returnValue := none
          finalStorage := storage
          finalMappings := Compiler.Proofs.storageAsMappings storage
          events := initialEvents } := by
  obtain ⟨body1, reservedNames, n0, cases', midN, hInner, hLowerCases⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered funcs inner hLower
  refine ⟨reservedNames, n0, cases', midN, ?_, ?_, ?_⟩
  · exact hLowerCases
  · let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hLowerFind :
        cases'.find? (fun entry => entry.1 == selector) = none :=
      lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_none_of_find_function
        reservedNames (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
        selector funcs cases' hLowerCases hFind
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hPeel :
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      let contract' : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      have hFuelShape :
          fuel + cases'.length + 19 =
            Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
        omega
      have hDispatcherPeel :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract' (initialState contract' tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner) (some contract')
              (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
        rw [hFuelShape]
        change
          contractDispatcherExecResult
              (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
              { dispatcher := .Block [.Block inner], functions := functions }
              (initialState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner)
              (some { dispatcher := .Block [.Block inner], functions := functions })
              (nativeSwitchInitialOkState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots)
        rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
          (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
          tx storage observableSlots]
        rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
          (some { dispatcher := .Block [.Block inner], functions := functions })
          (nativeSwitchInitialOkState
            { dispatcher := .Block [.Block inner], functions := functions }
            tx storage observableSlots)]
      calc
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots)
            = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
        _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block
                [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                    (some
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero"
                          [YulExpr.call "lt"
                            [YulExpr.call "calldatasize" [],
                             YulExpr.lit 4]]))),
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative
                      (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                    body1,
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                    [Backends.lowerNativeSwitchBlock
                      (YulExpr.call "shr"
                        [YulExpr.lit Compiler.Constants.selectorShift,
                         YulExpr.call "calldataload" [YulExpr.lit 0]])
                      (Backends.freshNativeSwitchId reservedNames n0) cases'
                      [nativeRevertZeroZeroStmt]]])
              (some contract)
              (nativeSwitchInitialOkState contract tx storage observableSlots) := by
            exact congrArg
              (fun body =>
                EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block body) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots))
              hInner
        _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
              have hExec :=
                (exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                  (fuel + cases'.length + 5) contract tx storage observableSlots
                  "__has_selector" body1
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames n0) cases'
                    [nativeRevertZeroZeroStmt]]
                  hNoWrap)
              simpa only [Nat.add_assoc] using hExec
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_error
      fuel selector (Backends.freshNativeSwitchId reservedNames n0) cases'
      contract tx storage observableSlots hSelector hLowerFind hSelectorRange
      hTagsRange
  · simp

/-- Exact-total-fuel companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_none_projectResult_eq`.

The theorem opens the generated dispatcher lowering first, exposes the lowered
case list, and then runs the dispatcher at any total fuel that covers the
structural selector-miss budget `cases'.length + 19`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_none_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (funcs : List IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun fn => fn.selector == selector) = none)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
          (Backends.freshNativeSwitchId reservedNames n0 + 1)
          (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      (cases'.length + 19 ≤ fuel' →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .error EvmYul.Yul.Exception.Revert ∧
        projectResult tx storage initialEvents
            (.error EvmYul.Yul.Exception.Revert) =
          { success := false
            returnValue := none
            finalStorage := storage
            finalMappings := Compiler.Proofs.storageAsMappings storage
            events := initialEvents }) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, hInner, hLowerCases⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered funcs inner hLower
  refine ⟨reservedNames, n0, cases', midN, ?_, ?_⟩
  · exact hLowerCases
  · intro hFuel
    let fuel := fuel' - (cases'.length + 19)
    have hFuelShape : fuel' = fuel + cases'.length + 19 := by
      dsimp [fuel]
      exact (Nat.sub_add_cancel hFuel).symm
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hLowerFind :
        cases'.find? (fun entry => entry.1 == selector) = none :=
      lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_none_of_find_function
        reservedNames (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
        selector funcs cases' hLowerCases hFind
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hPeel :
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      rw [hFuelShape]
      have hPeelStructural :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
        let contract' : EvmYul.Yul.Ast.YulContract :=
          { dispatcher := .Block [.Block inner], functions := functions }
        have hFuelShape' :
            fuel + cases'.length + 19 =
              Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
          omega
        have hDispatcherPeel :
            contractDispatcherExecResult (fuel + cases'.length + 19)
                contract' (initialState contract' tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract')
                (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
          rw [hFuelShape']
          change
            contractDispatcherExecResult
                (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
                { dispatcher := .Block [.Block inner], functions := functions }
                (initialState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner)
                (some { dispatcher := .Block [.Block inner], functions := functions })
                (nativeSwitchInitialOkState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots)
          rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
            (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
            tx storage observableSlots]
          rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (nativeSwitchInitialOkState
              { dispatcher := .Block [.Block inner], functions := functions }
              tx storage observableSlots)]
        calc
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots)
              = EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block inner) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
          _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block
                  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                      (some
                        (Backends.lowerExprNative
                          (YulExpr.call "iszero"
                            [YulExpr.call "lt"
                              [YulExpr.call "calldatasize" [],
                               YulExpr.lit 4]]))),
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                      body1,
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                      [Backends.lowerNativeSwitchBlock
                        (YulExpr.call "shr"
                          [YulExpr.lit Compiler.Constants.selectorShift,
                           YulExpr.call "calldataload" [YulExpr.lit 0]])
                        (Backends.freshNativeSwitchId reservedNames n0) cases'
                        [nativeRevertZeroZeroStmt]]])
                (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := by
              exact congrArg
                (fun body =>
                  EvmYul.Yul.exec (fuel + cases'.length + 17)
                    (.Block body) (some contract)
                    (nativeSwitchInitialOkState contract tx storage observableSlots))
                hInner
          _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
                (.Block
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames n0) cases'
                    [nativeRevertZeroZeroStmt]])
                (some contract)
                ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                  "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
                have hExec :=
                  (exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                    (fuel + cases'.length + 5) contract tx storage observableSlots
                    "__has_selector" body1
                    [Backends.lowerNativeSwitchBlock
                      (YulExpr.call "shr"
                        [YulExpr.lit Compiler.Constants.selectorShift,
                         YulExpr.call "calldataload" [YulExpr.lit 0]])
                      (Backends.freshNativeSwitchId reservedNames n0) cases'
                      [nativeRevertZeroZeroStmt]]
                    hNoWrap)
                simpa only [Nat.add_assoc] using hExec
      exact hPeelStructural
    constructor
    · rw [hPeel]
      exact exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_error
        fuel selector (Backends.freshNativeSwitchId reservedNames n0) cases'
        contract tx storage observableSlots hSelector hLowerFind hSelectorRange
        hTagsRange
    · simp

/-- Generic selector-hit native execution package for a no-fallback/no-receive
generated dispatcher when the selected native body exits through an error/halt
channel.

The theorem opens `buildSwitch` lowering, exposes the selected lowered body, and
packages the remaining body-execution premise at the post-selector-match state. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_projectResult_eq
    (fuel selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .error err) →
        projectResult tx storage initialEvents (.error err) = nativeYul →
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          .error err ∧
        projectResult tx storage initialEvents (.error err) = nativeYul) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  refine ⟨reservedNames, n0, cases', body', bodyStart, bodyEnd, ?_, ?_, ?_⟩
  · exact hCase
  · exact hBodyLower
  · intro hBody hProject
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hPeel :
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      let contract' : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      have hFuelShape :
          fuel + cases'.length + 19 =
            Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
        omega
      have hDispatcherPeel :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract' (initialState contract' tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner) (some contract')
              (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
        rw [hFuelShape]
        change
          contractDispatcherExecResult
              (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
              { dispatcher := .Block [.Block inner], functions := functions }
              (initialState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner)
              (some { dispatcher := .Block [.Block inner], functions := functions })
              (nativeSwitchInitialOkState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots)
        rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
          (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
          tx storage observableSlots]
        rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
          (some { dispatcher := .Block [.Block inner], functions := functions })
          (nativeSwitchInitialOkState
            { dispatcher := .Block [.Block inner], functions := functions }
            tx storage observableSlots)]
      calc
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots)
            = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
        _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block
                [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                    (some
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero"
                          [YulExpr.call "lt"
                            [YulExpr.call "calldatasize" [],
                             YulExpr.lit 4]]))),
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative
                      (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                    body1,
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                    [Backends.lowerNativeSwitchBlock
                      (YulExpr.call "shr"
                        [YulExpr.lit Compiler.Constants.selectorShift,
                         YulExpr.call "calldataload" [YulExpr.lit 0]])
                      (Backends.freshNativeSwitchId reservedNames n0) cases'
                      [nativeRevertZeroZeroStmt]]])
              (some contract)
              (nativeSwitchInitialOkState contract tx storage observableSlots) := by
            exact congrArg
              (fun body =>
                EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block body) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots))
              hInner
        _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
              have hExec :=
                (exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                  (fuel + cases'.length + 5) contract tx storage observableSlots
                  "__has_selector" body1
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames n0) cases'
                    [nativeRevertZeroZeroStmt]]
                  hNoWrap)
              simpa only [Nat.add_assoc] using hExec
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq
      fuel selector (Backends.freshNativeSwitchId reservedNames n0) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots err nativeYul hSelector hCase hSelectorRange hTagsRange
      hBody hProject

/-- Structural dispatcher/prologue peel for no-fallback/no-receive generated
    dispatchers after the selector availability guard succeeds. This isolates
    the common `__has_selector` setup and lazy native switch entry shape. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
    (fuel : Nat)
    (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (body1 inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hInner :
      inner =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some
              (Backends.lowerExprNative
                (YulExpr.call "iszero"
                  [YulExpr.call "lt"
                    [YulExpr.call "calldatasize" [], YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
            body1,
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]]])
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    contractDispatcherExecResult (fuel + cases'.length + 19)
        contract (initialState contract tx storage observableSlots) =
      EvmYul.Yul.exec (fuel + cases'.length + 13)
        (.Block
          [Backends.lowerNativeSwitchBlock
            (YulExpr.call "shr"
              [YulExpr.lit Compiler.Constants.selectorShift,
               YulExpr.call "calldataload" [YulExpr.lit 0]])
            (Backends.freshNativeSwitchId reservedNames n0) cases'
            [nativeRevertZeroZeroStmt]])
        (some contract)
        ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
  intro contract
  let contract' : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hFuelShape :
      fuel + cases'.length + 19 =
        Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
    omega
  have hDispatcherPeel :
      contractDispatcherExecResult (fuel + cases'.length + 19)
          contract' (initialState contract' tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 17)
          (.Block inner) (some contract')
          (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
    rw [hFuelShape]
    change
      contractDispatcherExecResult
          (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
          { dispatcher := .Block [.Block inner], functions := functions }
          (initialState
            { dispatcher := .Block [.Block inner], functions := functions }
            tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 17)
          (.Block inner)
          (some { dispatcher := .Block [.Block inner], functions := functions })
          (nativeSwitchInitialOkState
            { dispatcher := .Block [.Block inner], functions := functions }
            tx storage observableSlots)
    rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
      (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
      tx storage observableSlots]
    rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
      (some { dispatcher := .Block [.Block inner], functions := functions })
      (nativeSwitchInitialOkState
        { dispatcher := .Block [.Block inner], functions := functions }
        tx storage observableSlots)]
  calc
    contractDispatcherExecResult (fuel + cases'.length + 19)
        contract (initialState contract tx storage observableSlots)
        = EvmYul.Yul.exec (fuel + cases'.length + 17)
            (.Block inner) (some contract)
            (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
    _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
          (.Block
            [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                (some
                  (Backends.lowerExprNative
                    (YulExpr.call "iszero"
                      [YulExpr.call "lt"
                        [YulExpr.call "calldatasize" [],
                         YulExpr.lit 4]]))),
             EvmYul.Yul.Ast.Stmt.If
                (Backends.lowerExprNative
                  (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                body1,
             EvmYul.Yul.Ast.Stmt.If
                (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]]])
          (some contract)
          (nativeSwitchInitialOkState contract tx storage observableSlots) := by
        exact congrArg
          (fun body =>
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block body) (some contract)
              (nativeSwitchInitialOkState contract tx storage observableSlots))
          hInner
    _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
            "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
        have hExec :=
          exec_block_letSelector_if1Skip_if2Take_initialState_fuel
            (fuel + cases'.length + 5) contract tx storage observableSlots
            "__has_selector" body1
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]]
            hNoWrap
        simpa only [Nat.add_assoc] using hExec

/-- Structural dispatcher/prologue peel for generated runtimes whose dispatcher
    starts with the exact `initFreeMemoryPointer` statement before the lowered
    `buildSwitch` block. This is the generated-init companion to
    `contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel`.

    The post-init state is explicit, and the `__has_selector := 1` transition
    is modeled as part of the generated prefix rather than recovered later as a
    raw variable-store fact. -/
theorem contractDispatcherExecResult_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_peel
    (fuel : Nat)
    (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (body1 inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hInner :
      inner =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some
              (Backends.lowerExprNative
                (YulExpr.call "iszero"
                  [YulExpr.call "lt"
                    [YulExpr.call "calldatasize" [], YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
            body1,
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]]])
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    let initStmt : EvmYul.Yul.Ast.Stmt :=
      .ExprStmtCall
        (Backends.lowerExprNative
          (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
             Yul.YulExpr.lit 128]))
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [initStmt, .Block inner], functions := functions }
    contractDispatcherExecResult (fuel + cases'.length + 20)
        contract (initialState contract tx storage observableSlots) =
      EvmYul.Yul.exec (fuel + cases'.length + 13)
        (.Block
          [Backends.lowerNativeSwitchBlock
            (YulExpr.call "shr"
              [YulExpr.lit Compiler.Constants.selectorShift,
               YulExpr.call "calldataload" [YulExpr.lit 0]])
            (Backends.freshNativeSwitchId reservedNames n0) cases'
            [nativeRevertZeroZeroStmt]])
        (some contract)
        ((nativeSwitchPostInitFreeMemoryState contract tx storage
          observableSlots ∅).insert "__has_selector"
          (EvmYul.UInt256.ofNat 1)) := by
  intro initStmt contract
  let contract' : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [initStmt, .Block inner], functions := functions }
  have hFuelShape :
      fuel + cases'.length + 20 =
        Nat.succ (Nat.succ (fuel + cases'.length + 18)) := by
    omega
  have hDispatcherPeel :
      contractDispatcherExecResult (fuel + cases'.length + 20)
          contract' (initialState contract' tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 17)
          (.Block inner) (some contract')
          (nativeSwitchPostInitFreeMemoryState contract' tx storage
            observableSlots ∅) := by
    rw [hFuelShape]
    dsimp [contract']
    rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
      (fuel + cases'.length + 18) [initStmt, .Block inner] functions
      tx storage observableSlots]
    rw [show Nat.succ (fuel + cases'.length + 18) =
        Nat.succ ((fuel + cases'.length + 12) + 6) by omega]
    rw [exec_block_cons_initFreeMemoryPointer_eq
      (fuel + cases'.length + 12) [.Block inner] contract'
      tx storage observableSlots]
    rw [show (fuel + cases'.length + 12) + 6 =
        Nat.succ (Nat.succ (fuel + cases'.length + 16)) by omega]
    rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
      (some contract')
      (nativeSwitchPostInitFreeMemoryState contract' tx storage observableSlots ∅)]
  calc
    contractDispatcherExecResult (fuel + cases'.length + 20)
        contract (initialState contract tx storage observableSlots)
        = EvmYul.Yul.exec (fuel + cases'.length + 17)
            (.Block inner) (some contract)
            (nativeSwitchPostInitFreeMemoryState contract tx storage
              observableSlots ∅) := hDispatcherPeel
    _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
          (.Block
            [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                (some
                  (Backends.lowerExprNative
                    (YulExpr.call "iszero"
                      [YulExpr.call "lt"
                        [YulExpr.call "calldatasize" [],
                         YulExpr.lit 4]]))),
             EvmYul.Yul.Ast.Stmt.If
                (Backends.lowerExprNative
                  (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                body1,
             EvmYul.Yul.Ast.Stmt.If
                (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]]])
          (some contract)
          (nativeSwitchPostInitFreeMemoryState contract tx storage
            observableSlots ∅) := by
        exact congrArg
          (fun body =>
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block body) (some contract)
              (nativeSwitchPostInitFreeMemoryState contract tx storage
                observableSlots ∅))
          hInner
    _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchPostInitFreeMemoryState contract tx storage
            observableSlots ∅).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
          have hExec :=
            (exec_block_letSelector_if1Skip_if2Take_postInitFreeMemory_fuel
              (fuel + cases'.length + 5) contract tx storage observableSlots ∅
              "__has_selector" body1
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]]
              hNoWrap)
          simpa only [Nat.add_assoc] using hExec

/-- Generated-prefix variant of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_projectResult_eq`
for payable functions.

The public selected-body premise is over the lowered user body `fn.body`, not
the whole generated `switchCaseBody fn`; this theorem discharges the generated
comment no-op and calldata-size guard before applying the existing dispatcher
selector-hit wrapper at the correspondingly larger structural fuel. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_payable_generated_prefix_projectResult_eq
    (fuel selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots
              (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .error err) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error err) = nativeYul →
        contractDispatcherExecResult (fuel + cases'.length + 23)
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .error err ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error err) = nativeYul) := by
  obtain ⟨reservedNames, n0, cases', body', bodyStart, bodyEnd,
      hCase, hBodyLower, hDispatcherContinuation⟩ :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_projectResult_eq
      (fuel + 4) selector funcs fn inner functions (YulTransaction.ofIR tx)
      storage initialEvents observableSlots err nativeYul hLower hSelector
      hFind (by simpa [YulTransaction.ofIR_args] using hNoWrap)
      hSelectorRange hFunctionSelectorsRange
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_eq
      reservedNames bodyStart fn body' bodyEnd hPayable hBodyLower with
    ⟨guardBody, bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
  refine ⟨reservedNames, n0, cases', body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hCase, hBodyLower, hUserBodyLower, ?_⟩
  intro hUserBody hProject
  have hWholeBody :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (((fuel + 4) + 1) + suffix.length + 7)
          (.Block body') (some
            ({ dispatcher := .Block [.Block inner], functions := functions } :
              EvmYul.Yul.Ast.YulContract))
          (nativeSwitchStoreMarkedPrefixStateForId
            ({ dispatcher := .Block [.Block inner], functions := functions } :
              EvmYul.Yul.Ast.YulContract)
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames n0)
            nativeSwitchHasSelectorStore) = .error err := by
    intro pre suffix hCases
    rw [hBodyShape]
    have hPrefix := exec_switchCaseBody_payable_prefix_eq
      (fuel + suffix.length + 1) guardBody bodyNative
      ({ dispatcher := .Block [.Block inner], functions := functions } :
        EvmYul.Yul.Ast.YulContract)
      (YulTransaction.ofIR tx) storage observableSlots
      (Backends.freshNativeSwitchId reservedNames n0)
      nativeSwitchHasSelectorStore (4 + fn.params.length * 32)
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
      (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
      (by simp; omega)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hPrefix.trans (hUserBody pre suffix hCases)
  have hResult := hDispatcherContinuation hWholeBody hProject
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hResult

/-- Generated-prefix variant of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_projectResult_eq`
for non-payable functions.

The public selected-body premise is over the lowered user body `fn.body`; this
theorem discharges the generated comment no-op, callvalue guard, and
calldata-size guard before applying the existing dispatcher selector-hit
wrapper at the correspondingly larger structural fuel. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_nonpayable_generated_prefix_projectResult_eq
    (fuel selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots
              (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .error err) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error err) = nativeYul →
        contractDispatcherExecResult (fuel + cases'.length + 24)
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .error err ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error err) = nativeYul) := by
  obtain ⟨reservedNames, n0, cases', body', bodyStart, bodyEnd,
      hCase, hBodyLower, hDispatcherContinuation⟩ :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_projectResult_eq
      (fuel + 5) selector funcs fn inner functions (YulTransaction.ofIR tx)
      storage initialEvents observableSlots err nativeYul hLower hSelector
      hFind (by simpa [YulTransaction.ofIR_args] using hNoWrap)
      hSelectorRange hFunctionSelectorsRange
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_eq
      reservedNames bodyStart fn body' bodyEnd hNonPayable hBodyLower with
    ⟨callvalueGuardBody, calldataGuardBody, bodyNative, userBodyStart,
      hBodyShape, hUserBodyLower⟩
  refine ⟨reservedNames, n0, cases', body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hCase, hBodyLower, hUserBodyLower, ?_⟩
  intro hUserBody hProject
  have hWholeBody :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (((fuel + 5) + 1) + suffix.length + 7)
          (.Block body') (some
            ({ dispatcher := .Block [.Block inner], functions := functions } :
              EvmYul.Yul.Ast.YulContract))
          (nativeSwitchStoreMarkedPrefixStateForId
            ({ dispatcher := .Block [.Block inner], functions := functions } :
              EvmYul.Yul.Ast.YulContract)
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames n0)
            nativeSwitchHasSelectorStore) = .error err := by
    intro pre suffix hCases
    rw [hBodyShape]
    have hPrefix := exec_switchCaseBody_nonpayable_prefix_eq
      (fuel + suffix.length + 1) callvalueGuardBody calldataGuardBody
      bodyNative
      ({ dispatcher := .Block [.Block inner], functions := functions } :
        EvmYul.Yul.Ast.YulContract)
      (YulTransaction.ofIR tx) storage observableSlots
      (Backends.freshNativeSwitchId reservedNames n0)
      nativeSwitchHasSelectorStore (4 + fn.params.length * 32)
      (DispatchGuardsSafe_msgValue_zero_mod_of_nonpayable fn tx hguards
        hNonPayable)
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
      (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
      (by simp; omega)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hPrefix.trans (hUserBody pre suffix hCases)
  have hResult := hDispatcherContinuation hWholeBody hProject
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hResult

set_option linter.unusedVariables false in
/-- Non-payable selector-hit value-guard failure for a generated dispatcher.

This closes the generated `callvalue()` revert path directly: when the selected
function is non-payable and `msgValue` is nonzero modulo the EVM word modulus,
the selected switch-case prefix reverts before the calldata guard or user body.
-/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_nonpayable_callvalue_revert_projectResult_eq
    (fuel selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false)
    (hNonzero : tx.msgValue % evmModulus ≠ 0) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      contractDispatcherExecResult (fuel + cases'.length + 24)
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        .error EvmYul.Yul.Exception.Revert ∧
      projectResult (YulTransaction.ofIR tx) storage initialEvents
          (.error EvmYul.Yul.Exception.Revert) =
        projectResult (YulTransaction.ofIR tx) storage initialEvents
          (.error EvmYul.Yul.Exception.Revert) := by
  obtain ⟨reservedNames, n0, cases', body', bodyStart, bodyEnd,
      hCase, hBodyLower, hDispatcherContinuation⟩ :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_projectResult_eq
      (fuel + 5) selector funcs fn inner functions (YulTransaction.ofIR tx)
      storage initialEvents observableSlots EvmYul.Yul.Exception.Revert
      (projectResult (YulTransaction.ofIR tx) storage initialEvents
        (.error EvmYul.Yul.Exception.Revert))
      hLower hSelector hFind
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
      hSelectorRange hFunctionSelectorsRange
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hNonPayable hBodyLower with
    ⟨bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hWholeBody :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (((fuel + 5) + 1) + suffix.length + 7)
          (.Block body') (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames n0)
            nativeSwitchHasSelectorStore) =
          .error EvmYul.Yul.Exception.Revert := by
    intro pre suffix _hCases
    rw [hBodyShape]
    have hExec :=
      exec_switchCaseBody_nonpayable_callvalue_revert_fuel
        (fuel + suffix.length + 1)
        [nativeRevertZeroZeroStmt] bodyNative contract (YulTransaction.ofIR tx) storage
        observableSlots (Backends.freshNativeSwitchId reservedNames n0)
        nativeSwitchHasSelectorStore (4 + fn.params.length * 32)
        (by simpa [YulTransaction.ofIR] using hNonzero)
    simpa [contract, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hExec
  have hResult := hDispatcherContinuation hWholeBody rfl
  refine ⟨reservedNames, n0, cases', body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hCase, hBodyLower, hUserBodyLower, ?_⟩
  simpa [contract, Compiler.Proofs.YulGeneration.selectorExpr,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hResult

set_option linter.unusedVariables false in
/-- Exact-total-fuel companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_nonpayable_callvalue_revert_projectResult_eq`.
-/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_nonpayable_callvalue_revert_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false)
    (hNonzero : tx.msgValue % evmModulus ≠ 0) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 24 ≤ fuel' →
        contractDispatcherExecResult fuel'
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .error EvmYul.Yul.Exception.Revert ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error EvmYul.Yul.Exception.Revert) =
          projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error EvmYul.Yul.Exception.Revert)) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hNonPayable hBodyLower with
    ⟨bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange fn hFn
  refine ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart,
    bodyEnd, userBodyStart, hLowerCases, hCase, hBodyLower,
    hUserBodyLower, ?_⟩
  intro hFuel
  let fuel := fuel' - (cases'.length + 24)
  have hFuelShape : fuel' = fuel + cases'.length + 24 := by
    dsimp [fuel]
    exact (Nat.sub_add_cancel hFuel).symm
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 5) reservedNames n0 cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult fuel'
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 18)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    rw [hFuelShape]
    have hDispatcherFuel :
        fuel + cases'.length + 24 =
          (fuel + 5) + cases'.length + 19 := by omega
    have hSwitchFuel :
        fuel + cases'.length + 18 =
          (fuel + 5) + cases'.length + 13 := by omega
    rw [hDispatcherFuel, hSwitchFuel]
    simpa [contract] using hPeel
  rw [hPeel']
  have hBody :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (((fuel + 5) + 1) + suffix.length + 7)
          (.Block body') (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames n0)
            nativeSwitchHasSelectorStore) =
        .error EvmYul.Yul.Exception.Revert := by
    intro pre suffix _hCases
    rw [hBodyShape]
    have hExec :=
      exec_switchCaseBody_nonpayable_callvalue_revert_fuel
        (fuel + suffix.length + 1)
        [nativeRevertZeroZeroStmt] bodyNative contract (YulTransaction.ofIR tx)
        storage observableSlots (Backends.freshNativeSwitchId reservedNames n0)
        nativeSwitchHasSelectorStore (4 + fn.params.length * 32)
        (by simpa [YulTransaction.ofIR] using hNonzero)
    rw [show (((fuel + 5) + 1) + suffix.length + 7) =
        (fuel + suffix.length + 1) + 12 by omega]
    exact hExec
  have hSwitch :=
    exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq
      (fuel + 5) selector (Backends.freshNativeSwitchId reservedNames n0)
      selector cases' [nativeRevertZeroZeroStmt] body' contract
      (YulTransaction.ofIR tx) storage initialEvents observableSlots
      EvmYul.Yul.Exception.Revert
      (projectResult (YulTransaction.ofIR tx) storage initialEvents
        (.error EvmYul.Yul.Exception.Revert))
      hSelector hCase hSelectorRange hTagsRange hBody rfl
  rw [show fuel + cases'.length + 18 =
    (fuel + 5) + cases'.length + 13 by omega]
  simpa [Compiler.Proofs.YulGeneration.selectorExpr] using hSwitch

set_option linter.unusedVariables false in
/-- Payable selector-hit calldata guard failure for a generated dispatcher.

When the selected function is payable but the ABI calldata is too short for
its parameter count, the selected switch-case prefix reverts before the user
body executes. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_payable_args_short_revert_projectResult_eq
    (fuel selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgsShort : ¬ fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      contractDispatcherExecResult (fuel + cases'.length + 23)
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        .error EvmYul.Yul.Exception.Revert ∧
      projectResult (YulTransaction.ofIR tx) storage initialEvents
          (.error EvmYul.Yul.Exception.Revert) =
        projectResult (YulTransaction.ofIR tx) storage initialEvents
          (.error EvmYul.Yul.Exception.Revert) := by
  obtain ⟨reservedNames, n0, cases', body', bodyStart, bodyEnd,
      hCase, hBodyLower, hDispatcherContinuation⟩ :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_projectResult_eq
      (fuel + 4) selector funcs fn inner functions (YulTransaction.ofIR tx)
      storage initialEvents observableSlots EvmYul.Yul.Exception.Revert
      (projectResult (YulTransaction.ofIR tx) storage initialEvents
        (.error EvmYul.Yul.Exception.Revert))
      hLower hSelector hFind
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
      hSelectorRange hFunctionSelectorsRange
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hPayable hBodyLower with
    ⟨bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hCalldataLt :
      4 + (YulTransaction.ofIR tx).args.length * 32 <
        4 + fn.params.length * 32 := by
    have hArgLt : tx.args.length < fn.params.length := by omega
    simpa [YulTransaction.ofIR_args] using
      (by omega :
        4 + tx.args.length * 32 < 4 + fn.params.length * 32)
  have hWholeBody :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (((fuel + 4) + 1) + suffix.length + 7)
          (.Block body') (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames n0)
            nativeSwitchHasSelectorStore) =
          .error EvmYul.Yul.Exception.Revert := by
    intro pre suffix _hCases
    rw [hBodyShape]
    have hExec :=
      exec_switchCaseBody_payable_calldata_revert_fuel
        (fuel + suffix.length + 1) bodyNative contract
        (YulTransaction.ofIR tx) storage observableSlots
        (Backends.freshNativeSwitchId reservedNames n0)
        nativeSwitchHasSelectorStore (4 + fn.params.length * 32)
        (by simpa [YulTransaction.ofIR_args] using hNoWrap)
        (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
        hCalldataLt
    simpa [contract, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hExec
  have hResult := hDispatcherContinuation hWholeBody rfl
  refine ⟨reservedNames, n0, cases', body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hCase, hBodyLower, hUserBodyLower, ?_⟩
  simpa [contract, Compiler.Proofs.YulGeneration.selectorExpr,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hResult

set_option linter.unusedVariables false in
/-- Non-payable selector-hit calldata guard failure for a generated dispatcher
after the zero-callvalue guard skips. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_nonpayable_args_short_revert_projectResult_eq
    (fuel selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx)
    (hZero : tx.msgValue % evmModulus = 0)
    (hArgsShort : ¬ fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      contractDispatcherExecResult (fuel + cases'.length + 24)
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        .error EvmYul.Yul.Exception.Revert ∧
      projectResult (YulTransaction.ofIR tx) storage initialEvents
          (.error EvmYul.Yul.Exception.Revert) =
        projectResult (YulTransaction.ofIR tx) storage initialEvents
          (.error EvmYul.Yul.Exception.Revert) := by
  obtain ⟨reservedNames, n0, cases', body', bodyStart, bodyEnd,
      hCase, hBodyLower, hDispatcherContinuation⟩ :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_projectResult_eq
      (fuel + 5) selector funcs fn inner functions (YulTransaction.ofIR tx)
      storage initialEvents observableSlots EvmYul.Yul.Exception.Revert
      (projectResult (YulTransaction.ofIR tx) storage initialEvents
        (.error EvmYul.Yul.Exception.Revert))
      hLower hSelector hFind
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
      hSelectorRange hFunctionSelectorsRange
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hNonPayable hBodyLower with
    ⟨bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hCalldataLt :
      4 + (YulTransaction.ofIR tx).args.length * 32 <
        4 + fn.params.length * 32 := by
    have hArgLt : tx.args.length < fn.params.length := by omega
    simpa [YulTransaction.ofIR_args] using
      (by omega :
        4 + tx.args.length * 32 < 4 + fn.params.length * 32)
  have hWholeBody :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (((fuel + 5) + 1) + suffix.length + 7)
          (.Block body') (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames n0)
            nativeSwitchHasSelectorStore) =
          .error EvmYul.Yul.Exception.Revert := by
    intro pre suffix _hCases
    rw [hBodyShape]
    have hExec :=
      exec_switchCaseBody_nonpayable_calldata_revert_fuel
        (fuel + suffix.length + 1) bodyNative contract
        (YulTransaction.ofIR tx) storage observableSlots
        (Backends.freshNativeSwitchId reservedNames n0)
        nativeSwitchHasSelectorStore (4 + fn.params.length * 32)
        (by simpa [YulTransaction.ofIR] using hZero)
        (by simpa [YulTransaction.ofIR_args] using hNoWrap)
        (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
        hCalldataLt
    simpa [contract, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hExec
  have hResult := hDispatcherContinuation hWholeBody rfl
  refine ⟨reservedNames, n0, cases', body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hCase, hBodyLower, hUserBodyLower, ?_⟩
  simpa [contract, Compiler.Proofs.YulGeneration.selectorExpr,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hResult

set_option linter.unusedVariables false in
/-- Exact-total-fuel companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_payable_args_short_revert_projectResult_eq`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_payable_args_short_revert_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgsShort : ¬ fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 23 ≤ fuel' →
        contractDispatcherExecResult fuel'
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .error EvmYul.Yul.Exception.Revert ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error EvmYul.Yul.Exception.Revert) =
          projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error EvmYul.Yul.Exception.Revert)) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hPayable hBodyLower with
    ⟨bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange fn hFn
  have hCalldataLt :
      4 + (YulTransaction.ofIR tx).args.length * 32 <
        4 + fn.params.length * 32 := by
    have hArgLt : tx.args.length < fn.params.length := by omega
    simpa [YulTransaction.ofIR_args] using
      (by omega :
        4 + tx.args.length * 32 < 4 + fn.params.length * 32)
  refine ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart,
    bodyEnd, userBodyStart, hLowerCases, hCase, hBodyLower,
    hUserBodyLower, ?_⟩
  intro hFuel
  let fuel := fuel' - (cases'.length + 23)
  have hFuelShape : fuel' = fuel + cases'.length + 23 := by
    dsimp [fuel]
    exact (Nat.sub_add_cancel hFuel).symm
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 4) reservedNames n0 cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult fuel'
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 17)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    rw [hFuelShape]
    have hDispatcherFuel :
        fuel + cases'.length + 23 =
          (fuel + 4) + cases'.length + 19 := by omega
    have hSwitchFuel :
        fuel + cases'.length + 17 =
          (fuel + 4) + cases'.length + 13 := by omega
    rw [hDispatcherFuel, hSwitchFuel]
    simpa [contract] using hPeel
  rw [hPeel']
  have hBody :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (((fuel + 4) + 1) + suffix.length + 7)
          (.Block body') (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames n0)
            nativeSwitchHasSelectorStore) =
        .error EvmYul.Yul.Exception.Revert := by
    intro pre suffix _hCases
    rw [hBodyShape]
    have hExec :=
      exec_switchCaseBody_payable_calldata_revert_fuel
        (fuel + suffix.length + 1) bodyNative contract
        (YulTransaction.ofIR tx) storage observableSlots
        (Backends.freshNativeSwitchId reservedNames n0)
        nativeSwitchHasSelectorStore (4 + fn.params.length * 32)
        (by simpa [YulTransaction.ofIR_args] using hNoWrap)
        (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
        hCalldataLt
    rw [show (((fuel + 4) + 1) + suffix.length + 7) =
        (fuel + suffix.length + 1) + 11 by omega]
    exact hExec
  have hSwitch :=
    exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq
      (fuel + 4) selector (Backends.freshNativeSwitchId reservedNames n0)
      selector cases' [nativeRevertZeroZeroStmt] body' contract
      (YulTransaction.ofIR tx) storage initialEvents observableSlots
      EvmYul.Yul.Exception.Revert
      (projectResult (YulTransaction.ofIR tx) storage initialEvents
        (.error EvmYul.Yul.Exception.Revert))
      hSelector hCase hSelectorRange hTagsRange hBody rfl
  rw [show fuel + cases'.length + 17 =
    (fuel + 4) + cases'.length + 13 by omega]
  simpa [Compiler.Proofs.YulGeneration.selectorExpr] using hSwitch

set_option linter.unusedVariables false in
/-- Exact-total-fuel companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_nonpayable_args_short_revert_projectResult_eq`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_nonpayable_args_short_revert_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx)
    (hZero : tx.msgValue % evmModulus = 0)
    (hArgsShort : ¬ fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 24 ≤ fuel' →
        contractDispatcherExecResult fuel'
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .error EvmYul.Yul.Exception.Revert ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error EvmYul.Yul.Exception.Revert) =
          projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error EvmYul.Yul.Exception.Revert)) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hNonPayable hBodyLower with
    ⟨bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange fn hFn
  have hCalldataLt :
      4 + (YulTransaction.ofIR tx).args.length * 32 <
        4 + fn.params.length * 32 := by
    have hArgLt : tx.args.length < fn.params.length := by omega
    simpa [YulTransaction.ofIR_args] using
      (by omega :
        4 + tx.args.length * 32 < 4 + fn.params.length * 32)
  refine ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart,
    bodyEnd, userBodyStart, hLowerCases, hCase, hBodyLower,
    hUserBodyLower, ?_⟩
  intro hFuel
  let fuel := fuel' - (cases'.length + 24)
  have hFuelShape : fuel' = fuel + cases'.length + 24 := by
    dsimp [fuel]
    exact (Nat.sub_add_cancel hFuel).symm
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 5) reservedNames n0 cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult fuel'
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 18)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    rw [hFuelShape]
    have hDispatcherFuel :
        fuel + cases'.length + 24 =
          (fuel + 5) + cases'.length + 19 := by omega
    have hSwitchFuel :
        fuel + cases'.length + 18 =
          (fuel + 5) + cases'.length + 13 := by omega
    rw [hDispatcherFuel, hSwitchFuel]
    simpa [contract] using hPeel
  rw [hPeel']
  have hBody :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (((fuel + 5) + 1) + suffix.length + 7)
          (.Block body') (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames n0)
            nativeSwitchHasSelectorStore) =
        .error EvmYul.Yul.Exception.Revert := by
    intro pre suffix _hCases
    rw [hBodyShape]
    have hExec :=
      exec_switchCaseBody_nonpayable_calldata_revert_fuel
        (fuel + suffix.length + 1) bodyNative contract
        (YulTransaction.ofIR tx) storage observableSlots
        (Backends.freshNativeSwitchId reservedNames n0)
        nativeSwitchHasSelectorStore (4 + fn.params.length * 32)
        (by simpa [YulTransaction.ofIR] using hZero)
        (by simpa [YulTransaction.ofIR_args] using hNoWrap)
        (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
        hCalldataLt
    rw [show (((fuel + 5) + 1) + suffix.length + 7) =
        (fuel + suffix.length + 1) + 12 by omega]
    exact hExec
  have hSwitch :=
    exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq
      (fuel + 5) selector (Backends.freshNativeSwitchId reservedNames n0)
      selector cases' [nativeRevertZeroZeroStmt] body' contract
      (YulTransaction.ofIR tx) storage initialEvents observableSlots
      EvmYul.Yul.Exception.Revert
      (projectResult (YulTransaction.ofIR tx) storage initialEvents
        (.error EvmYul.Yul.Exception.Revert))
      hSelector hCase hSelectorRange hTagsRange hBody rfl
  rw [show fuel + cases'.length + 18 =
    (fuel + 5) + cases'.length + 13 by omega]
  simpa [Compiler.Proofs.YulGeneration.selectorExpr] using hSwitch

set_option linter.unusedVariables false in
/-- Exact-total-fuel reserved-context companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_nonpayable_callvalue_revert_atFuel_projectResult_eq`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_nonpayable_callvalue_revert_withSwitchIds_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false)
    (hNonzero : tx.msgValue % evmModulus ≠ 0) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 24 ≤ fuel' →
        contractDispatcherExecResult fuel'
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .error EvmYul.Yul.Exception.Revert ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error EvmYul.Yul.Exception.Revert) =
          projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error EvmYul.Yul.Exception.Revert)) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hNonPayable hBodyLower with
    ⟨bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange fn hFn
  refine ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower, ?_⟩
  intro hFuel
  let fuel := fuel' - (cases'.length + 24)
  have hFuelShape : fuel' = fuel + cases'.length + 24 := by
    dsimp [fuel]
    exact (Nat.sub_add_cancel hFuel).symm
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 5) reservedNames switchStart cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult fuel'
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 18)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames switchStart) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    rw [hFuelShape]
    have hDispatcherFuel :
        fuel + cases'.length + 24 =
          (fuel + 5) + cases'.length + 19 := by omega
    have hSwitchFuel :
        fuel + cases'.length + 18 =
          (fuel + 5) + cases'.length + 13 := by omega
    rw [hDispatcherFuel, hSwitchFuel]
    simpa [contract] using hPeel
  rw [hPeel']
  have hBody :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (((fuel + 5) + 1) + suffix.length + 7)
          (.Block body') (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames switchStart)
            nativeSwitchHasSelectorStore) =
        .error EvmYul.Yul.Exception.Revert := by
    intro pre suffix _hCases
    rw [hBodyShape]
    have hExec :=
      exec_switchCaseBody_nonpayable_callvalue_revert_fuel
        (fuel + suffix.length + 1)
        [nativeRevertZeroZeroStmt] bodyNative contract (YulTransaction.ofIR tx)
        storage observableSlots
        (Backends.freshNativeSwitchId reservedNames switchStart)
        nativeSwitchHasSelectorStore (4 + fn.params.length * 32)
        (by simpa [YulTransaction.ofIR] using hNonzero)
    rw [show (((fuel + 5) + 1) + suffix.length + 7) =
        (fuel + suffix.length + 1) + 12 by omega]
    exact hExec
  have hSwitch :=
    exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq
      (fuel + 5) selector (Backends.freshNativeSwitchId reservedNames switchStart)
      selector cases' [nativeRevertZeroZeroStmt] body' contract
      (YulTransaction.ofIR tx) storage initialEvents observableSlots
      EvmYul.Yul.Exception.Revert
      (projectResult (YulTransaction.ofIR tx) storage initialEvents
        (.error EvmYul.Yul.Exception.Revert))
      hSelector hCase hSelectorRange hTagsRange hBody rfl
  rw [show fuel + cases'.length + 18 =
    (fuel + 5) + cases'.length + 13 by omega]
  simpa [Compiler.Proofs.YulGeneration.selectorExpr] using hSwitch

set_option linter.unusedVariables false in
/-- Exact-total-fuel reserved-context companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_payable_args_short_revert_atFuel_projectResult_eq`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_payable_args_short_revert_withSwitchIds_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgsShort : ¬ fn.params.length ≤ tx.args.length) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 23 ≤ fuel' →
        contractDispatcherExecResult fuel'
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .error EvmYul.Yul.Exception.Revert ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error EvmYul.Yul.Exception.Revert) =
          projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error EvmYul.Yul.Exception.Revert)) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hPayable hBodyLower with
    ⟨bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange fn hFn
  have hCalldataLt :
      4 + (YulTransaction.ofIR tx).args.length * 32 <
        4 + fn.params.length * 32 := by
    have hArgLt : tx.args.length < fn.params.length := by omega
    simpa [YulTransaction.ofIR_args] using
      (by omega :
        4 + tx.args.length * 32 < 4 + fn.params.length * 32)
  refine ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower, ?_⟩
  intro hFuel
  let fuel := fuel' - (cases'.length + 23)
  have hFuelShape : fuel' = fuel + cases'.length + 23 := by
    dsimp [fuel]
    exact (Nat.sub_add_cancel hFuel).symm
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 4) reservedNames switchStart cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult fuel'
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 17)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames switchStart) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    rw [hFuelShape]
    have hDispatcherFuel :
        fuel + cases'.length + 23 =
          (fuel + 4) + cases'.length + 19 := by omega
    have hSwitchFuel :
        fuel + cases'.length + 17 =
          (fuel + 4) + cases'.length + 13 := by omega
    rw [hDispatcherFuel, hSwitchFuel]
    simpa [contract] using hPeel
  rw [hPeel']
  have hBody :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (((fuel + 4) + 1) + suffix.length + 7)
          (.Block body') (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames switchStart)
            nativeSwitchHasSelectorStore) =
        .error EvmYul.Yul.Exception.Revert := by
    intro pre suffix _hCases
    rw [hBodyShape]
    have hExec :=
      exec_switchCaseBody_payable_calldata_revert_fuel
        (fuel + suffix.length + 1) bodyNative contract
        (YulTransaction.ofIR tx) storage observableSlots
        (Backends.freshNativeSwitchId reservedNames switchStart)
        nativeSwitchHasSelectorStore (4 + fn.params.length * 32)
        (by simpa [YulTransaction.ofIR_args] using hNoWrap)
        (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
        hCalldataLt
    rw [show (((fuel + 4) + 1) + suffix.length + 7) =
        (fuel + suffix.length + 1) + 11 by omega]
    exact hExec
  have hSwitch :=
    exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq
      (fuel + 4) selector (Backends.freshNativeSwitchId reservedNames switchStart)
      selector cases' [nativeRevertZeroZeroStmt] body' contract
      (YulTransaction.ofIR tx) storage initialEvents observableSlots
      EvmYul.Yul.Exception.Revert
      (projectResult (YulTransaction.ofIR tx) storage initialEvents
        (.error EvmYul.Yul.Exception.Revert))
      hSelector hCase hSelectorRange hTagsRange hBody rfl
  rw [show fuel + cases'.length + 17 =
    (fuel + 4) + cases'.length + 13 by omega]
  simpa [Compiler.Proofs.YulGeneration.selectorExpr] using hSwitch

set_option linter.unusedVariables false in
/-- Exact-total-fuel reserved-context companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_nonpayable_args_short_revert_atFuel_projectResult_eq`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_nonpayable_args_short_revert_withSwitchIds_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx)
    (hZero : tx.msgValue % evmModulus = 0)
    (hArgsShort : ¬ fn.params.length ≤ tx.args.length) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 24 ≤ fuel' →
        contractDispatcherExecResult fuel'
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .error EvmYul.Yul.Exception.Revert ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error EvmYul.Yul.Exception.Revert) =
          projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.error EvmYul.Yul.Exception.Revert)) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hNonPayable hBodyLower with
    ⟨bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange fn hFn
  have hCalldataLt :
      4 + (YulTransaction.ofIR tx).args.length * 32 <
        4 + fn.params.length * 32 := by
    have hArgLt : tx.args.length < fn.params.length := by omega
    simpa [YulTransaction.ofIR_args] using
      (by omega :
        4 + tx.args.length * 32 < 4 + fn.params.length * 32)
  refine ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower, ?_⟩
  intro hFuel
  let fuel := fuel' - (cases'.length + 24)
  have hFuelShape : fuel' = fuel + cases'.length + 24 := by
    dsimp [fuel]
    exact (Nat.sub_add_cancel hFuel).symm
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 5) reservedNames switchStart cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult fuel'
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 18)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames switchStart) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    rw [hFuelShape]
    have hDispatcherFuel :
        fuel + cases'.length + 24 =
          (fuel + 5) + cases'.length + 19 := by omega
    have hSwitchFuel :
        fuel + cases'.length + 18 =
          (fuel + 5) + cases'.length + 13 := by omega
    rw [hDispatcherFuel, hSwitchFuel]
    simpa [contract] using hPeel
  rw [hPeel']
  have hBody :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (((fuel + 5) + 1) + suffix.length + 7)
          (.Block body') (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames switchStart)
            nativeSwitchHasSelectorStore) =
        .error EvmYul.Yul.Exception.Revert := by
    intro pre suffix _hCases
    rw [hBodyShape]
    have hExec :=
      exec_switchCaseBody_nonpayable_calldata_revert_fuel
        (fuel + suffix.length + 1) bodyNative contract
        (YulTransaction.ofIR tx) storage observableSlots
        (Backends.freshNativeSwitchId reservedNames switchStart)
        nativeSwitchHasSelectorStore (4 + fn.params.length * 32)
        (by simpa [YulTransaction.ofIR] using hZero)
        (by simpa [YulTransaction.ofIR_args] using hNoWrap)
        (DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
        hCalldataLt
    rw [show (((fuel + 5) + 1) + suffix.length + 7) =
        (fuel + suffix.length + 1) + 12 by omega]
    exact hExec
  have hSwitch :=
    exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq
      (fuel + 5) selector (Backends.freshNativeSwitchId reservedNames switchStart)
      selector cases' [nativeRevertZeroZeroStmt] body' contract
      (YulTransaction.ofIR tx) storage initialEvents observableSlots
      EvmYul.Yul.Exception.Revert
      (projectResult (YulTransaction.ofIR tx) storage initialEvents
        (.error EvmYul.Yul.Exception.Revert))
      hSelector hCase hSelectorRange hTagsRange hBody rfl
  rw [show fuel + cases'.length + 18 =
    (fuel + 5) + cases'.length + 13 by omega]
  simpa [Compiler.Proofs.YulGeneration.selectorExpr] using hSwitch

/-- Generated-prefix success variant for payable selector hits. The public
    selected-body premises are over the lowered user body `fn.body`, not over
    the generated `switchCaseBody fn` wrapper. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_payable_generated_prefix_projectResult_eq
    (fuel selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots
              (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult (fuel + cases'.length + 23)
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .ok final ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange _ hFn
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 4) reservedNames n0 cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult (fuel + cases'.length + 23)
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 17)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    simpa [contract, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hPeel
  have hBlock :=
    exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_payable_generated_prefix
      fuel selector (Backends.freshNativeSwitchId reservedNames n0) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage
      initialEvents observableSlots final nativeYul reservedNames bodyStart
      bodyEnd fn hSelector hCase hSelectorRange hTagsRange hBodyLower
      hPayable hguards hNoWrap hArgs
  rcases hBlock with ⟨bodyNative, userBodyStart, hUserBodyLower, hDispatcherContinuation⟩
  refine ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart,
    bodyEnd, userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower,
    ?_⟩
  intro hUserBody hPreservesUser hProject
  rw [hPeel']
  have hResult := hDispatcherContinuation hUserBody hPreservesUser hProject
  simpa [contract, Compiler.Proofs.YulGeneration.selectorExpr,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hResult

/-- Generated-prefix success variant for non-payable selector hits. The public
    selected-body premises are over the lowered user body `fn.body`, not over
    the generated `switchCaseBody fn` wrapper. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_nonpayable_generated_prefix_projectResult_eq
    (fuel selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots
              (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult (fuel + cases'.length + 24)
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .ok final ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange _ hFn
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 5) reservedNames n0 cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult (fuel + cases'.length + 24)
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 18)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    simpa [contract, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hPeel
  have hBlock :=
    exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_nonpayable_generated_prefix
      fuel selector (Backends.freshNativeSwitchId reservedNames n0) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage
      initialEvents observableSlots final nativeYul reservedNames bodyStart
      bodyEnd fn hSelector hCase hSelectorRange hTagsRange hBodyLower
      hNonPayable hguards hNoWrap hArgs
  rcases hBlock with ⟨bodyNative, userBodyStart, hUserBodyLower, hDispatcherContinuation⟩
  refine ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower, ?_⟩
  intro hUserBody hPreservesUser hProject
  rw [hPeel']
  have hResult := hDispatcherContinuation hUserBody hPreservesUser hProject
  simpa [Compiler.Proofs.YulGeneration.selectorExpr, contract, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hResult

/-- Reserved-context generated-prefix success variant for payable selector hits.
    The selected-body premises are over the lowered user body `fn.body`, not
    over the generated `switchCaseBody fn` wrapper. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_payable_withSwitchIds_generated_prefix_projectResult_eq
    (fuel selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots
              (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult (fuel + cases'.length + 23)
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .ok final ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange _ hFn
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 4) reservedNames switchStart cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult (fuel + cases'.length + 23)
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 17)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames switchStart) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    simpa [contract, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hPeel
  have hBlock :=
    exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_payable_generated_prefix
      fuel selector (Backends.freshNativeSwitchId reservedNames switchStart)
      selector cases' [nativeRevertZeroZeroStmt] body' contract tx storage
      initialEvents observableSlots final nativeYul reservedNames bodyStart
      bodyEnd fn hSelector hCase hSelectorRange hTagsRange hBodyLower
      hPayable hguards hNoWrap hArgs
  rcases hBlock with ⟨bodyNative, userBodyStart, hUserBodyLower, hDispatcherContinuation⟩
  refine ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower, ?_⟩
  intro hUserBody hPreservesUser hProject
  rw [hPeel']
  have hResult := hDispatcherContinuation hUserBody hPreservesUser hProject
  simpa [Compiler.Proofs.YulGeneration.selectorExpr, contract, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hResult

/-- Reserved-context generated-prefix success variant for non-payable selector
    hits. The selected-body premises are over the lowered user body `fn.body`,
    not over the generated `switchCaseBody fn` wrapper. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_nonpayable_withSwitchIds_generated_prefix_projectResult_eq
    (fuel selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots
              (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult (fuel + cases'.length + 24)
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .ok final ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange _ hFn
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 5) reservedNames switchStart cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult (fuel + cases'.length + 24)
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 18)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames switchStart) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    simpa [contract, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hPeel
  have hBlock :=
    exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_nonpayable_generated_prefix
      fuel selector (Backends.freshNativeSwitchId reservedNames switchStart)
      selector cases' [nativeRevertZeroZeroStmt] body' contract tx storage
      initialEvents observableSlots final nativeYul reservedNames bodyStart
      bodyEnd fn hSelector hCase hSelectorRange hTagsRange hBodyLower
      hNonPayable hguards hNoWrap hArgs
  rcases hBlock with ⟨bodyNative, userBodyStart, hUserBodyLower, hDispatcherContinuation⟩
  refine ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower, ?_⟩
  intro hUserBody hPreservesUser hProject
  rw [hPeel']
  have hResult := hDispatcherContinuation hUserBody hPreservesUser hProject
  simpa [Compiler.Proofs.YulGeneration.selectorExpr, contract, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hResult

/-- Exact-total-fuel companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_payable_generated_prefix_projectResult_eq`.

The selected-body execution premise remains over the lowered user body
`fn.body`, while the dispatcher result is stated at an externally supplied
total fuel `fuel'`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_payable_generated_prefix_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 23 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel' - (cases'.length + 23)) +
              suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots
              (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult fuel'
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .ok final ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange _ hFn
  have hBlock :
      ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (userBodyStart : Nat),
        Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
          fn.body = .ok (bodyNative, bodyEnd) ∧
        ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
            EvmYul.Yul.exec ((fuel' - (cases'.length + 23)) +
                suffix.length + 10) (.Block bodyNative)
              (some contract)
              (nativeSwitchStoreMarkedPrefixStateForId contract
                (YulTransaction.ofIR tx) storage observableSlots
                (Backends.freshNativeSwitchId reservedNames n0)
                nativeSwitchHasSelectorStore) = .ok final) →
          (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
            NativeBlockPreservesWord
              (Backends.nativeSwitchMatchedTempName
                (Backends.freshNativeSwitchId reservedNames n0))
              (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
          projectResult (YulTransaction.ofIR tx) storage initialEvents
              (.ok (final, [])) = nativeYul →
          EvmYul.Yul.exec ((fuel' - (cases'.length + 23)) + cases'.length + 17)
              (.Block [Backends.lowerNativeSwitchBlock
                Compiler.Proofs.YulGeneration.selectorExpr
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
                storage observableSlots).insert "__has_selector"
                (EvmYul.UInt256.ofNat 1)) =
            .ok final ∧
          projectResult (YulTransaction.ofIR tx) storage initialEvents
              (.ok (final, [])) = nativeYul) := by
    simpa [contract] using
      (exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_payable_generated_prefix
        (fuel' - (cases'.length + 23)) selector
        (Backends.freshNativeSwitchId reservedNames n0) selector
        cases' [nativeRevertZeroZeroStmt] body' contract tx storage
        initialEvents observableSlots final nativeYul reservedNames bodyStart
        bodyEnd fn hSelector hCase hSelectorRange hTagsRange hBodyLower
        hPayable hguards hNoWrap hArgs)
  rcases hBlock with ⟨bodyNative, userBodyStart, hUserBodyLower, hDispatcherContinuation⟩
  refine ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower, ?_⟩
  intro hFuel hUserBody hPreservesUser hProject
  let fuel := fuel' - (cases'.length + 23)
  have hFuelShape : fuel' = fuel + cases'.length + 23 := by
    dsimp [fuel]
    exact (Nat.sub_add_cancel hFuel).symm
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 4) reservedNames n0 cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult fuel'
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 17)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    rw [hFuelShape]
    have hDispatcherFuel :
        fuel + cases'.length + 23 =
          (fuel + 4) + cases'.length + 19 := by
      omega
    have hSwitchFuel :
        fuel + cases'.length + 17 =
          (fuel + 4) + cases'.length + 13 := by
      omega
    rw [hDispatcherFuel, hSwitchFuel]
    simpa [contract] using hPeel
  rw [hPeel']
  have hUserBody' :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
          (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames n0)
            nativeSwitchHasSelectorStore) = .ok final := by
    intro pre suffix hCases
    simpa [fuel, contract, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hUserBody pre suffix hCases
  have hResult := hDispatcherContinuation hUserBody' hPreservesUser hProject
  simpa [contract, fuel, Compiler.Proofs.YulGeneration.selectorExpr,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hResult

/-- Exact-total-fuel companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_nonpayable_generated_prefix_projectResult_eq`.

The selected-body execution premise remains over the lowered user body
`fn.body`, while the dispatcher result is stated at an externally supplied
total fuel `fuel'`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_nonpayable_generated_prefix_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 24 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel' - (cases'.length + 24)) +
              suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots
              (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult fuel'
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .ok final ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange _ hFn
  have hBlock :
      ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (userBodyStart : Nat),
        Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
          fn.body = .ok (bodyNative, bodyEnd) ∧
        ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
            EvmYul.Yul.exec ((fuel' - (cases'.length + 24)) +
                suffix.length + 10) (.Block bodyNative)
              (some contract)
              (nativeSwitchStoreMarkedPrefixStateForId contract
                (YulTransaction.ofIR tx) storage observableSlots
                (Backends.freshNativeSwitchId reservedNames n0)
                nativeSwitchHasSelectorStore) = .ok final) →
          (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
            NativeBlockPreservesWord
              (Backends.nativeSwitchMatchedTempName
                (Backends.freshNativeSwitchId reservedNames n0))
              (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
          projectResult (YulTransaction.ofIR tx) storage initialEvents
              (.ok (final, [])) = nativeYul →
          EvmYul.Yul.exec ((fuel' - (cases'.length + 24)) + cases'.length + 18)
              (.Block [Backends.lowerNativeSwitchBlock
                Compiler.Proofs.YulGeneration.selectorExpr
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
                storage observableSlots).insert "__has_selector"
                (EvmYul.UInt256.ofNat 1)) =
            .ok final ∧
          projectResult (YulTransaction.ofIR tx) storage initialEvents
              (.ok (final, [])) = nativeYul) := by
    simpa [contract] using
      (exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_nonpayable_generated_prefix
        (fuel' - (cases'.length + 24)) selector
        (Backends.freshNativeSwitchId reservedNames n0) selector
        cases' [nativeRevertZeroZeroStmt] body' contract tx storage
        initialEvents observableSlots final nativeYul reservedNames bodyStart
        bodyEnd fn hSelector hCase hSelectorRange hTagsRange hBodyLower
        hNonPayable hguards hNoWrap hArgs)
  rcases hBlock with ⟨bodyNative, userBodyStart, hUserBodyLower, hDispatcherContinuation⟩
  refine ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower, ?_⟩
  intro hFuel hUserBody hPreservesUser hProject
  let fuel := fuel' - (cases'.length + 24)
  have hFuelShape : fuel' = fuel + cases'.length + 24 := by
    dsimp [fuel]
    exact (Nat.sub_add_cancel hFuel).symm
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 5) reservedNames n0 cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult fuel'
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 18)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    rw [hFuelShape]
    have hDispatcherFuel :
        fuel + cases'.length + 24 =
          (fuel + 5) + cases'.length + 19 := by
      omega
    have hSwitchFuel :
        fuel + cases'.length + 18 =
          (fuel + 5) + cases'.length + 13 := by
      omega
    rw [hDispatcherFuel, hSwitchFuel]
    simpa [contract] using hPeel
  rw [hPeel']
  have hUserBody' :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
          (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames n0)
            nativeSwitchHasSelectorStore) = .ok final := by
    intro pre suffix hCases
    simpa [fuel, contract, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hUserBody pre suffix hCases
  have hResult := hDispatcherContinuation hUserBody' hPreservesUser hProject
  simpa [contract, fuel, Compiler.Proofs.YulGeneration.selectorExpr,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hResult

/-- Exact-total-fuel reserved-context companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_payable_withSwitchIds_generated_prefix_projectResult_eq`.

The selected-body execution premise remains over the lowered user body
`fn.body`, while the dispatcher result is stated at an externally supplied
total fuel `fuel'`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_payable_withSwitchIds_generated_prefix_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 23 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel' - (cases'.length + 23)) +
              suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots
              (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult fuel'
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .ok final ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange _ hFn
  have hBlock :
      ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (userBodyStart : Nat),
        Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
          fn.body = .ok (bodyNative, bodyEnd) ∧
        ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
            EvmYul.Yul.exec ((fuel' - (cases'.length + 23)) +
                suffix.length + 10) (.Block bodyNative)
              (some contract)
              (nativeSwitchStoreMarkedPrefixStateForId contract
                (YulTransaction.ofIR tx) storage observableSlots
                (Backends.freshNativeSwitchId reservedNames switchStart)
                nativeSwitchHasSelectorStore) = .ok final) →
          (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
            NativeBlockPreservesWord
              (Backends.nativeSwitchMatchedTempName
                (Backends.freshNativeSwitchId reservedNames switchStart))
              (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
          projectResult (YulTransaction.ofIR tx) storage initialEvents
              (.ok (final, [])) = nativeYul →
          EvmYul.Yul.exec ((fuel' - (cases'.length + 23)) + cases'.length + 17)
              (.Block [Backends.lowerNativeSwitchBlock
                Compiler.Proofs.YulGeneration.selectorExpr
                (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
                storage observableSlots).insert "__has_selector"
                (EvmYul.UInt256.ofNat 1)) =
            .ok final ∧
          projectResult (YulTransaction.ofIR tx) storage initialEvents
              (.ok (final, [])) = nativeYul) := by
    simpa [contract] using
      (exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_payable_generated_prefix
        (fuel' - (cases'.length + 23)) selector
        (Backends.freshNativeSwitchId reservedNames switchStart) selector
        cases' [nativeRevertZeroZeroStmt] body' contract tx storage
        initialEvents observableSlots final nativeYul reservedNames bodyStart
        bodyEnd fn hSelector hCase hSelectorRange hTagsRange hBodyLower
        hPayable hguards hNoWrap hArgs)
  rcases hBlock with ⟨bodyNative, userBodyStart, hUserBodyLower, hDispatcherContinuation⟩
  refine ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower, ?_⟩
  intro hFuel hUserBody hPreservesUser hProject
  let fuel := fuel' - (cases'.length + 23)
  have hFuelShape : fuel' = fuel + cases'.length + 23 := by
    dsimp [fuel]
    exact (Nat.sub_add_cancel hFuel).symm
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 4) reservedNames switchStart cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult fuel'
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 17)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames switchStart) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    rw [hFuelShape]
    have hDispatcherFuel :
        fuel + cases'.length + 23 =
          (fuel + 4) + cases'.length + 19 := by
      omega
    have hSwitchFuel :
        fuel + cases'.length + 17 =
          (fuel + 4) + cases'.length + 13 := by
      omega
    rw [hDispatcherFuel, hSwitchFuel]
    simpa [contract] using hPeel
  rw [hPeel']
  have hUserBody' :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
          (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames switchStart)
            nativeSwitchHasSelectorStore) = .ok final := by
    intro pre suffix hCases
    simpa [fuel, contract, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hUserBody pre suffix hCases
  have hResult := hDispatcherContinuation hUserBody' hPreservesUser hProject
  simpa [Compiler.Proofs.YulGeneration.selectorExpr, contract, fuel, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]
    using hResult

/-- Exact-total-fuel reserved-context companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_nonpayable_withSwitchIds_generated_prefix_projectResult_eq`.

The selected-body execution premise remains over the lowered user body
`fn.body`, while the dispatcher result is stated at an externally supplied
total fuel `fuel'`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_nonpayable_withSwitchIds_generated_prefix_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector =
        (YulTransaction.ofIR tx).functionSelector %
          Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd userBodyStart : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 24 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel' - (cases'.length + 24)) +
              suffix.length + 10) (.Block bodyNative)
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract
              (YulTransaction.ofIR tx) storage observableSlots
              (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult fuel'
            contract
            (initialState contract (YulTransaction.ofIR tx) storage
              observableSlots) =
          .ok final ∧
        projectResult (YulTransaction.ofIR tx) storage initialEvents
            (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange _ hFn
  have hBlock :
      ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (userBodyStart : Nat),
        Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
          fn.body = .ok (bodyNative, bodyEnd) ∧
        ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
            EvmYul.Yul.exec ((fuel' - (cases'.length + 24)) +
                suffix.length + 10) (.Block bodyNative)
              (some contract)
              (nativeSwitchStoreMarkedPrefixStateForId contract
                (YulTransaction.ofIR tx) storage observableSlots
                (Backends.freshNativeSwitchId reservedNames switchStart)
                nativeSwitchHasSelectorStore) = .ok final) →
          (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
            NativeBlockPreservesWord
              (Backends.nativeSwitchMatchedTempName
                (Backends.freshNativeSwitchId reservedNames switchStart))
              (EvmYul.UInt256.ofNat 1) bodyNative (some contract)) →
          projectResult (YulTransaction.ofIR tx) storage initialEvents
              (.ok (final, [])) = nativeYul →
          EvmYul.Yul.exec ((fuel' - (cases'.length + 24)) + cases'.length + 18)
              (.Block [Backends.lowerNativeSwitchBlock
                Compiler.Proofs.YulGeneration.selectorExpr
                (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
                storage observableSlots).insert "__has_selector"
                (EvmYul.UInt256.ofNat 1)) =
            .ok final ∧
          projectResult (YulTransaction.ofIR tx) storage initialEvents
              (.ok (final, [])) = nativeYul) := by
    simpa [contract] using
      (exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_nonpayable_generated_prefix
        (fuel' - (cases'.length + 24)) selector
        (Backends.freshNativeSwitchId reservedNames switchStart) selector
        cases' [nativeRevertZeroZeroStmt] body' contract tx storage
        initialEvents observableSlots final nativeYul reservedNames bodyStart
        bodyEnd fn hSelector hCase hSelectorRange hTagsRange hBodyLower
        hNonPayable hguards hNoWrap hArgs)
  rcases hBlock with ⟨bodyNative, userBodyStart, hUserBodyLower, hDispatcherContinuation⟩
  refine ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower, ?_⟩
  intro hFuel hUserBody hPreservesUser hProject
  let fuel := fuel' - (cases'.length + 24)
  have hFuelShape : fuel' = fuel + cases'.length + 24 := by
    dsimp [fuel]
    exact (Nat.sub_add_cancel hFuel).symm
  have hPeel :=
    contractDispatcherExecResult_buildSwitch_noFallback_noReceive_peel
      (fuel + 5) reservedNames switchStart cases' body1 inner functions
      (YulTransaction.ofIR tx) storage observableSlots hInner
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hPeel' :
      contractDispatcherExecResult fuel'
          contract
          (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 18)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames switchStart) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract (YulTransaction.ofIR tx)
            storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    rw [hFuelShape]
    have hDispatcherFuel :
        fuel + cases'.length + 24 =
          (fuel + 5) + cases'.length + 19 := by
      omega
    have hSwitchFuel :
        fuel + cases'.length + 18 =
          (fuel + 5) + cases'.length + 13 := by
      omega
    rw [hDispatcherFuel, hSwitchFuel]
    simpa [contract] using hPeel
  rw [hPeel']
  have hUserBody' :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
          (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract
            (YulTransaction.ofIR tx) storage observableSlots
            (Backends.freshNativeSwitchId reservedNames switchStart)
            nativeSwitchHasSelectorStore) = .ok final := by
    intro pre suffix hCases
    simpa [fuel, contract, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hUserBody pre suffix hCases
  have hResult := hDispatcherContinuation hUserBody' hPreservesUser hProject
  simpa [Compiler.Proofs.YulGeneration.selectorExpr, contract, fuel, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]
    using hResult

/-- Exact-total-fuel companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_projectResult_eq`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) +
              suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .error err) →
        projectResult tx storage initialEvents (.error err) = nativeYul →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .error err ∧
        projectResult tx storage initialEvents (.error err) = nativeYul) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  refine ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
    ?_, ?_, ?_, ?_⟩
  · exact hLowerCases
  · exact hCase
  · exact hBodyLower
  · intro hFuel hBody hProject
    let fuel := fuel' - (cases'.length + 19)
    have hFuelShape : fuel' = fuel + cases'.length + 19 := by
      dsimp [fuel]
      exact (Nat.sub_add_cancel hFuel).symm
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hBody' :
        ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .error err := by
      intro pre suffix hcases
      simpa [fuel, contract, Nat.add_assoc] using hBody pre suffix hcases
    have hPeel :
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      rw [hFuelShape]
      have hPeelStructural :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
        let contract' : EvmYul.Yul.Ast.YulContract :=
          { dispatcher := .Block [.Block inner], functions := functions }
        have hFuelShape' :
            fuel + cases'.length + 19 =
              Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
          omega
        have hDispatcherPeel :
            contractDispatcherExecResult (fuel + cases'.length + 19)
                contract' (initialState contract' tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract')
                (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
          rw [hFuelShape']
          change
            contractDispatcherExecResult
                (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
                { dispatcher := .Block [.Block inner], functions := functions }
                (initialState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner)
                (some { dispatcher := .Block [.Block inner], functions := functions })
                (nativeSwitchInitialOkState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots)
          rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
            (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
            tx storage observableSlots]
          rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (nativeSwitchInitialOkState
              { dispatcher := .Block [.Block inner], functions := functions }
              tx storage observableSlots)]
        calc
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots)
              = EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block inner) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
          _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block
                  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                      (some
                        (Backends.lowerExprNative
                          (YulExpr.call "iszero"
                            [YulExpr.call "lt"
                              [YulExpr.call "calldatasize" [],
                               YulExpr.lit 4]]))),
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                      body1,
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                      [Backends.lowerNativeSwitchBlock
                        (YulExpr.call "shr"
                          [YulExpr.lit Compiler.Constants.selectorShift,
                           YulExpr.call "calldataload" [YulExpr.lit 0]])
                        (Backends.freshNativeSwitchId reservedNames n0) cases'
                        [nativeRevertZeroZeroStmt]]])
                (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := by
              exact congrArg
                (fun body =>
                  EvmYul.Yul.exec (fuel + cases'.length + 17)
                    (.Block body) (some contract)
                    (nativeSwitchInitialOkState contract tx storage observableSlots))
                hInner
          _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
                (.Block
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames n0) cases'
                    [nativeRevertZeroZeroStmt]])
                (some contract)
                ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                  "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
              have hExec :=
                exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                  (fuel + cases'.length + 5) contract tx storage observableSlots
                  "__has_selector" body1
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames n0) cases'
                    [nativeRevertZeroZeroStmt]]
                  hNoWrap
              simpa only [Nat.add_assoc] using hExec
      exact hPeelStructural
    constructor
    · rw [hPeel]
      exact (exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq
        fuel selector (Backends.freshNativeSwitchId reservedNames n0) selector
        cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
        observableSlots err nativeYul hSelector hCase hSelectorRange hTagsRange
        hBody' hProject).1
    · exact hProject

/-- Artifact-fixed companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_atFuel_projectResult_eq`.

This no-reserved-context variant exposes the selected switch-case artifacts
before choosing the concrete error/result pair, matching the reserved-context
artifact theorem below. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_atFuel_artifact_projectResult_eq
    (fuel' selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (∀ (err : EvmYul.Yul.Exception) (nativeYul : YulResult),
        cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) +
              suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .error err) →
        projectResult tx storage initialEvents (.error err) = nativeYul →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .error err ∧
        projectResult tx storage initialEvents (.error err) = nativeYul) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  refine ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
    hLowerCases, hCase, hBodyLower, ?_⟩
  intro err nativeYul hFuel hBody hProject
  let fuel := fuel' - (cases'.length + 19)
  have hFuelShape : fuel' = fuel + cases'.length + 19 := by
    dsimp [fuel]
    exact (Nat.sub_add_cancel hFuel).symm
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange fn hFn
  have hBody' :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
          (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
            observableSlots (Backends.freshNativeSwitchId reservedNames n0)
            nativeSwitchHasSelectorStore) = .error err := by
    intro pre suffix hcases
    simpa [fuel, contract, Nat.add_assoc] using hBody pre suffix hcases
  have hPeel :
      contractDispatcherExecResult fuel'
          contract (initialState contract tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 13)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
            "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
    rw [hFuelShape]
    have hPeelStructural :
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      let contract' : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      have hFuelShape' :
          fuel + cases'.length + 19 =
            Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
        omega
      have hDispatcherPeel :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract' (initialState contract' tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner) (some contract')
              (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
        rw [hFuelShape']
        change
          contractDispatcherExecResult
              (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
              { dispatcher := .Block [.Block inner], functions := functions }
              (initialState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner)
              (some { dispatcher := .Block [.Block inner], functions := functions })
              (nativeSwitchInitialOkState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots)
        rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
          (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
          tx storage observableSlots]
        rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
          (some { dispatcher := .Block [.Block inner], functions := functions })
          (nativeSwitchInitialOkState
            { dispatcher := .Block [.Block inner], functions := functions }
            tx storage observableSlots)]
      calc
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots)
            = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
        _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block
                [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                    (some
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero"
                          [YulExpr.call "lt"
                            [YulExpr.call "calldatasize" [],
                             YulExpr.lit 4]]))),
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative
                      (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                    body1,
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                    [Backends.lowerNativeSwitchBlock
                      (YulExpr.call "shr"
                        [YulExpr.lit Compiler.Constants.selectorShift,
                         YulExpr.call "calldataload" [YulExpr.lit 0]])
                      (Backends.freshNativeSwitchId reservedNames n0) cases'
                      [nativeRevertZeroZeroStmt]]])
              (some contract)
              (nativeSwitchInitialOkState contract tx storage observableSlots) := by
            exact congrArg
              (fun body =>
                EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block body) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots))
              hInner
        _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
            have hExec :=
              exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                (fuel + cases'.length + 5) contract tx storage observableSlots
                "__has_selector" body1
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]]
                hNoWrap
            simpa only [Nat.add_assoc] using hExec
    exact hPeelStructural
  constructor
  · rw [hPeel]
    exact (exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq
      fuel selector (Backends.freshNativeSwitchId reservedNames n0) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots err nativeYul hSelector hCase hSelectorRange hTagsRange
      hBody' hProject).1
  · exact hProject

/-- Generic selector-hit native execution package for a no-fallback/no-receive
generated dispatcher when the selected native body finishes normally.

The selected-body execution, switch-temporary freshness, matched-flag
preservation, and final-state projection remain explicit premises; this theorem
packages the dispatcher/prologue/lazy-switch execution around them. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_projectResult_eq
    (fuel selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      ((Backends.nativeSwitchTempsFreshForNativeBodies
          (Backends.freshNativeSwitchId reservedNames n0) cases'
          [nativeRevertZeroZeroStmt]) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ stmt, stmt ∈ body' →
          Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames n0) ∉
            Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) stmt (some contract)) →
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          .ok final ∧
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  refine ⟨reservedNames, n0, cases', body', bodyStart, bodyEnd, ?_, ?_, ?_⟩
  · exact hCase
  · exact hBodyLower
  · intro hFresh hBody hStmtPreserves hProject
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hPeel :
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      let contract' : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      have hFuelShape :
          fuel + cases'.length + 19 =
            Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
        omega
      have hDispatcherPeel :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract' (initialState contract' tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner) (some contract')
              (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
        rw [hFuelShape]
        change
          contractDispatcherExecResult
              (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
              { dispatcher := .Block [.Block inner], functions := functions }
              (initialState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner)
              (some { dispatcher := .Block [.Block inner], functions := functions })
              (nativeSwitchInitialOkState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots)
        rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
          (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
          tx storage observableSlots]
        rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
          (some { dispatcher := .Block [.Block inner], functions := functions })
          (nativeSwitchInitialOkState
            { dispatcher := .Block [.Block inner], functions := functions }
            tx storage observableSlots)]
      calc
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots)
            = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
        _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block
                [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                    (some
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero"
                          [YulExpr.call "lt"
                            [YulExpr.call "calldatasize" [],
                             YulExpr.lit 4]]))),
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative
                      (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                    body1,
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                    [Backends.lowerNativeSwitchBlock
                      (YulExpr.call "shr"
                        [YulExpr.lit Compiler.Constants.selectorShift,
                         YulExpr.call "calldataload" [YulExpr.lit 0]])
                      (Backends.freshNativeSwitchId reservedNames n0) cases'
                      [nativeRevertZeroZeroStmt]]])
              (some contract)
              (nativeSwitchInitialOkState contract tx storage observableSlots) := by
            exact congrArg
              (fun body =>
                EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block body) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots))
              hInner
        _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
            have hExec :=
              exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                (fuel + cases'.length + 5) contract tx storage observableSlots
                "__has_selector" body1
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]]
                hNoWrap
            simpa only [Nat.add_assoc] using hExec
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq
      fuel selector (Backends.freshNativeSwitchId reservedNames n0) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots final nativeYul hSelector hCase hSelectorRange hTagsRange
      hFresh hBody hStmtPreserves hProject

/-- Block-preservation companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_projectResult_eq`.

This packages the dispatcher/prologue/lazy-switch execution while taking the
selected-body matched-word preservation as a block-level fact, avoiding a public
per-statement preservation/freshness obligation at this layer. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_projectResult_eq_preserved
    (fuel selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) body' (some contract)) →
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          .ok final ∧
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  refine ⟨reservedNames, n0, cases', body', bodyStart, bodyEnd, ?_, ?_, ?_⟩
  · exact hCase
  · exact hBodyLower
  · intro hBody hPreservesMatched hProject
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hPeel :
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      let contract' : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      have hFuelShape :
          fuel + cases'.length + 19 =
            Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
        omega
      have hDispatcherPeel :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract' (initialState contract' tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner) (some contract')
              (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
        rw [hFuelShape]
        change
          contractDispatcherExecResult
              (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
              { dispatcher := .Block [.Block inner], functions := functions }
              (initialState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner)
              (some { dispatcher := .Block [.Block inner], functions := functions })
              (nativeSwitchInitialOkState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots)
        rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
          (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
          tx storage observableSlots]
        rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
          (some { dispatcher := .Block [.Block inner], functions := functions })
          (nativeSwitchInitialOkState
            { dispatcher := .Block [.Block inner], functions := functions }
            tx storage observableSlots)]
      calc
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots)
            = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
        _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block
                [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                    (some
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero"
                          [YulExpr.call "lt"
                            [YulExpr.call "calldatasize" [],
                             YulExpr.lit 4]]))),
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative
                      (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                    body1,
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                    [Backends.lowerNativeSwitchBlock
                      (YulExpr.call "shr"
                        [YulExpr.lit Compiler.Constants.selectorShift,
                         YulExpr.call "calldataload" [YulExpr.lit 0]])
                      (Backends.freshNativeSwitchId reservedNames n0) cases'
                      [nativeRevertZeroZeroStmt]]])
              (some contract)
              (nativeSwitchInitialOkState contract tx storage observableSlots) := by
            exact congrArg
              (fun body =>
                EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block body) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots))
              hInner
        _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
            have hExec :=
              exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                (fuel + cases'.length + 5) contract tx storage observableSlots
                "__has_selector" body1
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]]
                hNoWrap
            simpa only [Nat.add_assoc] using hExec
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_preserved
      fuel selector (Backends.freshNativeSwitchId reservedNames n0) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots final nativeYul hSelector hCase hSelectorRange hTagsRange
      hBody hPreservesMatched hProject

/-- Exact-total-fuel companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_projectResult_eq`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (cases'.length + 19 ≤ fuel' →
        (Backends.nativeSwitchTempsFreshForNativeBodies
          (Backends.freshNativeSwitchId reservedNames n0) cases'
          [nativeRevertZeroZeroStmt]) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) +
              suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ stmt, stmt ∈ body' →
          Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames n0) ∉
            Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) stmt (some contract)) →
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .ok final ∧
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  refine ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
    ?_, ?_, ?_, ?_⟩
  · exact hLowerCases
  · exact hCase
  · exact hBodyLower
  · intro hFuel hFresh hBody hStmtPreserves hProject
    let fuel := fuel' - (cases'.length + 19)
    have hFuelShape : fuel' = fuel + cases'.length + 19 := by
      dsimp [fuel]
      exact (Nat.sub_add_cancel hFuel).symm
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hBody' :
        ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final := by
      intro pre suffix hcases
      simpa [fuel, contract, Nat.add_assoc] using hBody pre suffix hcases
    have hPeel :
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      rw [hFuelShape]
      have hPeelStructural :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
        let contract' : EvmYul.Yul.Ast.YulContract :=
          { dispatcher := .Block [.Block inner], functions := functions }
        have hFuelShape' :
            fuel + cases'.length + 19 =
              Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
          omega
        have hDispatcherPeel :
            contractDispatcherExecResult (fuel + cases'.length + 19)
                contract' (initialState contract' tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract')
                (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
          rw [hFuelShape']
          change
            contractDispatcherExecResult
                (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
                { dispatcher := .Block [.Block inner], functions := functions }
                (initialState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner)
                (some { dispatcher := .Block [.Block inner], functions := functions })
                (nativeSwitchInitialOkState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots)
          rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
            (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
            tx storage observableSlots]
          rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (nativeSwitchInitialOkState
              { dispatcher := .Block [.Block inner], functions := functions }
              tx storage observableSlots)]
        calc
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots)
              = EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block inner) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
          _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block
                  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                      (some
                        (Backends.lowerExprNative
                          (YulExpr.call "iszero"
                            [YulExpr.call "lt"
                              [YulExpr.call "calldatasize" [],
                               YulExpr.lit 4]]))),
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                      body1,
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                      [Backends.lowerNativeSwitchBlock
                        (YulExpr.call "shr"
                          [YulExpr.lit Compiler.Constants.selectorShift,
                           YulExpr.call "calldataload" [YulExpr.lit 0]])
                        (Backends.freshNativeSwitchId reservedNames n0) cases'
                        [nativeRevertZeroZeroStmt]]])
                (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := by
              exact congrArg
                (fun body =>
                  EvmYul.Yul.exec (fuel + cases'.length + 17)
                    (.Block body) (some contract)
                    (nativeSwitchInitialOkState contract tx storage observableSlots))
                hInner
          _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
                (.Block
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames n0) cases'
                    [nativeRevertZeroZeroStmt]])
                (some contract)
                ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                  "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
              have hExec :=
                exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                  (fuel + cases'.length + 5) contract tx storage observableSlots
                  "__has_selector" body1
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames n0) cases'
                    [nativeRevertZeroZeroStmt]]
                  hNoWrap
              simpa only [Nat.add_assoc] using hExec
      exact hPeelStructural
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq
      fuel selector (Backends.freshNativeSwitchId reservedNames n0) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots final nativeYul hSelector hCase hSelectorRange hTagsRange
      hFresh hBody' hStmtPreserves hProject

/-- Exact-total-fuel companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_projectResult_eq_preserved`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_atFuel_projectResult_eq_preserved
    (fuel' selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) +
              suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) body' (some contract)) →
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .ok final ∧
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  refine ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
    ?_, ?_, ?_, ?_⟩
  · exact hLowerCases
  · exact hCase
  · exact hBodyLower
  · intro hFuel hBody hPreservesMatched hProject
    let fuel := fuel' - (cases'.length + 19)
    have hFuelShape : fuel' = fuel + cases'.length + 19 := by
      dsimp [fuel]
      exact (Nat.sub_add_cancel hFuel).symm
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hBody' :
        ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final := by
      intro pre suffix hcases
      simpa [fuel, contract, Nat.add_assoc] using hBody pre suffix hcases
    have hPeel :
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      rw [hFuelShape]
      have hPeelStructural :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
        let contract' : EvmYul.Yul.Ast.YulContract :=
          { dispatcher := .Block [.Block inner], functions := functions }
        have hFuelShape' :
            fuel + cases'.length + 19 =
              Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
          omega
        have hDispatcherPeel :
            contractDispatcherExecResult (fuel + cases'.length + 19)
                contract' (initialState contract' tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract')
                (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
          rw [hFuelShape']
          change
            contractDispatcherExecResult
                (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
                { dispatcher := .Block [.Block inner], functions := functions }
                (initialState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner)
                (some { dispatcher := .Block [.Block inner], functions := functions })
                (nativeSwitchInitialOkState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots)
          rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
            (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
            tx storage observableSlots]
          rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (nativeSwitchInitialOkState
              { dispatcher := .Block [.Block inner], functions := functions }
              tx storage observableSlots)]
        calc
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots)
              = EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block inner) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
          _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block
                  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                      (some
                        (Backends.lowerExprNative
                          (YulExpr.call "iszero"
                            [YulExpr.call "lt"
                              [YulExpr.call "calldatasize" [],
                               YulExpr.lit 4]]))),
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                      body1,
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                      [Backends.lowerNativeSwitchBlock
                        (YulExpr.call "shr"
                          [YulExpr.lit Compiler.Constants.selectorShift,
                           YulExpr.call "calldataload" [YulExpr.lit 0]])
                        (Backends.freshNativeSwitchId reservedNames n0) cases'
                        [nativeRevertZeroZeroStmt]]])
                (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := by
              exact congrArg
                (fun body =>
                  EvmYul.Yul.exec (fuel + cases'.length + 17)
                    (.Block body) (some contract)
                    (nativeSwitchInitialOkState contract tx storage observableSlots))
                hInner
          _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
                (.Block
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames n0) cases'
                    [nativeRevertZeroZeroStmt]])
                (some contract)
                ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                  "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
              have hExec :=
                exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                  (fuel + cases'.length + 5) contract tx storage observableSlots
                  "__has_selector" body1
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames n0) cases'
                    [nativeRevertZeroZeroStmt]]
                  hNoWrap
              simpa only [Nat.add_assoc] using hExec
      exact hPeelStructural
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_preserved
      fuel selector (Backends.freshNativeSwitchId reservedNames n0) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots final nativeYul hSelector hCase hSelectorRange hTagsRange
      hBody' hPreservesMatched hProject

/-- Polymorphic-final companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_atFuel_projectResult_eq_preserved`.

The lowered selector-hit artifacts do not depend on the eventual selected-body
result, so this exposes one artifact package with a continuation that accepts
any normal selected-case result. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_atFuel_projectResult_eq_preserved_forall
    (fuel' selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (∀ final nativeYul,
        cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) +
              suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) body' (some contract)) →
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .ok final ∧
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  refine ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
    ?_, ?_, ?_, ?_⟩
  · exact hLowerCases
  · exact hCase
  · exact hBodyLower
  · intro final nativeYul hFuel hBody hPreservesMatched hProject
    let fuel := fuel' - (cases'.length + 19)
    have hFuelShape : fuel' = fuel + cases'.length + 19 := by
      dsimp [fuel]
      exact (Nat.sub_add_cancel hFuel).symm
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hBody' :
        ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final := by
      intro pre suffix hcases
      simpa [fuel, contract, Nat.add_assoc] using hBody pre suffix hcases
    have hPeel :
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      rw [hFuelShape]
      have hPeelStructural :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
        let contract' : EvmYul.Yul.Ast.YulContract :=
          { dispatcher := .Block [.Block inner], functions := functions }
        have hFuelShape' :
            fuel + cases'.length + 19 =
              Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
          omega
        have hDispatcherPeel :
            contractDispatcherExecResult (fuel + cases'.length + 19)
                contract' (initialState contract' tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract')
                (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
          rw [hFuelShape']
          change
            contractDispatcherExecResult
                (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
                { dispatcher := .Block [.Block inner], functions := functions }
                (initialState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner)
                (some { dispatcher := .Block [.Block inner], functions := functions })
                (nativeSwitchInitialOkState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots)
          rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
            (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
            tx storage observableSlots]
          rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (nativeSwitchInitialOkState
              { dispatcher := .Block [.Block inner], functions := functions }
              tx storage observableSlots)]
        calc
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots)
              = EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block inner) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
          _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block
                  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                      (some
                        (Backends.lowerExprNative
                          (YulExpr.call "iszero"
                            [YulExpr.call "lt"
                              [YulExpr.call "calldatasize" [],
                               YulExpr.lit 4]]))),
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                      body1,
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                      [Backends.lowerNativeSwitchBlock
                        (YulExpr.call "shr"
                          [YulExpr.lit Compiler.Constants.selectorShift,
                           YulExpr.call "calldataload" [YulExpr.lit 0]])
                        (Backends.freshNativeSwitchId reservedNames n0) cases'
                        [nativeRevertZeroZeroStmt]]])
                (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := by
              exact congrArg
                (fun body =>
                  EvmYul.Yul.exec (fuel + cases'.length + 17)
                    (.Block body) (some contract)
                    (nativeSwitchInitialOkState contract tx storage observableSlots))
                hInner
          _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
                (.Block
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames n0) cases'
                    [nativeRevertZeroZeroStmt]])
                (some contract)
                ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                  "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
              have hExec :=
                exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                  (fuel + cases'.length + 5) contract tx storage observableSlots
                  "__has_selector" body1
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames n0) cases'
                    [nativeRevertZeroZeroStmt]]
                  hNoWrap
              simpa only [Nat.add_assoc] using hExec
      exact hPeelStructural
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_preserved
      fuel selector (Backends.freshNativeSwitchId reservedNames n0) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots final nativeYul hSelector hCase hSelectorRange hTagsRange
      hBody' hPreservesMatched hProject

/-- Polymorphic-final companion with a direct raw matched-flag endpoint fact. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_atFuel_projectResult_eq_finalMatched_forall
    (fuel' selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok [.Block inner])
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' : List EvmYul.Yul.Ast.Stmt)
      (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (∀ final nativeYul,
        cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) +
              suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ matchedName : EvmYul.Identifier,
          matchedName = Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames n0) →
            final[matchedName]! = EvmYul.UInt256.ofNat 1) →
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .ok final ∧
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
      funcs inner selector fn hLower hFind
  refine ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
    ?_, ?_, ?_, ?_⟩
  · exact hLowerCases
  · exact hCase
  · exact hBodyLower
  · intro final nativeYul hFuel hBody hFinalMatched hProject
    let fuel := fuel' - (cases'.length + 19)
    have hFuelShape : fuel' = fuel + cases'.length + 19 := by
      dsimp [fuel]
      exact (Nat.sub_add_cancel hFuel).symm
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hBody' :
        ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames n0)
              nativeSwitchHasSelectorStore) = .ok final := by
      intro pre suffix hcases
      simpa [fuel, contract, Nat.add_assoc] using hBody pre suffix hcases
    have hPeel :
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames n0) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      rw [hFuelShape]
      have hPeelStructural :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames n0) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
        let contract' : EvmYul.Yul.Ast.YulContract :=
          { dispatcher := .Block [.Block inner], functions := functions }
        have hFuelShape' :
            fuel + cases'.length + 19 =
              Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
          omega
        have hDispatcherPeel :
            contractDispatcherExecResult (fuel + cases'.length + 19)
                contract' (initialState contract' tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract')
                (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
          rw [hFuelShape']
          change
            contractDispatcherExecResult
                (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
                { dispatcher := .Block [.Block inner], functions := functions }
                (initialState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner)
                (some { dispatcher := .Block [.Block inner], functions := functions })
                (nativeSwitchInitialOkState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots)
          rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
            (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
            tx storage observableSlots]
          rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (nativeSwitchInitialOkState
              { dispatcher := .Block [.Block inner], functions := functions }
              tx storage observableSlots)]
        calc
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots)
              = EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block inner) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
          _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block
                  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                      (some
                        (Backends.lowerExprNative
                          (YulExpr.call "iszero"
                            [YulExpr.call "lt"
                              [YulExpr.call "calldatasize" [],
                               YulExpr.lit 4]]))),
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                      body1,
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                      [Backends.lowerNativeSwitchBlock
                        (YulExpr.call "shr"
                          [YulExpr.lit Compiler.Constants.selectorShift,
                           YulExpr.call "calldataload" [YulExpr.lit 0]])
                        (Backends.freshNativeSwitchId reservedNames n0) cases'
                        [nativeRevertZeroZeroStmt]]])
                (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := by
              exact congrArg
                (fun body =>
                  EvmYul.Yul.exec (fuel + cases'.length + 17)
                    (.Block body) (some contract)
                    (nativeSwitchInitialOkState contract tx storage observableSlots))
                hInner
          _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
                (.Block
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames n0) cases'
                    [nativeRevertZeroZeroStmt]])
                (some contract)
                ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                  "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
              have hExec :=
                exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                  (fuel + cases'.length + 5) contract tx storage observableSlots
                  "__has_selector" body1
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames n0) cases'
                    [nativeRevertZeroZeroStmt]]
                  hNoWrap
              simpa only [Nat.add_assoc] using hExec
      exact hPeelStructural
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_finalMatched
      fuel selector (Backends.freshNativeSwitchId reservedNames n0) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots final nativeYul hSelector hCase hSelectorRange hTagsRange
      hBody' hFinalMatched hProject


/-- Reserved-context companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_projectResult_eq`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_withSwitchIds_projectResult_eq
    (fuel selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .error err) →
        projectResult tx storage initialEvents (.error err) = nativeYul →
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          .error err ∧
        projectResult tx storage initialEvents (.error err) = nativeYul) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  refine ⟨switchStart, cases', body', bodyStart, bodyEnd, ?_, ?_, ?_⟩
  · exact hCase
  · exact hBodyLower
  · intro hBody hProject
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hPeel :
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      let contract' : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      have hFuelShape :
          fuel + cases'.length + 19 =
            Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
        omega
      have hDispatcherPeel :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract' (initialState contract' tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner) (some contract')
              (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
        rw [hFuelShape]
        change
          contractDispatcherExecResult
              (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
              { dispatcher := .Block [.Block inner], functions := functions }
              (initialState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner)
              (some { dispatcher := .Block [.Block inner], functions := functions })
              (nativeSwitchInitialOkState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots)
        rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
          (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
          tx storage observableSlots]
        rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
          (some { dispatcher := .Block [.Block inner], functions := functions })
          (nativeSwitchInitialOkState
            { dispatcher := .Block [.Block inner], functions := functions }
            tx storage observableSlots)]
      calc
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots)
            = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
        _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block
                [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                    (some
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero"
                          [YulExpr.call "lt"
                            [YulExpr.call "calldatasize" [],
                             YulExpr.lit 4]]))),
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative
                      (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                    body1,
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                    [Backends.lowerNativeSwitchBlock
                      (YulExpr.call "shr"
                        [YulExpr.lit Compiler.Constants.selectorShift,
                         YulExpr.call "calldataload" [YulExpr.lit 0]])
                      (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                      [nativeRevertZeroZeroStmt]]])
              (some contract)
              (nativeSwitchInitialOkState contract tx storage observableSlots) := by
            exact congrArg
              (fun body =>
                EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block body) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots))
              hInner
        _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
            have hExec :=
              exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                (fuel + cases'.length + 5) contract tx storage observableSlots
                "__has_selector" body1
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]]
                hNoWrap
            simpa only [Nat.add_assoc] using hExec
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq
      fuel selector (Backends.freshNativeSwitchId reservedNames switchStart) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots err nativeYul hSelector hCase hSelectorRange hTagsRange
      hBody hProject

/-- Exact-total-fuel companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_withSwitchIds_projectResult_eq`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_withSwitchIds_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) +
              suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .error err) →
        projectResult tx storage initialEvents (.error err) = nativeYul →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .error err ∧
        projectResult tx storage initialEvents (.error err) = nativeYul) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  refine ⟨switchStart, cases', midN, body', bodyStart, bodyEnd,
    ?_, ?_, ?_, ?_⟩
  · exact hLowerCases
  · exact hCase
  · exact hBodyLower
  · intro hFuel hBody hProject
    let fuel := fuel' - (cases'.length + 19)
    have hFuelShape : fuel' = fuel + cases'.length + 19 := by
      dsimp [fuel]
      exact (Nat.sub_add_cancel hFuel).symm
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hBody' :
        ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .error err := by
      intro pre suffix hcases
      simpa [fuel, contract, Nat.add_assoc] using hBody pre suffix hcases
    have hPeel :
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      rw [hFuelShape]
      have hPeelStructural :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
        let contract' : EvmYul.Yul.Ast.YulContract :=
          { dispatcher := .Block [.Block inner], functions := functions }
        have hFuelShape' :
            fuel + cases'.length + 19 =
              Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
          omega
        have hDispatcherPeel :
            contractDispatcherExecResult (fuel + cases'.length + 19)
                contract' (initialState contract' tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract')
                (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
          rw [hFuelShape']
          change
            contractDispatcherExecResult
                (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
                { dispatcher := .Block [.Block inner], functions := functions }
                (initialState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner)
                (some { dispatcher := .Block [.Block inner], functions := functions })
                (nativeSwitchInitialOkState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots)
          rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
            (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
            tx storage observableSlots]
          rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (nativeSwitchInitialOkState
              { dispatcher := .Block [.Block inner], functions := functions }
              tx storage observableSlots)]
        calc
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots)
              = EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block inner) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
          _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block
                  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                      (some
                        (Backends.lowerExprNative
                          (YulExpr.call "iszero"
                            [YulExpr.call "lt"
                              [YulExpr.call "calldatasize" [],
                               YulExpr.lit 4]]))),
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                      body1,
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                      [Backends.lowerNativeSwitchBlock
                        (YulExpr.call "shr"
                          [YulExpr.lit Compiler.Constants.selectorShift,
                           YulExpr.call "calldataload" [YulExpr.lit 0]])
                        (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                        [nativeRevertZeroZeroStmt]]])
                (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := by
              exact congrArg
                (fun body =>
                  EvmYul.Yul.exec (fuel + cases'.length + 17)
                    (.Block body) (some contract)
                    (nativeSwitchInitialOkState contract tx storage observableSlots))
                hInner
          _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
                (.Block
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                    [nativeRevertZeroZeroStmt]])
                (some contract)
                ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                  "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
              have hExec :=
                exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                  (fuel + cases'.length + 5) contract tx storage observableSlots
                  "__has_selector" body1
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                    [nativeRevertZeroZeroStmt]]
                  hNoWrap
              simpa only [Nat.add_assoc] using hExec
      exact hPeelStructural
    constructor
    · rw [hPeel]
      exact (exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq
        fuel selector (Backends.freshNativeSwitchId reservedNames switchStart) selector
        cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
        observableSlots err nativeYul hSelector hCase hSelectorRange hTagsRange
        hBody' hProject).1
    · exact hProject

/-- Artifact-fixed companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_withSwitchIds_atFuel_projectResult_eq`.

The selected switch-case artifacts are exposed before choosing the concrete
error and projected native result. This is useful for halt-channel bodies,
where the selected-body execution itself produces the `YulHalt` state that must
be fed into the dispatcher error continuation. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_withSwitchIds_atFuel_artifact_projectResult_eq
    (fuel' selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (∀ (err : EvmYul.Yul.Exception) (nativeYul : YulResult),
        cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) +
              suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .error err) →
        projectResult tx storage initialEvents (.error err) = nativeYul →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .error err ∧
        projectResult tx storage initialEvents (.error err) = nativeYul) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  refine ⟨switchStart, cases', midN, body', bodyStart, bodyEnd,
    hLowerCases, hCase, hBodyLower, ?_⟩
  intro err nativeYul hFuel hBody hProject
  let fuel := fuel' - (cases'.length + 19)
  have hFuelShape : fuel' = fuel + cases'.length + 19 := by
    dsimp [fuel]
    exact (Nat.sub_add_cancel hFuel).symm
  let contract : EvmYul.Yul.Ast.YulContract :=
    { dispatcher := .Block [.Block inner], functions := functions }
  have hTagsEq :
      cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
      (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
      (buildSwitchSourceCases funcs) cases' hLowerCases
  have hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
    intro tag body hmem
    have hTagMem : tag ∈ cases'.map (·.1) := by
      exact List.mem_map_of_mem (f := Prod.fst) hmem
    rw [hTagsEq] at hTagMem
    simp [buildSwitchSourceCases] at hTagMem
    rcases hTagMem with ⟨fn, hFn, hTag⟩
    subst hTag
    exact hFunctionSelectorsRange fn hFn
  have hBody' :
      ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
        EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
          (some contract)
          (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
            observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
            nativeSwitchHasSelectorStore) = .error err := by
    intro pre suffix hcases
    simpa [fuel, contract, Nat.add_assoc] using hBody pre suffix hcases
  have hPeel :
      contractDispatcherExecResult fuel'
          contract (initialState contract tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 13)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames switchStart) cases'
              [nativeRevertZeroZeroStmt]])
          (some contract)
          ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
            "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
    rw [hFuelShape]
    have hPeelStructural :
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      let contract' : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      have hFuelShape' :
          fuel + cases'.length + 19 =
            Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
        omega
      have hDispatcherPeel :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract' (initialState contract' tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner) (some contract')
              (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
        rw [hFuelShape']
        change
          contractDispatcherExecResult
              (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
              { dispatcher := .Block [.Block inner], functions := functions }
              (initialState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner)
              (some { dispatcher := .Block [.Block inner], functions := functions })
              (nativeSwitchInitialOkState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots)
        rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
          (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
          tx storage observableSlots]
        rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
          (some { dispatcher := .Block [.Block inner], functions := functions })
          (nativeSwitchInitialOkState
            { dispatcher := .Block [.Block inner], functions := functions }
            tx storage observableSlots)]
      calc
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots)
            = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
        _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block
                [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                    (some
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero"
                          [YulExpr.call "lt"
                            [YulExpr.call "calldatasize" [],
                             YulExpr.lit 4]]))),
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative
                      (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                    body1,
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                    [Backends.lowerNativeSwitchBlock
                      (YulExpr.call "shr"
                        [YulExpr.lit Compiler.Constants.selectorShift,
                         YulExpr.call "calldataload" [YulExpr.lit 0]])
                      (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                      [nativeRevertZeroZeroStmt]]])
              (some contract)
              (nativeSwitchInitialOkState contract tx storage observableSlots) := by
            exact congrArg
              (fun body =>
                EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block body) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots))
              hInner
        _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
            have hExec :=
              exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                (fuel + cases'.length + 5) contract tx storage observableSlots
                "__has_selector" body1
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]]
                hNoWrap
            simpa only [Nat.add_assoc] using hExec
    exact hPeelStructural
  constructor
  · rw [hPeel]
    exact (exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq
      fuel selector (Backends.freshNativeSwitchId reservedNames switchStart) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots err nativeYul hSelector hCase hSelectorRange hTagsRange
      hBody' hProject).1
  · exact hProject

/-- Reserved-context companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_projectResult_eq`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_projectResult_eq
    (fuel selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      ((Backends.nativeSwitchTempsFreshForNativeBodies
          (Backends.freshNativeSwitchId reservedNames switchStart) cases'
          [nativeRevertZeroZeroStmt]) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ stmt, stmt ∈ body' →
          Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames switchStart) ∉
            Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) stmt (some contract)) →
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          .ok final ∧
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  refine ⟨switchStart, cases', body', bodyStart, bodyEnd, ?_, ?_, ?_⟩
  · exact hCase
  · exact hBodyLower
  · intro hFresh hBody hStmtPreserves hProject
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hPeel :
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      let contract' : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      have hFuelShape :
          fuel + cases'.length + 19 =
            Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
        omega
      have hDispatcherPeel :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract' (initialState contract' tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner) (some contract')
              (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
        rw [hFuelShape]
        change
          contractDispatcherExecResult
              (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
              { dispatcher := .Block [.Block inner], functions := functions }
              (initialState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner)
              (some { dispatcher := .Block [.Block inner], functions := functions })
              (nativeSwitchInitialOkState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots)
        rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
          (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
          tx storage observableSlots]
        rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
          (some { dispatcher := .Block [.Block inner], functions := functions })
          (nativeSwitchInitialOkState
            { dispatcher := .Block [.Block inner], functions := functions }
            tx storage observableSlots)]
      calc
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots)
            = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
        _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block
                [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                    (some
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero"
                          [YulExpr.call "lt"
                            [YulExpr.call "calldatasize" [],
                             YulExpr.lit 4]]))),
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative
                      (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                    body1,
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                    [Backends.lowerNativeSwitchBlock
                      (YulExpr.call "shr"
                        [YulExpr.lit Compiler.Constants.selectorShift,
                         YulExpr.call "calldataload" [YulExpr.lit 0]])
                      (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                      [nativeRevertZeroZeroStmt]]])
              (some contract)
              (nativeSwitchInitialOkState contract tx storage observableSlots) := by
            exact congrArg
              (fun body =>
                EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block body) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots))
              hInner
        _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
            have hExec :=
              exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                (fuel + cases'.length + 5) contract tx storage observableSlots
                "__has_selector" body1
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]]
                hNoWrap
            simpa only [Nat.add_assoc] using hExec
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq
      fuel selector (Backends.freshNativeSwitchId reservedNames switchStart) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots final nativeYul hSelector hCase hSelectorRange hTagsRange
      hFresh hBody hStmtPreserves hProject

/-- Block-preservation reserved-context companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_projectResult_eq`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_projectResult_eq_preserved
    (fuel selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) body' (some contract)) →
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          .ok final ∧
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  refine ⟨switchStart, cases', body', bodyStart, bodyEnd, ?_, ?_, ?_⟩
  · exact hCase
  · exact hBodyLower
  · intro hBody hPreservesMatched hProject
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hPeel :
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      let contract' : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      have hFuelShape :
          fuel + cases'.length + 19 =
            Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
        omega
      have hDispatcherPeel :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract' (initialState contract' tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner) (some contract')
              (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
        rw [hFuelShape]
        change
          contractDispatcherExecResult
              (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
              { dispatcher := .Block [.Block inner], functions := functions }
              (initialState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner)
              (some { dispatcher := .Block [.Block inner], functions := functions })
              (nativeSwitchInitialOkState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots)
        rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
          (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
          tx storage observableSlots]
        rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
          (some { dispatcher := .Block [.Block inner], functions := functions })
          (nativeSwitchInitialOkState
            { dispatcher := .Block [.Block inner], functions := functions }
            tx storage observableSlots)]
      calc
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots)
            = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
        _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block
                [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                    (some
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero"
                          [YulExpr.call "lt"
                            [YulExpr.call "calldatasize" [],
                             YulExpr.lit 4]]))),
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative
                      (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                    body1,
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                    [Backends.lowerNativeSwitchBlock
                      (YulExpr.call "shr"
                        [YulExpr.lit Compiler.Constants.selectorShift,
                         YulExpr.call "calldataload" [YulExpr.lit 0]])
                      (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                      [nativeRevertZeroZeroStmt]]])
              (some contract)
              (nativeSwitchInitialOkState contract tx storage observableSlots) := by
            exact congrArg
              (fun body =>
                EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block body) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots))
              hInner
        _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
            have hExec :=
              exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                (fuel + cases'.length + 5) contract tx storage observableSlots
                "__has_selector" body1
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]]
                hNoWrap
            simpa only [Nat.add_assoc] using hExec
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_preserved
      fuel selector (Backends.freshNativeSwitchId reservedNames switchStart) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots final nativeYul hSelector hCase hSelectorRange hTagsRange
      hBody hPreservesMatched hProject

/-- Exact-total-fuel reserved-context companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_projectResult_eq`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (cases'.length + 19 ≤ fuel' →
        (Backends.nativeSwitchTempsFreshForNativeBodies
          (Backends.freshNativeSwitchId reservedNames switchStart) cases'
          [nativeRevertZeroZeroStmt]) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) +
              suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ stmt, stmt ∈ body' →
          Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames switchStart) ∉
            Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) stmt (some contract)) →
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .ok final ∧
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  refine ⟨switchStart, cases', midN, body', bodyStart, bodyEnd,
    ?_, ?_, ?_, ?_⟩
  · exact hLowerCases
  · exact hCase
  · exact hBodyLower
  · intro hFuel hFresh hBody hStmtPreserves hProject
    let fuel := fuel' - (cases'.length + 19)
    have hFuelShape : fuel' = fuel + cases'.length + 19 := by
      dsimp [fuel]
      exact (Nat.sub_add_cancel hFuel).symm
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hBody' :
        ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final := by
      intro pre suffix hcases
      simpa [fuel, contract, Nat.add_assoc] using hBody pre suffix hcases
    have hPeel :
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      rw [hFuelShape]
      have hPeelStructural :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
        let contract' : EvmYul.Yul.Ast.YulContract :=
          { dispatcher := .Block [.Block inner], functions := functions }
        have hFuelShape' :
            fuel + cases'.length + 19 =
              Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
          omega
        have hDispatcherPeel :
            contractDispatcherExecResult (fuel + cases'.length + 19)
                contract' (initialState contract' tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract')
                (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
          rw [hFuelShape']
          change
            contractDispatcherExecResult
                (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
                { dispatcher := .Block [.Block inner], functions := functions }
                (initialState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner)
                (some { dispatcher := .Block [.Block inner], functions := functions })
                (nativeSwitchInitialOkState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots)
          rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
            (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
            tx storage observableSlots]
          rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (nativeSwitchInitialOkState
              { dispatcher := .Block [.Block inner], functions := functions }
              tx storage observableSlots)]
        calc
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots)
              = EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block inner) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
          _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block
                  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                      (some
                        (Backends.lowerExprNative
                          (YulExpr.call "iszero"
                            [YulExpr.call "lt"
                              [YulExpr.call "calldatasize" [],
                               YulExpr.lit 4]]))),
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                      body1,
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                      [Backends.lowerNativeSwitchBlock
                        (YulExpr.call "shr"
                          [YulExpr.lit Compiler.Constants.selectorShift,
                           YulExpr.call "calldataload" [YulExpr.lit 0]])
                        (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                        [nativeRevertZeroZeroStmt]]])
                (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := by
              exact congrArg
                (fun body =>
                  EvmYul.Yul.exec (fuel + cases'.length + 17)
                    (.Block body) (some contract)
                    (nativeSwitchInitialOkState contract tx storage observableSlots))
                hInner
          _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
                (.Block
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                    [nativeRevertZeroZeroStmt]])
                (some contract)
                ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                  "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
              have hExec :=
                exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                  (fuel + cases'.length + 5) contract tx storage observableSlots
                  "__has_selector" body1
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                    [nativeRevertZeroZeroStmt]]
                  hNoWrap
              simpa only [Nat.add_assoc] using hExec
      exact hPeelStructural
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq
      fuel selector (Backends.freshNativeSwitchId reservedNames switchStart) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots final nativeYul hSelector hCase hSelectorRange hTagsRange
      hFresh hBody' hStmtPreserves hProject

/-- Exact-total-fuel reserved-context companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_projectResult_eq_preserved`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_atFuel_projectResult_eq_preserved
    (fuel' selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) +
              suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) body' (some contract)) →
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .ok final ∧
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  refine ⟨switchStart, cases', midN, body', bodyStart, bodyEnd,
    ?_, ?_, ?_, ?_⟩
  · exact hLowerCases
  · exact hCase
  · exact hBodyLower
  · intro hFuel hBody hPreservesMatched hProject
    let fuel := fuel' - (cases'.length + 19)
    have hFuelShape : fuel' = fuel + cases'.length + 19 := by
      dsimp [fuel]
      exact (Nat.sub_add_cancel hFuel).symm
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hBody' :
        ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final := by
      intro pre suffix hcases
      simpa [fuel, contract, Nat.add_assoc] using hBody pre suffix hcases
    have hPeel :
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      rw [hFuelShape]
      have hPeelStructural :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
        let contract' : EvmYul.Yul.Ast.YulContract :=
          { dispatcher := .Block [.Block inner], functions := functions }
        have hFuelShape' :
            fuel + cases'.length + 19 =
              Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
          omega
        have hDispatcherPeel :
            contractDispatcherExecResult (fuel + cases'.length + 19)
                contract' (initialState contract' tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract')
                (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
          rw [hFuelShape']
          change
            contractDispatcherExecResult
                (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
                { dispatcher := .Block [.Block inner], functions := functions }
                (initialState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner)
                (some { dispatcher := .Block [.Block inner], functions := functions })
                (nativeSwitchInitialOkState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots)
          rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
            (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
            tx storage observableSlots]
          rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (nativeSwitchInitialOkState
              { dispatcher := .Block [.Block inner], functions := functions }
              tx storage observableSlots)]
        calc
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots)
              = EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block inner) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
          _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block
                  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                      (some
                        (Backends.lowerExprNative
                          (YulExpr.call "iszero"
                            [YulExpr.call "lt"
                              [YulExpr.call "calldatasize" [],
                               YulExpr.lit 4]]))),
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                      body1,
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                      [Backends.lowerNativeSwitchBlock
                        (YulExpr.call "shr"
                          [YulExpr.lit Compiler.Constants.selectorShift,
                           YulExpr.call "calldataload" [YulExpr.lit 0]])
                        (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                        [nativeRevertZeroZeroStmt]]])
                (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := by
              exact congrArg
                (fun body =>
                  EvmYul.Yul.exec (fuel + cases'.length + 17)
                    (.Block body) (some contract)
                    (nativeSwitchInitialOkState contract tx storage observableSlots))
                hInner
          _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
                (.Block
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                    [nativeRevertZeroZeroStmt]])
                (some contract)
                ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                  "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
              have hExec :=
                exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                  (fuel + cases'.length + 5) contract tx storage observableSlots
                  "__has_selector" body1
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                    [nativeRevertZeroZeroStmt]]
                  hNoWrap
              simpa only [Nat.add_assoc] using hExec
      exact hPeelStructural
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_preserved
      fuel selector (Backends.freshNativeSwitchId reservedNames switchStart) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots final nativeYul hSelector hCase hSelectorRange hTagsRange
      hBody' hPreservesMatched hProject

/-- Polymorphic-final reserved-context companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_atFuel_projectResult_eq_preserved`.

The reserved-name lowering artifacts are independent of the selected-body
normal result, so this exposes a single artifact package with a continuation
that accepts any `final/nativeYul`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_atFuel_projectResult_eq_preserved_forall
    (fuel' selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (∀ final nativeYul,
        cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) +
              suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          NativeBlockPreservesWord
            (Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) body' (some contract)) →
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .ok final ∧
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  refine ⟨switchStart, cases', midN, body', bodyStart, bodyEnd,
    ?_, ?_, ?_, ?_⟩
  · exact hLowerCases
  · exact hCase
  · exact hBodyLower
  · intro final nativeYul hFuel hBody hPreservesMatched hProject
    let fuel := fuel' - (cases'.length + 19)
    have hFuelShape : fuel' = fuel + cases'.length + 19 := by
      dsimp [fuel]
      exact (Nat.sub_add_cancel hFuel).symm
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hBody' :
        ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final := by
      intro pre suffix hcases
      simpa [fuel, contract, Nat.add_assoc] using hBody pre suffix hcases
    have hPeel :
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      rw [hFuelShape]
      have hPeelStructural :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
        let contract' : EvmYul.Yul.Ast.YulContract :=
          { dispatcher := .Block [.Block inner], functions := functions }
        have hFuelShape' :
            fuel + cases'.length + 19 =
              Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
          omega
        have hDispatcherPeel :
            contractDispatcherExecResult (fuel + cases'.length + 19)
                contract' (initialState contract' tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract')
                (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
          rw [hFuelShape']
          change
            contractDispatcherExecResult
                (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
                { dispatcher := .Block [.Block inner], functions := functions }
                (initialState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner)
                (some { dispatcher := .Block [.Block inner], functions := functions })
                (nativeSwitchInitialOkState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots)
          rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
            (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
            tx storage observableSlots]
          rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (nativeSwitchInitialOkState
              { dispatcher := .Block [.Block inner], functions := functions }
              tx storage observableSlots)]
        calc
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots)
              = EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block inner) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
          _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block
                  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                      (some
                        (Backends.lowerExprNative
                          (YulExpr.call "iszero"
                            [YulExpr.call "lt"
                              [YulExpr.call "calldatasize" [],
                               YulExpr.lit 4]]))),
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                      body1,
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                      [Backends.lowerNativeSwitchBlock
                        (YulExpr.call "shr"
                          [YulExpr.lit Compiler.Constants.selectorShift,
                           YulExpr.call "calldataload" [YulExpr.lit 0]])
                        (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                        [nativeRevertZeroZeroStmt]]])
                (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := by
              exact congrArg
                (fun body =>
                  EvmYul.Yul.exec (fuel + cases'.length + 17)
                    (.Block body) (some contract)
                    (nativeSwitchInitialOkState contract tx storage observableSlots))
                hInner
          _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
                (.Block
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                    [nativeRevertZeroZeroStmt]])
                (some contract)
                ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                  "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
              have hExec :=
                exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                  (fuel + cases'.length + 5) contract tx storage observableSlots
                  "__has_selector" body1
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                    [nativeRevertZeroZeroStmt]]
                  hNoWrap
              simpa only [Nat.add_assoc] using hExec
      exact hPeelStructural
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_preserved
      fuel selector (Backends.freshNativeSwitchId reservedNames switchStart) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots final nativeYul hSelector hCase hSelectorRange hTagsRange
      hBody' hPreservesMatched hProject

/-- Polymorphic-final reserved-context companion with a direct raw matched-flag endpoint fact. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_atFuel_projectResult_eq_finalMatched_forall
    (fuel' selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (∀ final nativeYul,
        cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) +
              suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final) →
        (∀ matchedName : EvmYul.Identifier,
          matchedName = Backends.nativeSwitchMatchedTempName
              (Backends.freshNativeSwitchId reservedNames switchStart) →
            final[matchedName]! = EvmYul.UInt256.ofNat 1) →
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .ok final ∧
        projectResult tx storage initialEvents (.ok (final, [])) = nativeYul) := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
      hInner, hLowerCases, hCase, hBodyLower⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames n0 funcs inner next selector fn hLower hFind
  refine ⟨switchStart, cases', midN, body', bodyStart, bodyEnd,
    ?_, ?_, ?_, ?_⟩
  · exact hLowerCases
  · exact hCase
  · exact hBodyLower
  · intro final nativeYul hFuel hBody hFinalMatched hProject
    let fuel := fuel' - (cases'.length + 19)
    have hFuelShape : fuel' = fuel + cases'.length + 19 := by
      dsimp [fuel]
      exact (Nat.sub_add_cancel hFuel).symm
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hBody' :
        ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some contract)
            (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
              observableSlots (Backends.freshNativeSwitchId reservedNames switchStart)
              nativeSwitchHasSelectorStore) = .ok final := by
      intro pre suffix hcases
      simpa [fuel, contract, Nat.add_assoc] using hBody pre suffix hcases
    have hPeel :
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      rw [hFuelShape]
      have hPeelStructural :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
        let contract' : EvmYul.Yul.Ast.YulContract :=
          { dispatcher := .Block [.Block inner], functions := functions }
        have hFuelShape' :
            fuel + cases'.length + 19 =
              Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
          omega
        have hDispatcherPeel :
            contractDispatcherExecResult (fuel + cases'.length + 19)
                contract' (initialState contract' tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract')
                (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
          rw [hFuelShape']
          change
            contractDispatcherExecResult
                (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
                { dispatcher := .Block [.Block inner], functions := functions }
                (initialState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner)
                (some { dispatcher := .Block [.Block inner], functions := functions })
                (nativeSwitchInitialOkState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots)
          rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
            (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
            tx storage observableSlots]
          rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (nativeSwitchInitialOkState
              { dispatcher := .Block [.Block inner], functions := functions }
              tx storage observableSlots)]
        calc
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots)
              = EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block inner) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
          _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block
                  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                      (some
                        (Backends.lowerExprNative
                          (YulExpr.call "iszero"
                            [YulExpr.call "lt"
                              [YulExpr.call "calldatasize" [],
                               YulExpr.lit 4]]))),
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                      body1,
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                      [Backends.lowerNativeSwitchBlock
                        (YulExpr.call "shr"
                          [YulExpr.lit Compiler.Constants.selectorShift,
                           YulExpr.call "calldataload" [YulExpr.lit 0]])
                        (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                        [nativeRevertZeroZeroStmt]]])
                (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := by
              exact congrArg
                (fun body =>
                  EvmYul.Yul.exec (fuel + cases'.length + 17)
                    (.Block body) (some contract)
                    (nativeSwitchInitialOkState contract tx storage observableSlots))
                hInner
          _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
                (.Block
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                    [nativeRevertZeroZeroStmt]])
                (some contract)
                ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                  "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
              have hExec :=
                exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                  (fuel + cases'.length + 5) contract tx storage observableSlots
                  "__has_selector" body1
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                    [nativeRevertZeroZeroStmt]]
                  hNoWrap
              simpa only [Nat.add_assoc] using hExec
      exact hPeelStructural
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq_finalMatched
      fuel selector (Backends.freshNativeSwitchId reservedNames switchStart) selector
      cases' [nativeRevertZeroZeroStmt] body' contract tx storage initialEvents
      observableSlots final nativeYul hSelector hCase hSelectorRange hTagsRange
      hBody' hFinalMatched hProject


/-- Reserved-context variant of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_none_projectResult_eq`.

This is the selector-miss package needed when the generated dispatcher is lowered
under the emitted runtime's reserved-name context, as in the mapping-helper
runtime path. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_none_withSwitchIds_projectResult_eq
    (fuel selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun fn => fn.selector == selector) = none)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
          (Backends.freshNativeSwitchId reservedNames switchStart + 1)
          (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      contractDispatcherExecResult (fuel + cases'.length + 19)
          contract (initialState contract tx storage observableSlots) =
        .error EvmYul.Yul.Exception.Revert ∧
      projectResult tx storage initialEvents
          (.error EvmYul.Yul.Exception.Revert) =
        { success := false
          returnValue := none
          finalStorage := storage
          finalMappings := Compiler.Proofs.storageAsMappings storage
          events := initialEvents } := by
  obtain ⟨body1, switchStart, cases', midN, hInner, hLowerCases⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered_withSwitchIds
      reservedNames n0 funcs inner next hLower
  refine ⟨switchStart, cases', midN, ?_, ?_, ?_⟩
  · exact hLowerCases
  · let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hLowerFind :
        cases'.find? (fun entry => entry.1 == selector) = none :=
      lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_none_of_find_function
        reservedNames (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
        selector funcs cases' hLowerCases hFind
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hPeel :
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      let contract' : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      have hFuelShape :
          fuel + cases'.length + 19 =
            Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
        omega
      have hDispatcherPeel :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract' (initialState contract' tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner) (some contract')
              (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
        rw [hFuelShape]
        change
          contractDispatcherExecResult
              (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
              { dispatcher := .Block [.Block inner], functions := functions }
              (initialState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block inner)
              (some { dispatcher := .Block [.Block inner], functions := functions })
              (nativeSwitchInitialOkState
                { dispatcher := .Block [.Block inner], functions := functions }
                tx storage observableSlots)
        rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
          (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
          tx storage observableSlots]
        rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
          (some { dispatcher := .Block [.Block inner], functions := functions })
          (nativeSwitchInitialOkState
            { dispatcher := .Block [.Block inner], functions := functions }
            tx storage observableSlots)]
      calc
        contractDispatcherExecResult (fuel + cases'.length + 19)
            contract (initialState contract tx storage observableSlots)
            = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
        _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
              (.Block
                [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                    (some
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero"
                          [YulExpr.call "lt"
                            [YulExpr.call "calldatasize" [],
                             YulExpr.lit 4]]))),
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative
                      (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                    body1,
                 EvmYul.Yul.Ast.Stmt.If
                    (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                    [Backends.lowerNativeSwitchBlock
                      (YulExpr.call "shr"
                        [YulExpr.lit Compiler.Constants.selectorShift,
                         YulExpr.call "calldataload" [YulExpr.lit 0]])
                      (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                      [nativeRevertZeroZeroStmt]]])
              (some contract)
              (nativeSwitchInitialOkState contract tx storage observableSlots) := by
            exact congrArg
              (fun body =>
                EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block body) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots))
              hInner
        _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
            have hExec :=
              exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                (fuel + cases'.length + 5) contract tx storage observableSlots
                "__has_selector" body1
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]]
                hNoWrap
            simpa only [Nat.add_assoc] using hExec
    rw [hPeel]
    exact exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_error
      fuel selector (Backends.freshNativeSwitchId reservedNames switchStart) cases'
      contract tx storage observableSlots hSelector hLowerFind hSelectorRange
      hTagsRange
  · simp

/-- Exact-total-fuel reserved-context selector-miss companion of
`contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_none_withSwitchIds_projectResult_eq`. -/
theorem contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_none_withSwitchIds_atFuel_projectResult_eq
    (fuel' selector : Nat)
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hLower :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], next))
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : funcs.find? (fun fn => fn.selector == selector) = none)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      let contract : EvmYul.Yul.Ast.YulContract :=
        { dispatcher := .Block [.Block inner], functions := functions }
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
          (Backends.freshNativeSwitchId reservedNames switchStart + 1)
          (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      (cases'.length + 19 ≤ fuel' →
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          .error EvmYul.Yul.Exception.Revert ∧
        projectResult tx storage initialEvents
            (.error EvmYul.Yul.Exception.Revert) =
          { success := false
            returnValue := none
            finalStorage := storage
            finalMappings := Compiler.Proofs.storageAsMappings storage
            events := initialEvents }) := by
  obtain ⟨body1, switchStart, cases', midN, hInner, hLowerCases⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered_withSwitchIds
      reservedNames n0 funcs inner next hLower
  refine ⟨switchStart, cases', midN, ?_, ?_⟩
  · exact hLowerCases
  · intro hFuel
    let fuel := fuel' - (cases'.length + 19)
    have hFuelShape : fuel' = fuel + cases'.length + 19 := by
      dsimp [fuel]
      exact (Nat.sub_add_cancel hFuel).symm
    let contract : EvmYul.Yul.Ast.YulContract :=
      { dispatcher := .Block [.Block inner], functions := functions }
    have hLowerFind :
        cases'.find? (fun entry => entry.1 == selector) = none :=
      lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_none_of_find_function
        reservedNames (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
        selector funcs cases' hLowerCases hFind
    have hTagsEq :
        cases'.map (·.1) = (buildSwitchSourceCases funcs).map (·.1) :=
      Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
        (buildSwitchSourceCases funcs) cases' hLowerCases
    have hTagsRange :
        ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
      intro tag body hmem
      have hTagMem : tag ∈ cases'.map (·.1) := by
        exact List.mem_map_of_mem (f := Prod.fst) hmem
      rw [hTagsEq] at hTagMem
      simp [buildSwitchSourceCases] at hTagMem
      rcases hTagMem with ⟨fn, hFn, hTag⟩
      subst hTag
      exact hFunctionSelectorsRange fn hFn
    have hPeel :
        contractDispatcherExecResult fuel'
            contract (initialState contract tx storage observableSlots) =
          EvmYul.Yul.exec (fuel + cases'.length + 13)
            (.Block
              [Backends.lowerNativeSwitchBlock
                (YulExpr.call "shr"
                  [YulExpr.lit Compiler.Constants.selectorShift,
                   YulExpr.call "calldataload" [YulExpr.lit 0]])
                (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                [nativeRevertZeroZeroStmt]])
            (some contract)
            ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
              "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
      rw [hFuelShape]
      have hPeelStructural :
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots) =
            EvmYul.Yul.exec (fuel + cases'.length + 13)
              (.Block
                [Backends.lowerNativeSwitchBlock
                  (YulExpr.call "shr"
                    [YulExpr.lit Compiler.Constants.selectorShift,
                     YulExpr.call "calldataload" [YulExpr.lit 0]])
                  (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                  [nativeRevertZeroZeroStmt]])
              (some contract)
              ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
        let contract' : EvmYul.Yul.Ast.YulContract :=
          { dispatcher := .Block [.Block inner], functions := functions }
        have hFuelShape' :
            fuel + cases'.length + 19 =
              Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))) := by
          omega
        have hDispatcherPeel :
            contractDispatcherExecResult (fuel + cases'.length + 19)
                contract' (initialState contract' tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner) (some contract')
                (nativeSwitchInitialOkState contract' tx storage observableSlots) := by
          rw [hFuelShape']
          change
            contractDispatcherExecResult
                (Nat.succ (Nat.succ (Nat.succ (fuel + cases'.length + 16))))
                { dispatcher := .Block [.Block inner], functions := functions }
                (initialState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots) =
              EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block inner)
                (some { dispatcher := .Block [.Block inner], functions := functions })
                (nativeSwitchInitialOkState
                  { dispatcher := .Block [.Block inner], functions := functions }
                  tx storage observableSlots)
          rw [contractDispatcherExecResult_block_dispatcher_eq_exec_block
            (Nat.succ (fuel + cases'.length + 16)) [.Block inner] functions
            tx storage observableSlots]
          rw [exec_singleton_block_eq_exec_block (fuel + cases'.length + 16) inner
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (nativeSwitchInitialOkState
              { dispatcher := .Block [.Block inner], functions := functions }
              tx storage observableSlots)]
        calc
          contractDispatcherExecResult (fuel + cases'.length + 19)
              contract (initialState contract tx storage observableSlots)
              = EvmYul.Yul.exec (fuel + cases'.length + 17)
                  (.Block inner) (some contract)
                  (nativeSwitchInitialOkState contract tx storage observableSlots) := hDispatcherPeel
          _ = EvmYul.Yul.exec (fuel + cases'.length + 17)
                (.Block
                  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
                      (some
                        (Backends.lowerExprNative
                          (YulExpr.call "iszero"
                            [YulExpr.call "lt"
                              [YulExpr.call "calldatasize" [],
                               YulExpr.lit 4]]))),
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative
                        (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]))
                      body1,
                   EvmYul.Yul.Ast.Stmt.If
                      (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
                      [Backends.lowerNativeSwitchBlock
                        (YulExpr.call "shr"
                          [YulExpr.lit Compiler.Constants.selectorShift,
                           YulExpr.call "calldataload" [YulExpr.lit 0]])
                        (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                        [nativeRevertZeroZeroStmt]]])
                (some contract)
                (nativeSwitchInitialOkState contract tx storage observableSlots) := by
              exact congrArg
                (fun body =>
                  EvmYul.Yul.exec (fuel + cases'.length + 17)
                    (.Block body) (some contract)
                    (nativeSwitchInitialOkState contract tx storage observableSlots))
                hInner
          _ = EvmYul.Yul.exec (fuel + cases'.length + 13)
                (.Block
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                    [nativeRevertZeroZeroStmt]])
                (some contract)
                ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
                  "__has_selector" (EvmYul.UInt256.ofNat 1)) := by
              have hExec :=
                exec_block_letSelector_if1Skip_if2Take_initialState_fuel
                  (fuel + cases'.length + 5) contract tx storage observableSlots
                  "__has_selector" body1
                  [Backends.lowerNativeSwitchBlock
                    (YulExpr.call "shr"
                      [YulExpr.lit Compiler.Constants.selectorShift,
                       YulExpr.call "calldataload" [YulExpr.lit 0]])
                    (Backends.freshNativeSwitchId reservedNames switchStart) cases'
                    [nativeRevertZeroZeroStmt]]
                  hNoWrap
              simpa only [Nat.add_assoc] using hExec
      exact hPeelStructural
    constructor
    · rw [hPeel]
      exact exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_error
        fuel selector (Backends.freshNativeSwitchId reservedNames switchStart) cases'
        contract tx storage observableSlots hSelector hLowerFind hSelectorRange
        hTagsRange
    · simp



end Compiler.Proofs.YulGeneration.Backends.Native
