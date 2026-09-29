import Verity.Core

/-!
# Hop storage namespacing smoke tests (G24, #2440)

A distinct-address hop (`Contract.hopCall` / `Contract.hopCallView`) gives the
callee its own world on every word-valued storage channel: scalar slots via
`StorageKey.contractSlot`, and address slots / transient slots / mappings via
`StorageKey.scoped`. The caller's same-numbered address slots and mapping
entries are never visible to, nor clobbered by, the callee.
-/

namespace Contracts.Smoke.HopNamespace

open Verity

def addrA : Address := (10 : Address)
def addrB : Address := (11 : Address)
def addrU : Address := (21 : Address)
def addrV : Address := (22 : Address)

def balances : StorageSlot (Address → Uint256) := ⟨3⟩
def owner : StorageSlot Address := ⟨5⟩

/-- Caller A: `owner = addrU`, `balances[addrU] = 50`. -/
def s0 : ContractState :=
  ({ defaultState with thisAddress := addrA, sender := (1 : Address) }.writeAddrSlot
    owner.slot addrU).writeMap balances.slot addrU 50

def readOwner : Contract Address := getStorageAddr owner

def readBalance : Contract Uint256 := getMapping balances addrU

/-- Callee B body: write its own `balances[addrU]` and `owner`. -/
def calleeWrite : Contract Unit := fun s =>
  match setMapping balances addrU 77 s with
  | .success _ s' => setStorageAddr owner addrV s'
  | .revert msg s' => .revert msg s'

/-- Caller state after one successful mutating hop into B. -/
def s1 : ContractState := (Contract.hopCall addrB calleeWrite s0).getState

/-! ## (a) Callee address slot is its own -/

/-- Before any hop, B's address slot 5 is empty even though A's holds `addrU`. -/
theorem callee_addr_slot_not_callers :
    (Contract.hopCallView addrB readOwner s0).getValue? = some (0 : Address) := by
  decide

theorem caller_addr_slot_is_addrU : s0.readAddrSlot owner.slot = addrU := by
  decide

/-- After B writes its own `owner`, a view hop into B reads B's value. -/
theorem callee_reads_own_addr_slot :
    (Contract.hopCallView addrB readOwner s1).getValue? = some addrV := by
  decide

/-- The read goes through `.scoped callee (.addr n)`. -/
theorem callee_addr_read_is_scoped :
    (s1.enterHop addrA addrB).readAddrSlot owner.slot =
      wordToAddress (s1.storageWords (.scoped addrB.toNat (.addr owner.slot))) :=
  ContractState.enterHop_readAddrSlot s1 addrA addrB owner.slot

/-! ## (b) Callee mapping writes stay in the callee's world -/

theorem caller_mapping_unchanged_after_hop :
    s1.readMap balances.slot addrU = 50 := by
  decide

theorem caller_addr_slot_unchanged_after_hop :
    s1.readAddrSlot owner.slot = addrU := by
  decide

theorem callee_mapping_write_parked_scoped :
    s1.storageWords (.scoped addrB.toNat (.map balances.slot addrU)) = 77 := by
  decide

theorem callee_mapping_write_visible_to_second_hop :
    (Contract.hopCallView addrB readBalance s1).getValue? = some (77 : Uint256) := by
  decide

/-! ## (c) Nested reentrant hop A → B → A sees A's own world -/

/-- B body: overwrite its own `balances[addrU]`, then call back into A and read
    A's `balances[addrU]` and `owner`. -/
def reenterRead : Contract (Uint256 × Address) := fun s =>
  match setMapping balances addrU 99 s with
  | .success _ s' =>
      Contract.hopCallView addrA (fun t =>
        match readBalance t with
        | .success m t' =>
            match readOwner t' with
            | .success a t'' => .success (m, a) t''
            | .revert msg t'' => .revert msg t''
        | .revert msg t' => .revert msg t') s'
  | .revert msg s' => .revert msg s'

theorem nested_reentrant_hop_sees_callers_world :
    (Contract.hopCall addrB reenterRead s1).getValue? = some ((50 : Uint256), addrU) := by
  decide

/-- B body: call back into A with a mutating hop that sets A's `balances[addrU]`. -/
def reenterWrite : Contract Unit :=
  Contract.hopCall addrA (setMapping balances addrU 60)

theorem nested_reentrant_write_lands_in_caller_world :
    let s2 := (Contract.hopCall addrB reenterWrite s1).getState
    s2.readMap balances.slot addrU = 60 ∧
      s2.storageWords (.scoped addrB.toNat (.map balances.slot addrU)) = 77 := by
  decide

/-! ## (d) Reverting hop leaves all storage unchanged -/

def calleeWriteThenRevert : Contract Unit := fun s =>
  match setMapping balances addrU 1 s with
  | .success _ s' => .revert "callee revert" s'
  | .revert msg s' => .revert msg s'

theorem reverting_hop_restores_snapshot :
    Contract.hopCall addrB calleeWriteThenRevert s1 =
      ContractResult.revert "callee revert" s1 := by
  unfold Contract.hopCall
  rfl

theorem reverting_hop_mapping_unchanged :
    (Contract.hopCall addrB calleeWriteThenRevert s1).getState.readMap balances.slot addrU = 50 ∧
      (Contract.hopCall addrB calleeWriteThenRevert s1).getState.storageWords
        (.scoped addrB.toNat (.map balances.slot addrU)) = 77 := by
  decide

end Contracts.Smoke.HopNamespace
