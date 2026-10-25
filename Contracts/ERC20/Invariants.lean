/-
  State invariants for the ERC20 foundation scaffold.
-/

import Verity.Specs.Common
import Verity.Specs.Common.Sum
import Contracts.ERC20.ERC20
import Verity.Proofs.Stdlib.Math
import Verity.Proofs.Stdlib.Automation

namespace Contracts.ERC20.Invariants

open Verity
open Contracts
open Verity.Specs.Common (sumBalances balancesFinite)
open Verity.Stdlib.Math (requireSomeUint safeAdd)

/-! ## State Invariants -/

/-- Basic well-formedness constraints for contract context and owner slot. -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonzero : s.sender ≠ 0
  contract_nonzero : s.thisAddress ≠ 0
  owner_nonzero : s.storageAddr ERC20.owner.slot ≠ 0

/-- ERC20 state well-formedness without any vacuous `s.txOrigin = 0` requirement,
using typed slot references. -/
structure WellFormedERC20State (s : ContractState) : Prop where
  sender_nonzero : s.sender ≠ 0
  contract_nonzero : s.thisAddress ≠ 0
  owner_nonzero : s.storageAddr ERC20.owner.slot ≠ 0

/-- `WellFormedState` implies `WellFormedERC20State`. -/
theorem WellFormedState_implies_WellFormedERC20State (s : ContractState)
    (h : WellFormedState s) : WellFormedERC20State s :=
  ⟨h.sender_nonzero, h.contract_nonzero, h.owner_nonzero⟩

/-- Total tracked balance at balances slot (`ERC20.balances.slot`). -/
def totalBalance (s : ContractState) : Uint256 :=
  sumBalances ERC20.balances.slot (s.knownAddresses ERC20.balances.slot) s.storageMap

/-- Global supply matches tracked balances over known addresses. -/
def supply_matches_balances (s : ContractState) : Prop :=
  totalBalance s = s.storage ERC20.totalSupply.slot

/-- Mapping isolation for balances slot updates. -/
def balances_slot_isolated (s s' : ContractState) : Prop :=
  ∀ slotIdx : Nat, slotIdx ≠ ERC20.balances.slot → ∀ addr : Address, s'.storageMap slotIdx addr = s.storageMap slotIdx addr

/-- Mapping isolation for allowances slot updates. -/
def allowances_slot_isolated (s s' : ContractState) : Prop :=
  ∀ slotIdx : Nat, slotIdx ≠ ERC20.allowances.slot →
    ∀ ownerAddr spender : Address, s'.storageMap2 slotIdx ownerAddr spender = s.storageMap2 slotIdx ownerAddr spender

/-- Context fields are preserved by state transitions. -/
abbrev context_preserved := Specs.sameContext

/-- Sum-preservation statement for transfer operations. -/
def transfer_preserves_total (s s' : ContractState) : Prop :=
  totalBalance s' = totalBalance s

/-- Approve only updates allowance map and not balances or total supply. -/
def approve_is_balance_neutral (s s' : ContractState) : Prop :=
  s'.storage = s.storage ∧
  s'.storageMap = s.storageMap

/-! ## Preservation of `WellFormedERC20State` -/

private def PreservesWFSuccess {α : Type} (m : Contract α) : Prop :=
  ∀ s a s', WellFormedERC20State s → m s = ContractResult.success a s' → WellFormedERC20State s'

private theorem wf_runState {α : Type} {m : Contract α} (hm : PreservesWFSuccess m)
    (s : ContractState) (h : WellFormedERC20State s) :
    WellFormedERC20State (m.runState s) := by
  unfold Contract.runState
  cases h_m : m s with
  | success a s' => exact hm s a s' h h_m
  | «revert» msg s' => exact h

private theorem wf_bind {α β : Type} {m : Contract α} {k : α → Contract β}
    (hm : PreservesWFSuccess m) (hk : ∀ a, PreservesWFSuccess (k a)) :
    PreservesWFSuccess (Verity.bind m k) := by
  intro s b s'' hs h_bind
  unfold Verity.bind at h_bind
  cases h_m : m s with
  | success a s' =>
    rw [h_m] at h_bind
    exact hk a s' b s'' (hm s a s' hs h_m) h_bind
  | «revert» msg s' =>
    rw [h_m] at h_bind
    cases h_bind

private theorem wf_pure {α : Type} (a : α) : PreservesWFSuccess (Verity.pure a) := by
  intro s _ s' hs h; cases h; exact hs

private theorem wf_msgSender : PreservesWFSuccess msgSender := by
  intro s _ s' hs h; cases h; exact hs

private theorem wf_getStorage (sSlot : StorageSlot Core.Uint256) : PreservesWFSuccess (getStorage sSlot) := by
  intro s _ s' hs h; cases h; exact hs

private theorem wf_getStorageAddr (sSlot : StorageSlot Address) : PreservesWFSuccess (getStorageAddr sSlot) := by
  intro s _ s' hs h; cases h; exact hs

private theorem wf_getMapping (sSlot : StorageSlot (Address → Core.Uint256)) (k : Address) :
    PreservesWFSuccess (getMapping sSlot k) := by
  intro s _ s' hs h; cases h; exact hs

private theorem wf_getMapping2 (sSlot : StorageSlot (Address → Address → Core.Uint256)) (k1 k2 : Address) :
    PreservesWFSuccess (getMapping2 sSlot k1 k2) := by
  intro s _ s' hs h; cases h; exact hs

private theorem wf_setStorage (sSlot : StorageSlot Core.Uint256) (v : Core.Uint256) :
    PreservesWFSuccess (setStorage sSlot v) := by
  intro s _ s' hs h; cases h; exact ⟨hs.sender_nonzero, hs.contract_nonzero, hs.owner_nonzero⟩

private theorem wf_setMapping (sSlot : StorageSlot (Address → Core.Uint256)) (k : Address) (v : Core.Uint256) :
    PreservesWFSuccess (setMapping sSlot k v) := by
  intro s _ s' hs h; cases h; exact ⟨hs.sender_nonzero, hs.contract_nonzero, hs.owner_nonzero⟩

private theorem wf_setMapping2 (sSlot : StorageSlot (Address → Address → Core.Uint256)) (k1 k2 : Address) (v : Core.Uint256) :
    PreservesWFSuccess (setMapping2 sSlot k1 k2 v) := by
  intro s _ s' hs h; cases h; exact ⟨hs.sender_nonzero, hs.contract_nonzero, hs.owner_nonzero⟩

private theorem wf_require (cond : Bool) (msg : String) :
    PreservesWFSuccess (Verity.require cond msg) := by
  intro s _ s' hs h; cases cond <;> cases h; exact hs

private theorem wf_requireSomeUint (opt : Option Core.Uint256) (msg : String) :
    PreservesWFSuccess (requireSomeUint opt msg) := by
  intro s _ s' hs h; cases opt <;> cases h; exact hs

/-- `ERC20.mint` preserves `WellFormedERC20State`. -/
theorem mint_preserves_wellFormedERC20State (s : ContractState) (toAddr : Address) (amount : Uint256)
    (h : WellFormedERC20State s) :
    WellFormedERC20State ((ERC20.mint toAddr amount).runState s) := by
  refine wf_runState ?_ s h
  unfold ERC20.mint
  simp only [Bind.bind]
  exact wf_bind wf_msgSender fun _ =>
    wf_bind (wf_getStorageAddr _) fun _ =>
    wf_bind (wf_require _ _) fun _ =>
    wf_bind (wf_getMapping _ _) fun _ =>
    wf_bind (wf_requireSomeUint _ _) fun _ =>
    wf_bind (wf_getStorage _) fun _ =>
    wf_bind (wf_requireSomeUint _ _) fun _ =>
    wf_bind (wf_setMapping _ _ _) fun _ =>
    wf_setStorage _ _

/-- `ERC20.transfer` preserves `WellFormedERC20State`. -/
theorem transfer_preserves_wellFormedERC20State (s : ContractState) (toAddr : Address) (amount : Uint256)
    (h : WellFormedERC20State s) :
    WellFormedERC20State ((ERC20.transfer toAddr amount).runState s) := by
  refine wf_runState ?_ s h
  unfold ERC20.transfer
  simp only [Bind.bind, Pure.pure]
  refine wf_bind wf_msgSender fun _ =>
    wf_bind (wf_getMapping _ _) fun _ =>
    wf_bind (wf_require _ _) fun _ => ?_
  split
  · exact wf_pure ()
  · exact wf_bind (wf_getMapping _ _) fun _ =>
      wf_bind (wf_requireSomeUint _ _) fun _ =>
      wf_bind (wf_setMapping _ _ _) fun _ =>
      wf_setMapping _ _ _

/-- `ERC20.approve` preserves `WellFormedERC20State`. -/
theorem approve_preserves_wellFormedERC20State (s : ContractState) (spender : Address) (amount : Uint256)
    (h : WellFormedERC20State s) :
    WellFormedERC20State ((ERC20.approve spender amount).runState s) := by
  refine wf_runState ?_ s h
  unfold ERC20.approve
  simp only [Bind.bind]
  exact wf_bind wf_msgSender fun _ => wf_setMapping2 _ _ _ _

/-- `ERC20.transferFrom` preserves `WellFormedERC20State`. -/
theorem transferFrom_preserves_wellFormedERC20State
    (s : ContractState) (fromAddr toAddr : Address) (amount : Uint256)
    (h : WellFormedERC20State s) :
    WellFormedERC20State ((ERC20.transferFrom fromAddr toAddr amount).runState s) := by
  refine wf_runState ?_ s h
  unfold ERC20.transferFrom
  simp only [Bind.bind, Pure.pure]
  refine wf_bind wf_msgSender fun _ =>
    wf_bind (wf_getMapping2 _ _ _) fun _ =>
    wf_bind (wf_require _ _) fun _ =>
    wf_bind (wf_getMapping _ _) fun _ =>
    wf_bind (wf_require _ _) fun _ => ?_
  split
  · refine wf_bind (wf_pure ()) fun _ => ?_
    split
    · exact wf_pure ()
    · exact wf_setMapping2 _ _ _ _
  · refine wf_bind (wf_getMapping _ _) fun _ =>
      wf_bind (wf_requireSomeUint _ _) fun _ =>
      wf_bind (wf_setMapping _ _ _) fun _ =>
      wf_bind (wf_setMapping _ _ _) fun _ => ?_
    split
    · exact wf_pure ()
    · exact wf_setMapping2 _ _ _ _

end Contracts.ERC20.Invariants
