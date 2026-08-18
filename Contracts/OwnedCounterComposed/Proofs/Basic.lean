import Contracts.OwnedCounterComposed.Spec
import Contracts.Ownable.Proofs.Basic
import Contracts.Ownable.Invariants
import Verity.Specs.Composition
import Verity.Proofs.Stdlib.Automation

namespace Contracts.OwnedCounterComposed.Proofs

open Verity
open Contracts.OwnedCounterComposed
open Contracts.OwnedCounterComposed.Spec
open Contracts.Ownable
open Contracts.Ownable.Proofs
open Contracts.Ownable.Invariants
open Verity.Specs.Composition

theorem increment_reverts_when_not_owner (s : ContractState)
    (h_not_owner : s.sender ≠ s.storageAddr (StorageSlot.slot owner)) :
    ∃ msg, increment.run s = ContractResult.revert msg s := by
  rcases onlyOwner_reverts s h_not_owner with ⟨msg, hrev⟩
  refine ⟨msg, ?_⟩
  simp only [increment]
  exact Verity.bind_run_revert onlyOwner _ s msg hrev

theorem increment_meets_spec_when_owner (s : ContractState)
    (h_owner : s.sender = s.storageAddr (StorageSlot.slot owner)) :
    let s' := (increment.run s).snd
    increment_spec s s' := by
  have hok := onlyOwner_ok s h_owner
  simp only [increment, Bind.bind]
  rw [bind_run_success onlyOwner _ s () hok]
  simp [increment_spec, count, getStorage, setStorage,
    ContractState.readSlot, ContractState.writeSlot,
    Verity.bind, Contract.run, ContractResult.snd,
    Specs.storageUpdateSpec, Specs.storageUnchangedExcept,
    Specs.sameAddrMapContext, Specs.sameStorageAddr, Specs.sameStorageMap,
    Specs.sameStorageArray, Specs.sameContext]
  simp_all [ContractState.storage_unfold, ContractState.storageAddr_unfold, ContractState.storageMap_unfold, ContractState.storageMapUint_unfold, ContractState.storageMap2_unfold, ContractState.transientStorage_unfold]

theorem increment_preserves_owner (s : ContractState)
    (h_owner : s.sender = s.storageAddr (StorageSlot.slot owner)) :
    ((increment.run s).snd).storageAddr (StorageSlot.slot owner)
      = s.storageAddr (StorageSlot.slot owner) := by
  have hok := onlyOwner_ok s h_owner
  simp only [increment, Bind.bind]
  rw [bind_run_success onlyOwner _ s () hok]
  simp [count, getStorage, setStorage, ContractState.readSlot, ContractState.writeSlot,
    Verity.bind, Contract.run, ContractResult.snd, ContractState.storageAddr]

theorem increment_writes_only_count (s : ContractState)
    (h_owner : s.sender = s.storageAddr (StorageSlot.slot owner)) :
    WritesOnly countFootprint s (increment.run s).snd := by
  have hok := onlyOwner_ok s h_owner
  simp only [increment, Bind.bind]
  rw [bind_run_success onlyOwner _ s () hok]
  simp [countFootprint, WritesOnly, count, getStorage, setStorage,
    ContractState.readSlot, ContractState.writeSlot,
    Verity.bind, Contract.run, ContractResult.snd, Specs.sameContext]
  simp_all [ContractState.storage_unfold, ContractState.storageAddr_unfold, ContractState.storageMap_unfold, ContractState.storageMapUint_unfold, ContractState.storageMap2_unfold, ContractState.transientStorage_unfold]

theorem increment_preserves_ownable_inv (s : ContractState)
    (h_owner : s.sender = s.storageAddr (StorageSlot.slot owner))
    (hInv : Inv s) :
    Inv (increment.run s).snd :=
  writesOnly_preserves_other_inv
    countFootprint
    { addrSlots := [StorageSlot.slot owner] }
    (disjoint_uint_addr (StorageSlot.slot count) (StorageSlot.slot owner))
    Inv inv_depends_only_on_footprint
    s (increment.run s).snd
    (increment_writes_only_count s h_owner)
    hInv

theorem getCount_meets_spec (s : ContractState) :
    getCount_spec ((getCount).run s).fst s := by
  simp [getCount, getCount_spec, count, getStorage, ContractState.readSlot,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run]

end Contracts.OwnedCounterComposed.Proofs
