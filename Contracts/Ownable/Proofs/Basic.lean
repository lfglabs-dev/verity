import Contracts.Ownable.Spec
import Contracts.Ownable.Invariants
import Verity.Proofs.Stdlib.Automation
import Verity.Specs.Composition

namespace Contracts.Ownable.Proofs

open Verity
open Contracts.Ownable
open Contracts.Ownable.Spec
open Contracts.Ownable.Invariants
open Verity.Proofs.Stdlib.Automation (address_beq_false_of_ne)
open Verity.Specs.Composition

private theorem owner_slot_zero : StorageSlot.slot owner = 0 := rfl

theorem onlyOwner_ok (s : ContractState)
    (h_owner : s.sender = s.storageAddr (StorageSlot.slot owner)) :
    onlyOwner.run s = ContractResult.success () s := by
  simp [onlyOwner, owner, msgSender, getStorageAddr, ContractState.readAddrSlot,
    Verity.require, Verity.bind, Bind.bind, Contract.run, h_owner]

theorem onlyOwner_reverts (s : ContractState)
    (h_not_owner : s.sender ≠ s.storageAddr (StorageSlot.slot owner)) :
    ∃ msg, onlyOwner.run s = ContractResult.revert msg s :=
  ⟨"Caller is not the owner", by
    have h : s.sender ≠ s.storageAddr 0 := owner_slot_zero ▸ h_not_owner
    simp [onlyOwner, owner, msgSender, getStorageAddr, ContractState.readAddrSlot,
      Verity.require, Verity.bind, Bind.bind, Contract.run,
      address_beq_false_of_ne s.sender (s.storageAddr 0) h]⟩

theorem transferOwnership_writes_only (s : ContractState) (newOwner : Address)
    (h_owner : s.sender = s.storageAddr (StorageSlot.slot owner)) :
    WritesOnly footprint s ((transferOwnership newOwner).run s).snd := by
  simp [transferOwnership, footprint, WritesOnly, owner,
    msgSender, getStorageAddr, setStorageAddr, ContractState.readAddrSlot,
    ContractState.writeAddrSlot, Verity.require, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd, h_owner, Specs.sameContext,
    ContractState.storage, ContractState.storageAddr, ContractState.storageMap,
    ContractState.storageMapUint, ContractState.storageMap2, ContractState.transientStorage]
  intro _ hneq heq
  exact (hneq heq).elim

theorem transferOwnership_meets_spec_when_owner (s : ContractState) (newOwner : Address)
    (h_owner : s.sender = s.storageAddr (StorageSlot.slot owner)) :
    let s' := ((transferOwnership newOwner).run s).snd
    transferOwnership_spec newOwner s s' := by
  simp [transferOwnership, transferOwnership_spec, owner,
    msgSender, getStorageAddr, setStorageAddr, ContractState.readAddrSlot,
    ContractState.writeAddrSlot, Verity.require, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd, h_owner,
    Specs.storageAddrUpdateSpec, Specs.storageAddrUnchangedExcept,
    Specs.sameStorageMapContext, Specs.sameStorage, Specs.sameStorageMap,
    Specs.sameStorageArray, Specs.sameContext,
    ContractState.storage, ContractState.storageAddr, ContractState.storageMap,
    ContractState.storageMapUint, ContractState.storageMap2, ContractState.transientStorage]
  intro _ hneq heq
  exact (hneq heq).elim

theorem getOwner_meets_spec (s : ContractState) :
    getOwner_spec ((getOwner).run s).fst s := by
  simp [getOwner, getOwner_spec, owner, getStorageAddr, ContractState.readAddrSlot,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run]

theorem constructor_sets_owner (s : ContractState) (initialOwner : Address) :
    ((«constructor» initialOwner).run s).snd.storageAddr (StorageSlot.slot owner)
      = initialOwner := by
  simp [«constructor», owner, setStorageAddr, ContractState.writeAddrSlot,
    Contract.run, ContractResult.snd]

end Contracts.Ownable.Proofs
