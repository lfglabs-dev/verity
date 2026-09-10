import Verity.Specs.Common
import Verity.Specs.Common.Sum
import Verity.EVM.Uint256
import Contracts.VaultFromSolidity.VaultFromSolidity

namespace Contracts.VaultFromSolidity.Spec

open Verity
open Verity.Specs
open Verity.EVM.Uint256

def storageUnchangedExceptAssetSlots (s s' : ContractState) : Prop :=
  ∀ slotIdx : Nat, slotIdx ≠ 0 → slotIdx ≠ 1 → s'.storage slotIdx = s.storage slotIdx

def sameStorageExceptAssetSlots (s s' : ContractState) : Prop :=
  storageUnchangedExceptAssetSlots s s' ∧
  Specs.sameStorageAddr s s' ∧
  Specs.sameContext s s'

def deposit_spec (assets : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) assets ∧
  s'.storage 0 = add (s.storage 0) assets ∧
  s'.storage 1 = add (s.storage 1) assets ∧
  Specs.storageMapUnchangedExceptKeyAtSlot 2 s.sender s s' ∧
  sameStorageExceptAssetSlots s s'

def withdraw_spec (shares : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 2 s.sender = sub (s.storageMap 2 s.sender) shares ∧
  s'.storage 0 = sub (s.storage 0) shares ∧
  s'.storage 1 = sub (s.storage 1) shares ∧
  Specs.storageMapUnchangedExceptKeyAtSlot 2 s.sender s s' ∧
  sameStorageExceptAssetSlots s s'

/-- Exact post-state, including Verity's ghost key-enumeration metadata. -/
def accountingState (s : ContractState) (shares assets supply : Uint256) : ContractState :=
  let mapped := { s.writeMap 2 s.sender shares with
    knownAddresses := fun slotIdx => if slotIdx == 2 then
      (s.knownAddresses slotIdx).insert s.sender else s.knownAddresses slotIdx }
  (mapped.writeSlot 0 assets).writeSlot 1 supply

def deposit_execution (s : ContractState) (amount : Uint256) : Prop :=
  (Contracts.VaultFromSolidity.deposit amount).run s = ContractResult.success ()
    (accountingState s (s.readMap 2 s.sender + amount)
      (s.readSlot 0 + amount)
      (s.readSlot 1 + amount))

def withdraw_execution (s : ContractState) (amount : Uint256) : Prop :=
  (Contracts.VaultFromSolidity.withdraw amount).run s = ContractResult.success ()
    (accountingState s (s.readMap 2 s.sender - amount)
      (s.readSlot 0 - amount)
      (s.readSlot 1 - amount))

def balance_execution (s : ContractState) (account : Address) : Prop :=
  (Contracts.VaultFromSolidity.balanceOf account).run s =
    ContractResult.success (s.readMap 2 account) s

end Contracts.VaultFromSolidity.Spec
