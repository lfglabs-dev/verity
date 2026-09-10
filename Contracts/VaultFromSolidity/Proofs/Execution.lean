import Contracts.VaultFromSolidity.Spec

namespace Contracts.VaultFromSolidity.Proofs.Execution
open Verity
open Verity.Stdlib.Math

macro "reduce_vault" : tactic => `(tactic|
  simp_all [Spec.deposit_execution, Spec.withdraw_execution, Spec.balance_execution,
    Spec.accountingState, deposit, withdraw, balanceOf, totalAssets, totalSupply,
    shareBalances, totalAssetsSlot, totalSupplySlot, shareBalancesSlot,
    Contract.run, Bind.bind, Pure.pure, Verity.instMonadContract, Verity.bind, Verity.pure,
    msgValue, msgSender, Verity.require,
    getStorage, setStorage, getMapping, setMapping, requireSomeUint, safeSub,
    Verity.EVM.Uint256.sub, Nat.not_le_of_lt, Nat.not_lt_of_ge,
    ContractState.readSlot, ContractState.writeSlot, ContractState.readMap,
    ContractState.writeMap, ContractState.storage, ContractState.storageMap])

theorem balance_meets_spec (s : ContractState) (account : Address)
    (h0 : s.msgValue = 0) : Spec.balance_execution s account := by
  reduce_vault

theorem deposit_meets_spec (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : safeAdd (s.readMap 2 s.sender) amount = some (s.readMap 2 s.sender + amount))
    (ha : safeAdd (s.readSlot 0) amount = some (s.readSlot 0 + amount))
    (ht : safeAdd (s.readSlot 1) amount = some (s.readSlot 1 + amount)) :
    Spec.deposit_execution s amount := by
  reduce_vault

theorem withdraw_meets_spec (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : amount.val ≤ (s.readMap 2 s.sender).val)
    (ha : amount.val ≤ (s.readSlot 0).val)
    (ht : amount.val ≤ (s.readSlot 1).val) : Spec.withdraw_execution s amount := by
  reduce_vault

theorem deposit_nonpayable (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue.val ≠ 0) :
    (deposit amount).run s = ContractResult.revert "Nonpayable" s := by
  reduce_vault

/-- A late failing addition rolls back the earlier mapping and asset writes. -/
theorem deposit_late_overflow_rollback (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : safeAdd (s.readMap 2 s.sender) amount = some (s.readMap 2 s.sender + amount))
    (ha : safeAdd (s.readSlot 0) amount = some (s.readSlot 0 + amount))
    (ht : safeAdd (s.readSlot 1) amount = none) :
    (deposit amount).run s = ContractResult.revert "Panic(0x11)" s := by
  reduce_vault

theorem withdraw_insufficient_shares (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hs : (s.readMap 2 s.sender).val < amount.val) :
    (withdraw amount).run s = ContractResult.revert "InsufficientShares()" s := by
  reduce_vault

/-- Successful deposit changes no unrelated logical storage key. -/
theorem deposit_frame (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : safeAdd (s.readMap 2 s.sender) amount = some (s.readMap 2 s.sender + amount))
    (ha : safeAdd (s.readSlot 0) amount = some (s.readSlot 0 + amount))
    (ht : safeAdd (s.readSlot 1) amount = some (s.readSlot 1 + amount))
    (key : Verity.StorageKey) (hk0 : key ≠ .slot 0) (hk1 : key ≠ .slot 1)
    (hkm : key ≠ .map 2 s.sender) :
    ((deposit amount).run s).snd.storageWords key = s.storageWords key := by
  have h := deposit_meets_spec s amount h0 hs ha ht
  rw [Spec.deposit_execution] at h
  rw [h]
  simp [Spec.accountingState, ContractState.writeSlot, ContractState.writeMap, hk0, hk1, hkm]

theorem totalAssets_getter (s : ContractState) (h0 : s.msgValue = 0) :
    totalAssets.run s = ContractResult.success (s.readSlot 0) s := by
  reduce_vault

theorem totalSupply_getter (s : ContractState) (h0 : s.msgValue = 0) :
    totalSupply.run s = ContractResult.success (s.readSlot 1) s := by
  reduce_vault

theorem shareBalances_getter (s : ContractState) (account : Address) (h0 : s.msgValue = 0) :
    (shareBalances account).run s = ContractResult.success (s.readMap 2 account) s := by
  reduce_vault

theorem withdraw_nonpayable (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue.val ≠ 0) :
    (withdraw amount).run s = ContractResult.revert "Nonpayable" s := by
  reduce_vault

theorem withdraw_insufficient_assets (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hs : amount.val ≤ (s.readMap 2 s.sender).val)
    (ha : (s.readSlot 0).val < amount.val) :
    (withdraw amount).run s = ContractResult.revert "InsufficientAssets()" s := by
  reduce_vault

theorem withdraw_insufficient_supply (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hs : amount.val ≤ (s.readMap 2 s.sender).val)
    (ha : amount.val ≤ (s.readSlot 0).val) (ht : (s.readSlot 1).val < amount.val) :
    (withdraw amount).run s = ContractResult.revert "InsufficientSupply()" s := by
  reduce_vault

theorem deposit_existing_spec (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : safeAdd (s.readMap 2 s.sender) amount = some (s.readMap 2 s.sender + amount))
    (ha : safeAdd (s.readSlot 0) amount = some (s.readSlot 0 + amount))
    (ht : safeAdd (s.readSlot 1) amount = some (s.readSlot 1 + amount)) :
    Spec.deposit_spec amount s ((deposit amount).run s).snd := by
  have h := deposit_meets_spec s amount h0 hs ha ht
  rw [Spec.deposit_execution] at h
  rw [h]
  simp +contextual [Spec.deposit_spec, Spec.accountingState, Spec.sameStorageExceptAssetSlots,
    Spec.storageUnchangedExceptAssetSlots, Specs.sameStorageAddr, Specs.sameContext,
    Specs.storageMapUnchangedExceptKeyAtSlot, Specs.storageMapUnchangedExceptKey,
    Specs.storageMapUnchangedExceptSlot, ContractResult.snd, ContractState.readSlot,
    ContractState.readMap, ContractState.writeSlot, ContractState.writeMap,
    ContractState.storage, ContractState.storageMap,
    Verity.EVM.Uint256.add]
  repeat' constructor
  all_goals exact Verity.Core.Uint256.add_comm _ _

theorem withdraw_existing_spec (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : amount.val ≤ (s.readMap 2 s.sender).val)
    (ha : amount.val ≤ (s.readSlot 0).val)
    (ht : amount.val ≤ (s.readSlot 1).val) :
    Spec.withdraw_spec amount s ((withdraw amount).run s).snd := by
  have h := withdraw_meets_spec s amount h0 hs ha ht
  rw [Spec.withdraw_execution] at h
  rw [h]
  simp +contextual [Spec.withdraw_spec, Spec.accountingState, Spec.sameStorageExceptAssetSlots,
    Spec.storageUnchangedExceptAssetSlots, Specs.sameStorageAddr, Specs.sameContext,
    Specs.storageMapUnchangedExceptKeyAtSlot, Specs.storageMapUnchangedExceptKey,
    Specs.storageMapUnchangedExceptSlot, ContractResult.snd, ContractState.readSlot,
    ContractState.readMap, ContractState.writeSlot, ContractState.writeMap,
    ContractState.storage, ContractState.storageMap,
    Verity.EVM.Uint256.sub]
  repeat' constructor

end Contracts.VaultFromSolidity.Proofs.Execution
