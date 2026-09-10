import Contracts.Vault.Spec
import Contracts.Vault.Implementations

namespace Contracts.Vault.Execution
open Verity
open Verity.Stdlib.Math

/-- The same proof tactic unfolds either implementation; it does not assume
that the imported body is equal to the handwritten one. -/
macro "reduce_vault" : tactic => `(tactic|
  simp_all [Spec.deposit_execution, Spec.withdraw_execution, Spec.balance_execution,
    Spec.accountingState, Implementation.deposit, Implementation.withdraw,
    Implementation.balanceOf, Implementation.totalAssets, Implementation.totalSupply,
    Implementation.shareBalances, nonpayableEntry,
    Vault.deposit, Vault.withdraw, Vault.balanceOf, Vault.totalAssets, Vault.totalSupply,
    Vault.totalAssetsSlot, Vault.totalSupplySlot, Vault.shareBalancesSlot,
    Solidity.deposit, Solidity.withdraw, Solidity.balanceOf, Solidity.totalAssets,
    Solidity.totalSupply, Solidity.shareBalances,
    Solidity.totalAssetsSlot, Solidity.totalSupplySlot, Solidity.shareBalancesSlot,
    Contract.run, Bind.bind, Pure.pure, Verity.instMonadContract, Verity.bind, Verity.pure,
    msgValue, msgSender, Verity.require, revertCustomError, formatCustomError, getStorage, setStorage, getMapping, setMapping,
    requireSomeUint, safeSub, Verity.EVM.Uint256.sub, Nat.not_le_of_lt, Nat.not_lt_of_ge,
    ContractState.readSlot, ContractState.writeSlot, ContractState.readMap,
    ContractState.writeMap, ContractState.storage, ContractState.storageMap])

theorem balance_meets_spec (impl : Implementation) (s : ContractState) (account : Address)
    (h0 : s.msgValue = 0) : Spec.balance_execution impl.balanceOf s account := by
  cases impl <;> reduce_vault

theorem deposit_meets_spec (impl : Implementation) (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : safeAdd (s.readMap 2 s.sender) amount = some (s.readMap 2 s.sender + amount))
    (ha : safeAdd (s.readSlot 0) amount = some (s.readSlot 0 + amount))
    (ht : safeAdd (s.readSlot 1) amount = some (s.readSlot 1 + amount)) :
    Spec.deposit_execution impl.deposit s amount := by
  cases impl <;> reduce_vault

theorem withdraw_meets_spec (impl : Implementation) (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : amount.val ≤ (s.readMap 2 s.sender).val)
    (ha : amount.val ≤ (s.readSlot 0).val)
    (ht : amount.val ≤ (s.readSlot 1).val) : Spec.withdraw_execution impl.withdraw s amount := by
  cases impl <;> reduce_vault
  rfl

theorem deposit_nonpayable (impl : Implementation) (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue.val ≠ 0) :
    (impl.deposit amount).run s = ContractResult.revert "Nonpayable" s := by
  cases impl <;> reduce_vault

/-- A late failing addition rolls back the earlier mapping and asset writes. -/
theorem deposit_late_overflow_rollback (impl : Implementation) (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : safeAdd (s.readMap 2 s.sender) amount = some (s.readMap 2 s.sender + amount))
    (ha : safeAdd (s.readSlot 0) amount = some (s.readSlot 0 + amount))
    (ht : safeAdd (s.readSlot 1) amount = none) :
    (impl.deposit amount).run s = ContractResult.revert "Panic(0x11)" s := by
  cases impl <;> reduce_vault

theorem withdraw_insufficient_shares (impl : Implementation) (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hs : (s.readMap 2 s.sender).val < amount.val) :
    (impl.withdraw amount).run s = ContractResult.revert "InsufficientShares()" s := by
  cases impl <;> reduce_vault

/-- Successful deposit changes no unrelated logical storage key. -/
theorem deposit_frame (impl : Implementation) (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : safeAdd (s.readMap 2 s.sender) amount = some (s.readMap 2 s.sender + amount))
    (ha : safeAdd (s.readSlot 0) amount = some (s.readSlot 0 + amount))
    (ht : safeAdd (s.readSlot 1) amount = some (s.readSlot 1 + amount))
    (key : Verity.StorageKey) (hk0 : key ≠ .slot 0) (hk1 : key ≠ .slot 1)
    (hkm : key ≠ .map 2 s.sender) :
    ((impl.deposit amount).run s).snd.storageWords key = s.storageWords key := by
  have h := deposit_meets_spec impl s amount h0 hs ha ht
  rw [Spec.deposit_execution] at h
  rw [h]
  simp [Spec.accountingState, ContractState.writeSlot, ContractState.writeMap, hk0, hk1, hkm]

theorem totalAssets_getter (impl : Implementation) (s : ContractState) (h0 : s.msgValue = 0) :
    impl.totalAssets.run s = ContractResult.success (s.readSlot 0) s := by
  cases impl <;> reduce_vault

theorem totalSupply_getter (impl : Implementation) (s : ContractState) (h0 : s.msgValue = 0) :
    impl.totalSupply.run s = ContractResult.success (s.readSlot 1) s := by
  cases impl <;> reduce_vault

theorem shareBalances_getter (impl : Implementation) (s : ContractState) (account : Address) (h0 : s.msgValue = 0) :
    (impl.shareBalances account).run s = ContractResult.success (s.readMap 2 account) s := by
  cases impl <;> reduce_vault

theorem withdraw_nonpayable (impl : Implementation) (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue.val ≠ 0) :
    (impl.withdraw amount).run s = ContractResult.revert "Nonpayable" s := by
  cases impl <;> reduce_vault

theorem withdraw_insufficient_assets (impl : Implementation) (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hs : amount.val ≤ (s.readMap 2 s.sender).val)
    (ha : (s.readSlot 0).val < amount.val) :
    (impl.withdraw amount).run s = ContractResult.revert "InsufficientAssets()" s := by
  cases impl <;> reduce_vault

theorem withdraw_insufficient_supply (impl : Implementation) (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hs : amount.val ≤ (s.readMap 2 s.sender).val)
    (ha : amount.val ≤ (s.readSlot 0).val) (ht : (s.readSlot 1).val < amount.val) :
    (impl.withdraw amount).run s = ContractResult.revert "InsufficientSupply()" s := by
  cases impl <;> reduce_vault

/-- Both implementations satisfy the pre-existing public deposit specification. -/
theorem deposit_existing_spec (impl : Implementation) (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : safeAdd (s.readMap 2 s.sender) amount = some (s.readMap 2 s.sender + amount))
    (ha : safeAdd (s.readSlot 0) amount = some (s.readSlot 0 + amount))
    (ht : safeAdd (s.readSlot 1) amount = some (s.readSlot 1 + amount)) :
    Spec.deposit_spec amount s ((impl.deposit amount).run s).snd := by
  have h := deposit_meets_spec impl s amount h0 hs ha ht
  rw [Spec.deposit_execution] at h
  rw [h]
  simp +contextual [Spec.deposit_spec, Spec.accountingState, Spec.sameStorageExceptAssetSlots,
    Spec.storageUnchangedExceptAssetSlots, Specs.sameStorageAddr, Specs.sameContext,
    Specs.storageMapUnchangedExceptKeyAtSlot, Specs.storageMapUnchangedExceptKey,
    Specs.storageMapUnchangedExceptSlot, ContractResult.snd, ContractState.readSlot,
    ContractState.readMap, ContractState.writeSlot, ContractState.writeMap,
    ContractState.storage, ContractState.storageMap, ContractState.storageAddr,
    Verity.EVM.Uint256.add]
  repeat' constructor
  all_goals exact Verity.Core.Uint256.add_comm _ _

/-- Both implementations satisfy the pre-existing public withdrawal specification. -/
theorem withdraw_existing_spec (impl : Implementation) (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : amount.val ≤ (s.readMap 2 s.sender).val)
    (ha : amount.val ≤ (s.readSlot 0).val)
    (ht : amount.val ≤ (s.readSlot 1).val) :
    Spec.withdraw_spec amount s ((impl.withdraw amount).run s).snd := by
  have h := withdraw_meets_spec impl s amount h0 hs ha ht
  rw [Spec.withdraw_execution] at h
  rw [h]
  simp +contextual [Spec.withdraw_spec, Spec.accountingState, Spec.sameStorageExceptAssetSlots,
    Spec.storageUnchangedExceptAssetSlots, Specs.sameStorageAddr, Specs.sameContext,
    Specs.storageMapUnchangedExceptKeyAtSlot, Specs.storageMapUnchangedExceptKey,
    Specs.storageMapUnchangedExceptSlot, ContractResult.snd, ContractState.readSlot,
    ContractState.readMap, ContractState.writeSlot, ContractState.writeMap,
    ContractState.storage, ContractState.storageMap, ContractState.storageAddr,
    Verity.EVM.Uint256.sub]
  repeat' constructor

end Contracts.Vault.Execution
