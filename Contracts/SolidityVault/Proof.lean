import Contracts.SolidityVault.Spec

namespace Contracts.SolidityVault
open Verity
open Verity.Stdlib.Math

macro "reduce_import" : tactic => `(tactic|
  simp_all [Spec.deposit, Spec.withdraw, Spec.balance, Spec.accountingState,
    Imported.deposit, Imported.withdraw, Imported.balanceOf,
    Imported.totalAssetsSlot, Imported.totalSupplySlot, Imported.shareBalancesSlot,
    Contract.run, Bind.bind, Pure.pure, Verity.instMonadContract, Verity.bind, Verity.pure, msgValue, msgSender, Verity.require,
    getStorage, setStorage, getMapping, setMapping, requireSomeUint, safeSub,
    Nat.not_le_of_lt, Nat.not_lt_of_ge,
    ContractState.readSlot, ContractState.writeSlot, ContractState.readMap,
    ContractState.writeMap, ContractState.storage, ContractState.storageMap])

theorem balance_meets_spec (s : ContractState) (account : Address)
    (h0 : s.msgValue = 0) : Spec.balance s account := by
  reduce_import

theorem deposit_meets_spec (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : safeAdd (s.readMap 2 s.sender) amount = some (s.readMap 2 s.sender + amount))
    (ha : safeAdd (s.readSlot 0) amount = some (s.readSlot 0 + amount))
    (ht : safeAdd (s.readSlot 1) amount = some (s.readSlot 1 + amount)) :
    Spec.deposit s amount := by
  reduce_import

theorem withdraw_meets_spec (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : amount.val ≤ (s.readMap 2 s.sender).val)
    (ha : amount.val ≤ (s.readSlot 0).val)
    (ht : amount.val ≤ (s.readSlot 1).val) : Spec.withdraw s amount := by
  reduce_import

theorem deposit_nonpayable (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue.val ≠ 0) :
    (Imported.deposit amount).run s = ContractResult.revert "Nonpayable" s := by
  reduce_import

/-- A late failing addition rolls back the earlier mapping and asset writes. -/
theorem deposit_late_overflow_rollback (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : safeAdd (s.readMap 2 s.sender) amount = some (s.readMap 2 s.sender + amount))
    (ha : safeAdd (s.readSlot 0) amount = some (s.readSlot 0 + amount))
    (ht : safeAdd (s.readSlot 1) amount = none) :
    (Imported.deposit amount).run s = ContractResult.revert "Panic(0x11)" s := by
  reduce_import

theorem withdraw_insufficient_shares (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hs : (s.readMap 2 s.sender).val < amount.val) :
    (Imported.withdraw amount).run s = ContractResult.revert "InsufficientShares" s := by
  reduce_import

/-- Successful deposit changes no unrelated logical storage key. -/
theorem deposit_frame (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : safeAdd (s.readMap 2 s.sender) amount = some (s.readMap 2 s.sender + amount))
    (ha : safeAdd (s.readSlot 0) amount = some (s.readSlot 0 + amount))
    (ht : safeAdd (s.readSlot 1) amount = some (s.readSlot 1 + amount))
    (key : StorageKey) (hk0 : key ≠ .slot 0) (hk1 : key ≠ .slot 1)
    (hkm : key ≠ .map 2 s.sender) :
    ((Imported.deposit amount).run s).snd.storageWords key = s.storageWords key := by
  have h := deposit_meets_spec s amount h0 hs ha ht
  rw [Spec.deposit] at h
  rw [h]
  simp [Spec.accountingState, Imported.totalAssetsSlot, Imported.totalSupplySlot,
    Imported.shareBalancesSlot, ContractState.writeSlot, ContractState.writeMap, hk0, hk1, hkm]

theorem totalAssets_getter (s : ContractState) (h0 : s.msgValue = 0) :
    Imported.totalAssets.run s = ContractResult.success (s.readSlot 0) s := by
  simp [Imported.totalAssets, Imported.totalAssetsSlot, Contract.run, Verity.bind,
    msgValue, Verity.require, getStorage, h0]

theorem totalSupply_getter (s : ContractState) (h0 : s.msgValue = 0) :
    Imported.totalSupply.run s = ContractResult.success (s.readSlot 1) s := by
  simp [Imported.totalSupply, Imported.totalSupplySlot, Contract.run, Verity.bind,
    msgValue, Verity.require, getStorage, h0]

theorem shareBalances_getter (s : ContractState) (account : Address) (h0 : s.msgValue = 0) :
    (Imported.shareBalances account).run s = ContractResult.success (s.readMap 2 account) s := by
  simp [Imported.shareBalances, Imported.shareBalancesSlot, Contract.run, Verity.bind,
    msgValue, Verity.require, getMapping, h0]

theorem withdraw_nonpayable (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue.val ≠ 0) :
    (Imported.withdraw amount).run s = ContractResult.revert "Nonpayable" s := by
  reduce_import

theorem withdraw_insufficient_assets (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hs : amount.val ≤ (s.readMap 2 s.sender).val)
    (ha : (s.readSlot 0).val < amount.val) :
    (Imported.withdraw amount).run s = ContractResult.revert "InsufficientAssets" s := by
  reduce_import

theorem withdraw_insufficient_supply (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hs : amount.val ≤ (s.readMap 2 s.sender).val)
    (ha : amount.val ≤ (s.readSlot 0).val) (ht : (s.readSlot 1).val < amount.val) :
    (Imported.withdraw amount).run s = ContractResult.revert "InsufficientSupply" s := by
  reduce_import

#print axioms deposit_frame
#print axioms totalAssets_getter
#print axioms totalSupply_getter
#print axioms shareBalances_getter
#print axioms withdraw_nonpayable
#print axioms withdraw_insufficient_assets
#print axioms withdraw_insufficient_supply
#print axioms balance_meets_spec
#print axioms deposit_meets_spec
#print axioms withdraw_meets_spec
#print axioms deposit_nonpayable
#print axioms deposit_late_overflow_rollback
#print axioms withdraw_insufficient_shares

end Contracts.SolidityVault
