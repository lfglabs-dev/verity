import Contracts.VaultFromSolidity.Spec

/-!
# Proofs about the Vault imported from Solidity

Two layers, deliberately kept small:

1. `*_meets_spec` -- each entry point produces exactly the state
   `Spec` describes. These unfold the definitions `Importer.lean` registered
   from `Vault.sol`, so they fail if the Solidity source changes behaviour.
2. `*_preserves_solvency` -- the contract-level result. Neither a deposit nor a
   withdrawal can break the one-for-one backing between assets and issued
   shares. A reverting call leaves the state untouched (`Contract.run` rolls
   back), so solvency can only ever be lost on a successful call, which is what
   these two theorems rule out.
-/

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

/-! ## Exact behaviour of each entry point -/

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

/-! ## The vault stays solvent -/

/-- A successful deposit credits the caller's shares and both totals by the same
amount, so assets still exactly back the issued shares. -/
theorem deposit_preserves_solvency (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : safeAdd (s.readMap 2 s.sender) amount = some (s.readMap 2 s.sender + amount))
    (ha : safeAdd (s.readSlot 0) amount = some (s.readSlot 0 + amount))
    (ht : safeAdd (s.readSlot 1) amount = some (s.readSlot 1 + amount))
    (hsolvent : Spec.solvent s) :
    Spec.solvent ((deposit amount).run s).snd := by
  have h := deposit_meets_spec s amount h0 hs ha ht
  rw [Spec.deposit_execution] at h
  rw [h]
  simp only [Spec.solvent, Spec.accountingState, ContractResult.snd,
    ContractState.readSlot, ContractState.writeSlot, ContractState.writeMap,
    ContractState.storage] at hsolvent ⊢
  simp [hsolvent]

/-- A successful withdrawal debits the caller's shares and both totals by the
same amount, so assets still exactly back the issued shares. -/
theorem withdraw_preserves_solvency (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0)
    (hs : amount.val ≤ (s.readMap 2 s.sender).val)
    (ha : amount.val ≤ (s.readSlot 0).val)
    (ht : amount.val ≤ (s.readSlot 1).val)
    (hsolvent : Spec.solvent s) :
    Spec.solvent ((withdraw amount).run s).snd := by
  have h := withdraw_meets_spec s amount h0 hs ha ht
  rw [Spec.withdraw_execution] at h
  rw [h]
  simp only [Spec.solvent, Spec.accountingState, ContractResult.snd,
    ContractState.readSlot, ContractState.writeSlot, ContractState.writeMap,
    ContractState.storage] at hsolvent ⊢
  simp [hsolvent]

end Contracts.VaultFromSolidity.Proofs.Execution
