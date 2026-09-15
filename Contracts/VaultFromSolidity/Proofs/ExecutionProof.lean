import Contracts.VaultFromSolidity.Spec

/-!
# Proofs about the Vault imported from Solidity

Three layers, deliberately kept small:

1. `*_exact_state` -- internal: each entry point produces exactly this raw
   `ContractState`, including Verity's ghost key-enumeration metadata. These
   unfold the definitions `Importer.lean` registered from `Vault.sol`, so they
   fail if the Solidity source changes behaviour.
2. `*_meets_spec` -- the named-storage promise from `Spec`. Each states that
   the call succeeds under its precondition and that the successful post-state
   (or, for `balanceOf`, the returned value) satisfies the spec. These are
   proved directly against the imported definitions, not derived from the
   exact-state lemmas, so a behaviour change in `Vault.sol` breaks them on
   their own.
3. `*_preserves_solvency` -- the contract-level result. Neither a deposit nor a
   withdrawal can break the one-for-one backing between assets and issued
   shares. A reverting call leaves the state untouched (`Contract.run` rolls
   back), so solvency can only ever be lost on a successful call, which is what
   these two theorems rule out.

Slots are only ever referenced through the imported `<var>Slot` handles, so the
proofs do not depend on the storage-layout order solc picks.
-/

namespace Contracts.VaultFromSolidity.Proofs.ExecutionProof
open Verity
open Verity.Stdlib.Math
open Spec

/-- Exact post-state of a successful `deposit`/`withdraw`: the caller's share
balance and both totals move together, including Verity's ghost
key-enumeration metadata. -/
def accountingState (s : ContractState) (shares assets supply : Uint256) : ContractState :=
  let mapped := { s.writeMap shareBalancesSlot.slot s.sender shares with
    knownAddresses := fun slotIdx => if slotIdx == shareBalancesSlot.slot then
      (s.knownAddresses slotIdx).insert s.sender else s.knownAddresses slotIdx }
  (mapped.writeSlot totalAssetsSlot.slot assets).writeSlot totalSupplySlot.slot supply

macro "reduce_vault" : tactic => `(tactic|
  simp_all [depositFits, withdrawCovered, accountingState, view,
    Storage.totalAssets, Storage.totalSupply, Storage.shareBalances,
    deposit, withdraw, balanceOf, totalAssets, totalSupply,
    shareBalances, totalAssetsSlot, totalSupplySlot, shareBalancesSlot,
    Contract.run, Bind.bind, Pure.pure, Verity.instMonadContract, Verity.bind, Verity.pure,
    msgValue, msgSender, Verity.require,
    getStorage, setStorage, getMapping, setMapping, requireSomeUint, safeAdd, safeSub,
    Verity.EVM.Uint256.sub, Nat.not_le_of_lt, Nat.not_lt_of_ge,
    ContractState.readSlot, ContractState.writeSlot, ContractState.readMap,
    ContractState.writeMap, ContractState.storage, ContractState.storageMap])

/-! ## Exact behaviour of each entry point -/

theorem balance_exact_state (s : ContractState) (account : Address)
    (h0 : s.msgValue = 0) :
    (balanceOf account).run s = ContractResult.success ((view s).shareBalances account) s := by
  reduce_vault

theorem deposit_exact_state (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hfits : depositFits amount s.sender (view s)) :
    (deposit amount).run s = ContractResult.success ()
      (accountingState s ((view s).shareBalances s.sender + amount)
        ((view s).totalAssets + amount) ((view s).totalSupply + amount)) := by
  reduce_vault

theorem withdraw_exact_state (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hcovered : withdrawCovered amount s.sender (view s)) :
    (withdraw amount).run s = ContractResult.success ()
      (accountingState s ((view s).shareBalances s.sender - amount)
        ((view s).totalAssets - amount) ((view s).totalSupply - amount)) := by
  reduce_vault

/-! ## Each entry point meets its named-storage spec -/

/-- `balanceOf` succeeds, leaves the state untouched, and returns the
account's shares as `balanceOf_spec` promises. -/
theorem balance_meets_spec (s : ContractState) (account : Address)
    (h0 : s.msgValue = 0) :
    ∃ result, (balanceOf account).run s = ContractResult.success result s ∧
      balanceOf_spec account result (view s) := by
  unfold balanceOf_spec
  reduce_vault

/-- Under `depositFits`, `deposit` succeeds and its post-state satisfies
`deposit_spec`. -/
theorem deposit_meets_spec (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hfits : depositFits amount s.sender (view s)) :
    ∃ post, (deposit amount).run s = ContractResult.success () post ∧
      deposit_spec amount s.sender (view s) (view post) := by
  unfold deposit_spec
  reduce_vault

/-- Under `withdrawCovered`, `withdraw` succeeds and its post-state satisfies
`withdraw_spec`. -/
theorem withdraw_meets_spec (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hcovered : withdrawCovered amount s.sender (view s)) :
    ∃ post, (withdraw amount).run s = ContractResult.success () post ∧
      withdraw_spec amount s.sender (view s) (view post) := by
  unfold withdraw_spec
  reduce_vault

/-! ## The vault stays solvent -/

/-- A successful deposit credits the caller's shares and both totals by the same
amount, so assets still exactly back the issued shares. -/
theorem deposit_preserves_solvency (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hfits : depositFits amount s.sender (view s))
    (hsolvent : solvent (view s)) :
    solvent (view ((deposit amount).run s).snd) := by
  obtain ⟨post, hrun, hassets, hsupply, _⟩ := deposit_meets_spec s amount h0 hfits
  unfold solvent at hsolvent ⊢
  rw [hrun, ContractResult.snd_success, hassets, hsupply, hsolvent]

/-- A successful withdrawal debits the caller's shares and both totals by the
same amount, so assets still exactly back the issued shares. -/
theorem withdraw_preserves_solvency (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hcovered : withdrawCovered amount s.sender (view s))
    (hsolvent : solvent (view s)) :
    solvent (view ((withdraw amount).run s).snd) := by
  obtain ⟨post, hrun, hassets, hsupply, _⟩ := withdraw_meets_spec s amount h0 hcovered
  unfold solvent at hsolvent ⊢
  rw [hrun, ContractResult.snd_success, hassets, hsupply, hsolvent]

end Contracts.VaultFromSolidity.Proofs.ExecutionProof
