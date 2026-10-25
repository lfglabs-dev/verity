/-
  ERC-4626 1:1 Share/Asset Conservation and Roundtrip Proofs for Vault.

  Proves non-vacuous share/asset conservation laws, spec compliance,
  deposit-withdraw roundtrip restoration, invariant preservation, and
  revert completeness on `Vault.deposit` and `Vault.withdraw`.
-/

import Contracts.Vault.Proofs.Correctness
import Contracts.Vault.Invariants
import Verity.Proofs.Stdlib.Math
import Verity.Proofs.Stdlib.Automation

namespace Contracts.Vault.Proofs

open Verity
open Contracts.Vault
open Contracts.Vault.Spec
open Contracts.Vault.Invariants
open Verity.Stdlib.Math (MAX_UINT256 safeAdd requireSomeUint)
open Verity.Proofs.Stdlib.Automation (safeAdd_some_val uint256_ge_val_le lt_modulus_of_le_max_uint256)

/-! ## Arithmetic Cancellation Helpers -/

/-- Adding `delta` and subtracting the base `x` in `Uint256` recovers `delta` exactly. -/
private theorem add_sub_self_left (x delta : Uint256) :
    EVM.Uint256.add x delta - x = delta := by
  change (x + delta) - x = delta
  rw [Verity.Core.Uint256.add_comm]
  exact Verity.Core.Uint256.sub_add_cancel delta x

/-- Subtracting `x - delta` from `x` when `x ≥ delta` recovers `delta` in `Uint256`. -/
private theorem sub_sub_self_of_ge {x delta : Uint256} (h : x ≥ delta) :
    x - EVM.Uint256.sub x delta = delta := by
  have h_le : delta.val ≤ x.val := uint256_ge_val_le h
  have h_sub_val : (EVM.Uint256.sub x delta).val = x.val - delta.val :=
    Verity.Core.Uint256.subNoWrap h_le
  have h_sub_le : (EVM.Uint256.sub x delta).val ≤ x.val := by
    rw [h_sub_val]
    omega
  apply Verity.Core.Uint256.ext
  change (EVM.Uint256.sub x (EVM.Uint256.sub x delta)).val = delta.val
  rw [Verity.Core.Uint256.subNoWrap h_sub_le, h_sub_val]
  omega

/-! ## Deposit Unfold and Spec Compliance -/

/-- Unfold `Vault.deposit` when share balance, totalAssets, and totalSupply additions do not overflow. -/
private theorem deposit_unfold (s : ContractState) (assets : Uint256)
    (h_no_share_overflow : (s.storageMap shareBalancesSlot.slot s.sender : Nat) + (assets : Nat) ≤ MAX_UINT256)
    (h_no_asset_overflow : (s.storage totalAssetsSlot.slot : Nat) + (assets : Nat) ≤ MAX_UINT256)
    (h_no_supply_overflow : (s.storage totalSupplySlot.slot : Nat) + (assets : Nat) ≤ MAX_UINT256) :
    (deposit assets).run s = ContractResult.success ()
      { ((s.writeMap 2 s.sender (EVM.Uint256.add (s.storageMap 2 s.sender) assets)).writeSlot
          0 (EVM.Uint256.add (s.storage 0) assets)).writeSlot
          1 (EVM.Uint256.add (s.storage 1) assets) with
        knownAddresses := fun slotIdx =>
          if slotIdx == 2 then (s.knownAddresses slotIdx).insert s.sender
          else s.knownAddresses slotIdx } := by
  have h_safe_shares : safeAdd (s.storageMap 2 s.sender) assets =
      some (s.storageMap 2 s.sender + assets) :=
    safeAdd_some_val (s.storageMap 2 s.sender) assets h_no_share_overflow
  have h_safe_assets : safeAdd (s.storage 0) assets =
      some (s.storage 0 + assets) :=
    safeAdd_some_val (s.storage 0) assets h_no_asset_overflow
  have h_safe_supply : safeAdd (s.storage 1) assets =
      some (s.storage 1 + assets) :=
    safeAdd_some_val (s.storage 1) assets h_no_supply_overflow
  verity_unfold deposit
  simp only [shareBalancesSlot, totalAssetsSlot, totalSupplySlot]
  unfold requireSomeUint
  rw [h_safe_shares]
  simp only [Verity.pure, Pure.pure, Bind.bind]
  rw [h_safe_assets]
  simp only [Verity.pure]
  rw [h_safe_supply]
  simp only [Verity.pure, HAdd.hAdd]
  rfl

/-- `Vault.deposit` meets its formal specification `deposit_spec` when no overflow occurs. -/
theorem deposit_meets_spec (s : ContractState) (assets : Uint256)
    (h_no_share_overflow : (s.storageMap shareBalancesSlot.slot s.sender : Nat) + (assets : Nat) ≤ MAX_UINT256)
    (h_no_asset_overflow : (s.storage totalAssetsSlot.slot : Nat) + (assets : Nat) ≤ MAX_UINT256)
    (h_no_supply_overflow : (s.storage totalSupplySlot.slot : Nat) + (assets : Nat) ≤ MAX_UINT256) :
    let s' := ((deposit assets).run s).snd
    deposit_spec assets s s' := by
  rw [deposit_unfold s assets h_no_share_overflow h_no_asset_overflow h_no_supply_overflow]
  unfold deposit_spec sameStorageExceptAssetSlots storageUnchangedExceptAssetSlots
    Specs.storageMapUnchangedExceptKeyAtSlot Specs.storageMapUnchangedExceptKey
    Specs.storageMapUnchangedExceptSlot
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, ContractState.storageMap]
  · simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, ContractState.storage]
  · simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, ContractState.storage]
  · intro addr h_ne
    simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, h_ne, ContractState.storageMap]
  · intro slotIdx h_ne addr
    simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, h_ne, ContractState.storageMap]
  · intro slotIdx h0 h1
    simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, h0, h1, ContractState.storage]
  · simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap,
      Specs.sameStorageAddr, ContractState.storageAddr_unfold]
  · simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, Specs.sameContext]

/-! ## Withdraw Unfold, Spec Compliance, and Revert Completeness -/

/-- Unfold `Vault.withdraw` when shares, totalAssets, and totalSupply are at least `shares`. -/
private theorem withdraw_unfold (s : ContractState) (shares : Uint256)
    (h_shares : s.storageMap shareBalancesSlot.slot s.sender ≥ shares)
    (h_assets : s.storage totalAssetsSlot.slot ≥ shares)
    (h_supply : s.storage totalSupplySlot.slot ≥ shares) :
    (withdraw shares).run s = ContractResult.success ()
      { ((s.writeMap 2 s.sender (EVM.Uint256.sub (s.storageMap 2 s.sender) shares)).writeSlot
          0 (EVM.Uint256.sub (s.storage 0) shares)).writeSlot
          1 (EVM.Uint256.sub (s.storage 1) shares) with
        knownAddresses := fun slotIdx =>
          if slotIdx == 2 then (s.knownAddresses slotIdx).insert s.sender
          else s.knownAddresses slotIdx } := by
  have h_shares' : s.storageMap 2 s.sender ≥ shares := h_shares
  have h_assets' : s.storage 0 ≥ shares := h_assets
  have h_supply' : s.storage 1 ≥ shares := h_supply
  verity_unfold withdraw
  simp [shareBalancesSlot, totalAssetsSlot, totalSupplySlot, h_shares', h_assets', h_supply']

/-- `Vault.withdraw` meets its formal specification `withdraw_spec` when guards succeed. -/
theorem withdraw_meets_spec (s : ContractState) (shares : Uint256)
    (h_shares : s.storageMap shareBalancesSlot.slot s.sender ≥ shares)
    (h_assets : s.storage totalAssetsSlot.slot ≥ shares)
    (h_supply : s.storage totalSupplySlot.slot ≥ shares) :
    let s' := ((withdraw shares).run s).snd
    withdraw_spec shares s s' := by
  rw [withdraw_unfold s shares h_shares h_assets h_supply]
  unfold withdraw_spec sameStorageExceptAssetSlots storageUnchangedExceptAssetSlots
    Specs.storageMapUnchangedExceptKeyAtSlot Specs.storageMapUnchangedExceptKey
    Specs.storageMapUnchangedExceptSlot
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, ContractState.storageMap]
  · simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, ContractState.storage]
  · simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, ContractState.storage]
  · intro addr h_ne
    simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, h_ne, ContractState.storageMap]
  · intro slotIdx h_ne addr
    simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, h_ne, ContractState.storageMap]
  · intro slotIdx h0 h1
    simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, h0, h1, ContractState.storage]
  · simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap,
      Specs.sameStorageAddr, ContractState.storageAddr_unfold]
  · simp [ContractResult.snd, ContractState.writeSlot, ContractState.writeMap, Specs.sameContext]

/-- Exact revert completeness for `Vault.withdraw`: when `shares > userShares`,
    `withdraw` reverts with `"Insufficient shares"` and leaves state `s` unchanged. -/
theorem withdraw_reverts_when_insufficient_shares (s : ContractState) (shares : Uint256)
    (h_insufficient : shares > s.storageMap shareBalancesSlot.slot s.sender) :
    (withdraw shares).run s = ContractResult.revert "Insufficient shares" s := by
  have h_lt : (s.storageMap 2 s.sender).val < shares.val := h_insufficient
  have h_ge_false : (s.storageMap 2 s.sender >= shares) = false := by
    simp [ge_iff_le, Verity.Core.Uint256.le_def]
    omega
  simp [withdraw, msgSender, getMapping, shareBalancesSlot, ContractState.readMap,
    Verity.require, Verity.bind, Bind.bind, Contract.run, h_ge_false]

/-! ## ERC-4626 1:1 Share/Asset Conservation Theorems -/

/-- ERC-4626 1:1 deposit conservation: after a successful `Vault.deposit assets`,
    the increase in `totalAssets` equals the increase in `totalSupply`, and the
    sender's share balance increases by exactly `assets` (both in `Uint256` and `Nat`). -/
theorem deposit_share_asset_conservation (s : ContractState) (assets : Uint256)
    (h_no_share_overflow : (s.storageMap shareBalancesSlot.slot s.sender : Nat) + (assets : Nat) ≤ MAX_UINT256)
    (h_no_asset_overflow : (s.storage totalAssetsSlot.slot : Nat) + (assets : Nat) ≤ MAX_UINT256)
    (h_no_supply_overflow : (s.storage totalSupplySlot.slot : Nat) + (assets : Nat) ≤ MAX_UINT256) :
    let s' := ((deposit assets).run s).snd
    s'.storage totalAssetsSlot.slot - s.storage totalAssetsSlot.slot =
      s'.storage totalSupplySlot.slot - s.storage totalSupplySlot.slot ∧
    s'.storageMap shareBalancesSlot.slot s.sender -
      s.storageMap shareBalancesSlot.slot s.sender = assets ∧
    (s'.storage totalAssetsSlot.slot).val - (s.storage totalAssetsSlot.slot).val =
      (s'.storage totalSupplySlot.slot).val - (s.storage totalSupplySlot.slot).val ∧
    (s'.storageMap shareBalancesSlot.slot s.sender).val -
      (s.storageMap shareBalancesSlot.slot s.sender).val = assets.val := by
  have h_spec := deposit_meets_spec s assets h_no_share_overflow h_no_asset_overflow h_no_supply_overflow
  dsimp only at h_spec
  rcases h_spec with ⟨h_shares_eq, h_assets_eq, h_supply_eq, _⟩
  let s' := ((deposit assets).run s).snd
  have h_shares_diff :
      s'.storageMap shareBalancesSlot.slot s.sender - s.storageMap shareBalancesSlot.slot s.sender = assets := by
    change s'.storageMap 2 s.sender - s.storageMap 2 s.sender = assets
    rw [h_shares_eq]
    exact add_sub_self_left (s.storageMap 2 s.sender) assets
  have h_assets_diff :
      s'.storage totalAssetsSlot.slot - s.storage totalAssetsSlot.slot = assets := by
    change s'.storage 0 - s.storage 0 = assets
    rw [h_assets_eq]
    exact add_sub_self_left (s.storage 0) assets
  have h_supply_diff :
      s'.storage totalSupplySlot.slot - s.storage totalSupplySlot.slot = assets := by
    change s'.storage 1 - s.storage 1 = assets
    rw [h_supply_eq]
    exact add_sub_self_left (s.storage 1) assets
  have h_shares_val :
      (s'.storageMap shareBalancesSlot.slot s.sender).val =
        (s.storageMap shareBalancesSlot.slot s.sender).val + assets.val := by
    change (s'.storageMap 2 s.sender).val = (s.storageMap 2 s.sender).val + assets.val
    rw [h_shares_eq]
    exact Verity.Core.Uint256.addNoWrap (lt_modulus_of_le_max_uint256 _ h_no_share_overflow)
  have h_assets_val :
      (s'.storage totalAssetsSlot.slot).val =
        (s.storage totalAssetsSlot.slot).val + assets.val := by
    change (s'.storage 0).val = (s.storage 0).val + assets.val
    rw [h_assets_eq]
    exact Verity.Core.Uint256.addNoWrap (lt_modulus_of_le_max_uint256 _ h_no_asset_overflow)
  have h_supply_val :
      (s'.storage totalSupplySlot.slot).val =
        (s.storage totalSupplySlot.slot).val + assets.val := by
    change (s'.storage 1).val = (s.storage 1).val + assets.val
    rw [h_supply_eq]
    exact Verity.Core.Uint256.addNoWrap (lt_modulus_of_le_max_uint256 _ h_no_supply_overflow)
  refine ⟨?_, h_shares_diff, ?_, ?_⟩
  · rw [h_assets_diff, h_supply_diff]
  · change (s'.storage totalAssetsSlot.slot).val - (s.storage totalAssetsSlot.slot).val =
      (s'.storage totalSupplySlot.slot).val - (s.storage totalSupplySlot.slot).val
    rw [h_assets_val, h_supply_val]
    omega
  · change (s'.storageMap shareBalancesSlot.slot s.sender).val -
      (s.storageMap shareBalancesSlot.slot s.sender).val = assets.val
    rw [h_shares_val]
    omega

/-- ERC-4626 1:1 withdraw conservation: after a successful `Vault.withdraw shares`,
    the decrease in `totalAssets` equals the decrease in `totalSupply`, and the
    sender's share balance decreases by `shares` (both in `Uint256` and `Nat`). -/
theorem withdraw_share_asset_conservation (s : ContractState) (shares : Uint256)
    (h_shares : s.storageMap shareBalancesSlot.slot s.sender ≥ shares)
    (h_assets : s.storage totalAssetsSlot.slot ≥ shares)
    (h_supply : s.storage totalSupplySlot.slot ≥ shares) :
    let s' := ((withdraw shares).run s).snd
    s.storage totalAssetsSlot.slot - s'.storage totalAssetsSlot.slot =
      s.storage totalSupplySlot.slot - s'.storage totalSupplySlot.slot ∧
    s.storageMap shareBalancesSlot.slot s.sender -
      s'.storageMap shareBalancesSlot.slot s.sender = shares ∧
    (s.storage totalAssetsSlot.slot).val - (s'.storage totalAssetsSlot.slot).val =
      (s.storage totalSupplySlot.slot).val - (s'.storage totalSupplySlot.slot).val ∧
    (s.storageMap shareBalancesSlot.slot s.sender).val -
      (s'.storageMap shareBalancesSlot.slot s.sender).val = shares.val := by
  have h_spec := withdraw_meets_spec s shares h_shares h_assets h_supply
  dsimp only at h_spec
  rcases h_spec with ⟨h_shares_eq, h_assets_eq, h_supply_eq, _⟩
  let s' := ((withdraw shares).run s).snd
  have h_shares_diff :
      s.storageMap shareBalancesSlot.slot s.sender - s'.storageMap shareBalancesSlot.slot s.sender = shares := by
    change s.storageMap 2 s.sender - s'.storageMap 2 s.sender = shares
    rw [h_shares_eq]
    exact sub_sub_self_of_ge h_shares
  have h_assets_diff :
      s.storage totalAssetsSlot.slot - s'.storage totalAssetsSlot.slot = shares := by
    change s.storage 0 - s'.storage 0 = shares
    rw [h_assets_eq]
    exact sub_sub_self_of_ge h_assets
  have h_supply_diff :
      s.storage totalSupplySlot.slot - s'.storage totalSupplySlot.slot = shares := by
    change s.storage 1 - s'.storage 1 = shares
    rw [h_supply_eq]
    exact sub_sub_self_of_ge h_supply
  have h_shares_le : shares.val ≤ (s.storageMap shareBalancesSlot.slot s.sender).val :=
    uint256_ge_val_le h_shares
  have h_assets_le : shares.val ≤ (s.storage totalAssetsSlot.slot).val :=
    uint256_ge_val_le h_assets
  have h_supply_le : shares.val ≤ (s.storage totalSupplySlot.slot).val :=
    uint256_ge_val_le h_supply
  have h_shares_val :
      (s'.storageMap shareBalancesSlot.slot s.sender).val =
        (s.storageMap shareBalancesSlot.slot s.sender).val - shares.val := by
    change (s'.storageMap 2 s.sender).val = (s.storageMap 2 s.sender).val - shares.val
    rw [h_shares_eq]
    exact Verity.Core.Uint256.subNoWrap h_shares_le
  have h_assets_val :
      (s'.storage totalAssetsSlot.slot).val =
        (s.storage totalAssetsSlot.slot).val - shares.val := by
    change (s'.storage 0).val = (s.storage 0).val - shares.val
    rw [h_assets_eq]
    exact Verity.Core.Uint256.subNoWrap h_assets_le
  have h_supply_val :
      (s'.storage totalSupplySlot.slot).val =
        (s.storage totalSupplySlot.slot).val - shares.val := by
    change (s'.storage 1).val = (s.storage 1).val - shares.val
    rw [h_supply_eq]
    exact Verity.Core.Uint256.subNoWrap h_supply_le
  refine ⟨?_, h_shares_diff, ?_, ?_⟩
  · rw [h_assets_diff, h_supply_diff]
  · change (s.storage totalAssetsSlot.slot).val - (s'.storage totalAssetsSlot.slot).val =
      (s.storage totalSupplySlot.slot).val - (s'.storage totalSupplySlot.slot).val
    rw [h_assets_val, h_supply_val]
    omega
  · change (s.storageMap shareBalancesSlot.slot s.sender).val -
      (s'.storageMap shareBalancesSlot.slot s.sender).val = shares.val
    rw [h_shares_val]
    omega

/-! ## Deposit-Withdraw Roundtrip -/

/-- `Vault.deposit assets` followed by `Vault.withdraw assets` restores the user's
    exact share balance, `totalAssets`, and `totalSupply`. -/
theorem deposit_withdraw_roundtrip (s : ContractState) (assets : Uint256)
    (h_no_share_overflow : (s.storageMap shareBalancesSlot.slot s.sender : Nat) + (assets : Nat) ≤ MAX_UINT256)
    (h_no_asset_overflow : (s.storage totalAssetsSlot.slot : Nat) + (assets : Nat) ≤ MAX_UINT256)
    (h_no_supply_overflow : (s.storage totalSupplySlot.slot : Nat) + (assets : Nat) ≤ MAX_UINT256) :
    let s1 := ((deposit assets).run s).snd
    let s2 := ((withdraw assets).run s1).snd
    s2.storageMap shareBalancesSlot.slot s.sender = s.storageMap shareBalancesSlot.slot s.sender ∧
    s2.storage totalAssetsSlot.slot = s.storage totalAssetsSlot.slot ∧
    s2.storage totalSupplySlot.slot = s.storage totalSupplySlot.slot := by
  let s1 := ((deposit assets).run s).snd
  have h_dep := deposit_meets_spec s assets h_no_share_overflow h_no_asset_overflow h_no_supply_overflow
  dsimp only at h_dep
  rcases h_dep with ⟨h_s1_shares, h_s1_assets, h_s1_supply, _, _, _, h_s1_ctx⟩
  have h_sender : s1.sender = s.sender := h_s1_ctx.1
  have h_s1_shares_val : (s1.storageMap 2 s1.sender).val =
      (s.storageMap 2 s.sender).val + assets.val := by
    rw [h_sender, h_s1_shares]
    exact Verity.Core.Uint256.addNoWrap (lt_modulus_of_le_max_uint256 _ h_no_share_overflow)
  have h_s1_assets_val : (s1.storage 0).val = (s.storage 0).val + assets.val := by
    rw [h_s1_assets]
    exact Verity.Core.Uint256.addNoWrap (lt_modulus_of_le_max_uint256 _ h_no_asset_overflow)
  have h_s1_supply_val : (s1.storage 1).val = (s.storage 1).val + assets.val := by
    rw [h_s1_supply]
    exact Verity.Core.Uint256.addNoWrap (lt_modulus_of_le_max_uint256 _ h_no_supply_overflow)
  have h_shares_ge : s1.storageMap shareBalancesSlot.slot s1.sender ≥ assets := by
    change assets.val ≤ (s1.storageMap 2 s1.sender).val
    rw [h_s1_shares_val]
    omega
  have h_assets_ge : s1.storage totalAssetsSlot.slot ≥ assets := by
    change assets.val ≤ (s1.storage 0).val
    rw [h_s1_assets_val]
    omega
  have h_supply_ge : s1.storage totalSupplySlot.slot ≥ assets := by
    change assets.val ≤ (s1.storage 1).val
    rw [h_s1_supply_val]
    omega
  have h_wd := withdraw_meets_spec s1 assets h_shares_ge h_assets_ge h_supply_ge
  dsimp only at h_wd
  rcases h_wd with ⟨h_s2_shares, h_s2_assets, h_s2_supply, _⟩
  refine ⟨?_, ?_, ?_⟩
  · change ((withdraw assets).run s1).snd.storageMap 2 s.sender = s.storageMap 2 s.sender
    rw [← h_sender, h_s2_shares, h_sender, h_s1_shares,
      EVM.Uint256.sub_add_cancel (s.storageMap 2 s.sender) assets]
  · change ((withdraw assets).run s1).snd.storage 0 = s.storage 0
    rw [h_s2_assets, h_s1_assets, EVM.Uint256.sub_add_cancel (s.storage 0) assets]
  · change ((withdraw assets).run s1).snd.storage 1 = s.storage 1
    rw [h_s2_supply, h_s1_supply, EVM.Uint256.sub_add_cancel (s.storage 1) assets]

/-! ## Invariant Preservation (`assets_supply_synced` and `WellFormedState`) -/

/-- `Vault.deposit` preserves the 1:1 `assets_supply_synced` invariant (`totalAssets = totalSupply`). -/
theorem deposit_preserves_assets_supply_synced (s : ContractState) (assets : Uint256)
    (h_sync : assets_supply_synced s)
    (h_no_share_overflow : (s.storageMap shareBalancesSlot.slot s.sender : Nat) + (assets : Nat) ≤ MAX_UINT256)
    (h_no_asset_overflow : (s.storage totalAssetsSlot.slot : Nat) + (assets : Nat) ≤ MAX_UINT256) :
    let s' := ((deposit assets).run s).snd
    assets_supply_synced s' := by
  have h_sync_eq : s.storage 0 = s.storage 1 := h_sync
  have h_no_supply_overflow : (s.storage totalSupplySlot.slot : Nat) + (assets : Nat) ≤ MAX_UINT256 := by
    change (s.storage 1 : Nat) + (assets : Nat) ≤ MAX_UINT256
    rw [← h_sync_eq]
    exact h_no_asset_overflow
  have h_spec := deposit_meets_spec s assets h_no_share_overflow h_no_asset_overflow h_no_supply_overflow
  dsimp only at h_spec ⊢
  rcases h_spec with ⟨_, h_assets_eq, h_supply_eq, _⟩
  unfold assets_supply_synced
  rw [h_assets_eq, h_supply_eq, h_sync_eq]

/-- `Vault.withdraw` preserves the 1:1 `assets_supply_synced` invariant (`totalAssets = totalSupply`). -/
theorem withdraw_preserves_assets_supply_synced (s : ContractState) (shares : Uint256)
    (h_sync : assets_supply_synced s)
    (h_shares : s.storageMap shareBalancesSlot.slot s.sender ≥ shares)
    (h_assets : s.storage totalAssetsSlot.slot ≥ shares) :
    let s' := ((withdraw shares).run s).snd
    assets_supply_synced s' := by
  have h_sync_eq : s.storage 0 = s.storage 1 := h_sync
  have h_supply : s.storage totalSupplySlot.slot ≥ shares := by
    change s.storage 1 ≥ shares
    rw [← h_sync_eq]
    exact h_assets
  have h_spec := withdraw_meets_spec s shares h_shares h_assets h_supply
  dsimp only at h_spec ⊢
  rcases h_spec with ⟨_, h_assets_eq, h_supply_eq, _⟩
  unfold assets_supply_synced
  rw [h_assets_eq, h_supply_eq, h_sync_eq]

end Contracts.Vault.Proofs
