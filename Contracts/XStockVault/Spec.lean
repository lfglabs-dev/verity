import Verity.Specs.Common
import Verity.Specs.Common.Sum
import Verity.Specs.Ink.XStocks
import Verity.Macro
import Verity.EVM.Uint256
import Contracts.XStockVault.XStockVault

namespace Contracts.XStockVault.Spec

open Verity
open Verity.Specs
open Verity.EVM.Uint256
open Verity.Specs.Common (sumBalances balancesFinite)
open Verity.Specs.Ink.XStocks

def storageUnchangedExceptAssetSupplySlots (s s' : ContractState) : Prop :=
  ∀ slotIdx : Nat,
    slotIdx ≠ 1 → slotIdx ≠ 2 →
      s'.storage slotIdx = s.storage slotIdx

def sameStorageExceptAssetSupplySlots (s s' : ContractState) : Prop :=
  storageUnchangedExceptAssetSupplySlots s s' ∧
  Specs.sameStorageAddr s s' ∧
  Specs.sameContext s s'

def storageUnchangedExceptTotalAssetsSlot (s s' : ContractState) : Prop :=
  ∀ slotIdx : Nat,
    slotIdx ≠ 1 →
      s'.storage slotIdx = s.storage slotIdx

def deposit_spec (assets quoteEpoch : Uint256) (s s' : ContractState) : Prop :=
  s.storage 5 = 0 ∧
  quoteEpoch = s.storage 4 ∧
  s'.storageMap 3 s.sender = add (s.storageMap 3 s.sender) assets ∧
  s'.storage 1 = add (s.storage 1) assets ∧
  s'.storage 2 = add (s.storage 2) assets ∧
  Specs.storageMapUnchangedExceptKeyAtSlot 3 s.sender s s' ∧
  sameStorageExceptAssetSupplySlots s s'

def withdraw_spec (shares quoteEpoch : Uint256) (s s' : ContractState) : Prop :=
  s.storage 5 = 0 ∧
  quoteEpoch = s.storage 4 ∧
  s.storageMap 3 s.sender ≥ shares ∧
  s.storage 1 ≥ shares ∧
  s.storage 2 ≥ shares ∧
  s'.storageMap 3 s.sender = sub (s.storageMap 3 s.sender) shares ∧
  s'.storage 1 = sub (s.storage 1) shares ∧
  s'.storage 2 = sub (s.storage 2) shares ∧
  Specs.storageMapUnchangedExceptKeyAtSlot 3 s.sender s s' ∧
  sameStorageExceptAssetSupplySlots s s'

def syncFromBalanceOf_spec (adjustedBalanceOfVault : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 1 = adjustedBalanceOfVault ∧
  s'.storage 2 = s.storage 2 ∧
  s'.storage 4 = s.storage 4 ∧
  s'.storage 5 = s.storage 5 ∧
  storageUnchangedExceptTotalAssetsSlot s s' ∧
  Specs.sameStorageMap s s' ∧
  Specs.sameStorageAddr s s' ∧
  Specs.sameContext s s'

def balanceOf_spec (addr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 3 addr

def totalAssets_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 1

def totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 2

def multiplierEpoch_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 4

structure VaultState where
  totalAssets : Rat
  totalShares : Rat
  shareBalance : Address → Rat
  xstockMultiplierEpoch : MultiplierEpoch

def syncAssetsFromXStock (s : VaultState) (x : XStockSnapshot) : VaultState :=
  { s with totalAssets := x.evmBalanceOfVault }

def shareFraction (s : VaultState) (user : Address) : Rat :=
  if s.totalShares = 0 then 0 else s.shareBalance user / s.totalShares

def userClaim (s : VaultState) (user : Address) : Rat :=
  shareFraction s user * s.totalAssets

def applyMultiplierUpdate
    (s : VaultState)
    (oldMultiplier newMultiplier : Rat) : VaultState :=
  { s with totalAssets := s.totalAssets * (newMultiplier / oldMultiplier) }

structure DepositQuote where
  user : Address
  amount : Rat
  sharesOut : Rat
  multiplierEpoch : MultiplierEpoch

def mintSharesForSettledDeposit
    (s : VaultState)
    (user : Address)
    (amount sharesOut : Rat) : VaultState :=
  { s with
    totalAssets := s.totalAssets + amount,
    totalShares := s.totalShares + sharesOut,
    shareBalance := fun addr => if addr = user then s.shareBalance addr + sharesOut else s.shareBalance addr }

def settleDepositQuote (s : VaultState) (q : DepositQuote) : VaultState :=
  if q.multiplierEpoch = s.xstockMultiplierEpoch then
    mintSharesForSettledDeposit s q.user q.amount q.sharesOut
  else
    s

def totalShares (s : ContractState) : Uint256 :=
  sumBalances 3 (s.knownAddresses 3) s.storageMap

end Contracts.XStockVault.Spec
