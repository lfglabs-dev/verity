import Contracts.Common

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-!
A deliberately small xStocks integration accounting vault.

The contract models the accounting side of a builder-owned vault that mints
shares 1:1 for a settled adjusted xStock amount. Token custody and transfer
success remain abstract: the reusable proof kit specifies the assumptions an
Ink/EVM integrator needs around `balanceOf`, multipliers, and epochs.
-/
verity_contract XStockVault where
  storage
    xStockTokenSlot : Address := slot 0
    totalAssetsSlot : Uint256 := slot 1
    totalSupplySlot : Uint256 := slot 2
    shareBalancesSlot : Address → Uint256 := slot 3
    multiplierEpochSlot : Uint256 := slot 4
    corporateActionPausedSlot : Uint256 := slot 5

  constructor (xStockToken : Address) := do
    setStorageAddr xStockTokenSlot xStockToken
    setStorage totalAssetsSlot 0
    setStorage totalSupplySlot 0
    setStorage multiplierEpochSlot 0
    setStorage corporateActionPausedSlot 0

  function setCorporateActionPaused (paused : Uint256) : Unit := do
    require (paused == 0 || paused == 1) "Pause flag must be 0 or 1"
    setStorage corporateActionPausedSlot paused

  function updateMultiplierEpoch (newEpoch : Uint256) : Unit := do
    setStorage multiplierEpochSlot newEpoch

  function syncFromBalanceOf (adjustedBalanceOfVault : Uint256) : Unit := do
    setStorage totalAssetsSlot adjustedBalanceOfVault

  function deposit (assets : Uint256, quoteEpoch : Uint256) : Unit := do
    let paused ← getStorage corporateActionPausedSlot
    require (paused == 0) "Corporate action window"
    let currentEpoch ← getStorage multiplierEpochSlot
    require (quoteEpoch == currentEpoch) "Stale multiplier epoch"
    let sender ← msgSender
    let currentShares ← getMapping shareBalancesSlot sender
    let newShares ← requireSomeUint (safeAdd currentShares assets) "Share balance overflow"
    let currentAssets ← getStorage totalAssetsSlot
    let newAssets ← requireSomeUint (safeAdd currentAssets assets) "Total assets overflow"
    let currentSupply ← getStorage totalSupplySlot
    let newSupply ← requireSomeUint (safeAdd currentSupply assets) "Total supply overflow"
    setMapping shareBalancesSlot sender newShares
    setStorage totalAssetsSlot newAssets
    setStorage totalSupplySlot newSupply

  function withdraw (shares : Uint256, quoteEpoch : Uint256) : Unit := do
    let paused ← getStorage corporateActionPausedSlot
    require (paused == 0) "Corporate action window"
    let currentEpoch ← getStorage multiplierEpochSlot
    require (quoteEpoch == currentEpoch) "Stale multiplier epoch"
    let sender ← msgSender
    let currentShares ← getMapping shareBalancesSlot sender
    require (currentShares >= shares) "Insufficient shares"
    let currentAssets ← getStorage totalAssetsSlot
    require (currentAssets >= shares) "Insufficient assets"
    let currentSupply ← getStorage totalSupplySlot
    require (currentSupply >= shares) "Insufficient supply"
    setMapping shareBalancesSlot sender (sub currentShares shares)
    setStorage totalAssetsSlot (sub currentAssets shares)
    setStorage totalSupplySlot (sub currentSupply shares)

  function balanceOf (addr : Address) : Uint256 := do
    let currentShares ← getMapping shareBalancesSlot addr
    return currentShares

  function totalAssets () : Uint256 := do
    let currentAssets ← getStorage totalAssetsSlot
    return currentAssets

  function totalSupply () : Uint256 := do
    let currentSupply ← getStorage totalSupplySlot
    return currentSupply

  function multiplierEpoch () : Uint256 := do
    let currentEpoch ← getStorage multiplierEpochSlot
    return currentEpoch

namespace XStockVault

abbrev getTotalAssets : Contract Uint256 := totalAssets
abbrev getTotalSupply : Contract Uint256 := totalSupply

end XStockVault

end Contracts
