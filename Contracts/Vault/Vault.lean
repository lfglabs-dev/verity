import Contracts.Common

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-!
A minimal ERC4626-style vault example with 1:1 asset/share accounting.

This is intentionally conservative: deposits mint shares equal to assets and
withdrawals burn shares 1:1. That keeps the example mechanically tractable
while still exercising the canonical vault surface and share-accounting proofs.
-/
verity_contract Vault where
  storage
    totalAssetsSlot : Uint256 := slot 0
    totalSupplySlot : Uint256 := slot 1
    shareBalancesSlot : Address → Uint256 := slot 2

  errors
    error InsufficientShares()
    error InsufficientAssets()
    error InsufficientSupply()

  constructor () := do
    setStorage totalAssetsSlot 0
    setStorage totalSupplySlot 0

  function deposit (assets : Uint256) : Unit := do
    let sender ← msgSender
    let currentShares ← getMapping shareBalancesSlot sender
    let newShares ← requireSomeUint (safeAdd currentShares assets) "Panic(0x11)"
    setMapping shareBalancesSlot sender newShares
    let currentAssets ← getStorage totalAssetsSlot
    let newAssets ← requireSomeUint (safeAdd currentAssets assets) "Panic(0x11)"
    setStorage totalAssetsSlot newAssets
    let currentSupply ← getStorage totalSupplySlot
    let newSupply ← requireSomeUint (safeAdd currentSupply assets) "Panic(0x11)"
    setStorage totalSupplySlot newSupply

  function withdraw (shares : Uint256) : Unit := do
    let sender ← msgSender
    let currentShares ← getMapping shareBalancesSlot sender
    requireError (currentShares >= shares) InsufficientShares()
    let currentAssets ← getStorage totalAssetsSlot
    requireError (currentAssets >= shares) InsufficientAssets()
    let currentSupply ← getStorage totalSupplySlot
    requireError (currentSupply >= shares) InsufficientSupply()
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

namespace Vault

abbrev getTotalAssets : Contract Uint256 := totalAssets
abbrev getTotalSupply : Contract Uint256 := totalSupply

end Vault

end Contracts
