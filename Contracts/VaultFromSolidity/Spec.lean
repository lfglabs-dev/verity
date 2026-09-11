import Verity.EVM.Uint256
import Contracts.VaultFromSolidity.VaultFromSolidity

/-!
# What the imported Vault is supposed to do

`Importer.lean` turns `Vault.sol` into ordinary Verity definitions: `deposit`,
`withdraw`, `balanceOf`, and one `StorageSlot` per state variable
(slot `0 = totalAssets`, slot `1 = totalSupply`, slot `2 = shareBalances`).

This file states two things about them:

* `solvent` -- the property that matters for the contract as a whole. Shares are
  issued one-for-one against assets, so every share outstanding must stay backed
  by an asset the vault accounts for.
* `deposit_execution` / `withdraw_execution` / `balance_execution` -- the exact
  state each entry point produces. These pin down behaviour precisely enough to
  derive `solvent`, and they are what a Solidity mutation has to break.
-/

namespace Contracts.VaultFromSolidity.Spec

open Verity
open Verity.EVM.Uint256

/-- The vault's main invariant: issued shares are exactly backed by assets
(`totalAssets = totalSupply`). If this ever breaks, shares stop being
redeemable one-for-one and the vault is insolvent. -/
def solvent (s : ContractState) : Prop :=
  s.readSlot 0 = s.readSlot 1

/-- Exact post-state of a successful `deposit`/`withdraw`: the caller's share
balance and both totals move together, including Verity's ghost
key-enumeration metadata. -/
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
