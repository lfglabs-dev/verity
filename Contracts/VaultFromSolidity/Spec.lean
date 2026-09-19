import Verity.EVM.Uint256
import Contracts.VaultFromSolidity.VaultFromSolidity

/-!
# What the imported Vault is supposed to do

`Importer.lean` turns `Vault.sol` into ordinary Verity definitions: `deposit`,
`withdraw`, `balanceOf`, and a read-only storage view named after the Solidity
state variables. For `v : Storage`, `v.totalAssets`, `v.totalSupply` and
`v.shareBalances` read those variables; `view s` is the view of a state `s`.
The storage-layout slot behind each name comes from solc, not from this file,
so reordering the Solidity declarations does not change anything here.

This file only states the promise:

* `solvent` -- the property that matters for the contract as a whole. Shares are
  issued one-for-one against assets, so every share outstanding must stay backed
  by an asset the vault accounts for.
* `deposit_spec` / `withdraw_spec` / `balanceOf_spec` -- what each entry point
  does to the named storage, under the preconditions `depositFits` /
  `withdrawCovered`.
-/

namespace Contracts.VaultFromSolidity.Spec

open Verity
open Verity.EVM.Uint256

/-- The vault's main invariant: issued shares are exactly backed by assets.
If this ever breaks, shares stop being redeemable one-for-one and the vault is
insolvent. -/
def solvent (v : Storage) : Prop :=
  v.totalAssets = v.totalSupply

/-- `deposit(amount)` credits the caller's shares and both totals by `amount`,
and leaves every other account's shares alone. -/
def deposit_spec (amount : Uint256) (caller : Address) (pre post : Storage) : Prop :=
  post.totalAssets = pre.totalAssets + amount ∧
  post.totalSupply = pre.totalSupply + amount ∧
  post.shareBalances caller = pre.shareBalances caller + amount ∧
  ∀ other, other ≠ caller → post.shareBalances other = pre.shareBalances other

/-- `withdraw(amount)` debits the caller's shares and both totals by `amount`,
and leaves every other account's shares alone. -/
def withdraw_spec (amount : Uint256) (caller : Address) (pre post : Storage) : Prop :=
  post.totalAssets = pre.totalAssets - amount ∧
  post.totalSupply = pre.totalSupply - amount ∧
  post.shareBalances caller = pre.shareBalances caller - amount ∧
  ∀ other, other ≠ caller → post.shareBalances other = pre.shareBalances other

/-- `balanceOf(account)` returns the account's shares. -/
def balanceOf_spec (account : Address) (result : Uint256) (v : Storage) : Prop :=
  result = v.shareBalances account

/-- A deposit of `amount` overflows none of the three counters it increments. -/
def depositFits (amount : Uint256) (caller : Address) (v : Storage) : Prop :=
  (v.shareBalances caller).val + amount.val ≤ Verity.Core.MAX_UINT256 ∧
  v.totalAssets.val + amount.val ≤ Verity.Core.MAX_UINT256 ∧
  v.totalSupply.val + amount.val ≤ Verity.Core.MAX_UINT256

/-- A withdrawal of `amount` is covered by the caller's shares and both totals,
so none of the three guards in `withdraw` reverts. -/
def withdrawCovered (amount : Uint256) (caller : Address) (v : Storage) : Prop :=
  amount.val ≤ (v.shareBalances caller).val ∧
  amount.val ≤ v.totalAssets.val ∧
  amount.val ≤ v.totalSupply.val

end Contracts.VaultFromSolidity.Spec
