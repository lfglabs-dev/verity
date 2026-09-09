import Contracts.Vault.Vault
import Contracts.Vault.Solidity

namespace Contracts.Vault
open Verity

-- The entry adapter below is valid only while the native compiler metadata
-- marks every Vault function nonpayable. A payable edit must fail this check.
#guard Vault.spec.functions.all (fun fn => !fn.isPayable)

/-- Two implementations, one explicit external-call boundary for shared proofs.
`verity_contract` function definitions are bodies; its compiler adds nonpayable
checks at dispatch. The Solidity importer already exposes guarded entrypoints.
This wrapper models that existing dispatch rule, not a change to either body. -/
inductive Implementation where
  | verity
  | solidity

def nonpayableEntry {α : Type} (body : Contract α) : Contract α := do
  let value ← msgValue
  require (value.val == 0) "Nonpayable"
  body

namespace Implementation

def deposit (impl : Implementation) (assets : Uint256) : Contract Unit :=
  match impl with
  | .verity => nonpayableEntry (Vault.deposit assets)
  | .solidity => Solidity.deposit assets

def withdraw (impl : Implementation) (shares : Uint256) : Contract Unit :=
  match impl with
  | .verity => nonpayableEntry (Vault.withdraw shares)
  | .solidity => Solidity.withdraw shares

def balanceOf (impl : Implementation) (account : Address) : Contract Uint256 :=
  match impl with
  | .verity => nonpayableEntry (Vault.balanceOf account)
  | .solidity => Solidity.balanceOf account

def totalAssets (impl : Implementation) : Contract Uint256 :=
  match impl with
  | .verity => nonpayableEntry Vault.totalAssets
  | .solidity => Solidity.totalAssets

def totalSupply (impl : Implementation) : Contract Uint256 :=
  match impl with
  | .verity => nonpayableEntry Vault.totalSupply
  | .solidity => Solidity.totalSupply

/-- The Solidity public-mapping getter has the same role as Verity's balanceOf. -/
def shareBalances (impl : Implementation) (account : Address) : Contract Uint256 :=
  match impl with
  | .verity => nonpayableEntry (Vault.balanceOf account)
  | .solidity => Solidity.shareBalances account

end Implementation
end Contracts.Vault
