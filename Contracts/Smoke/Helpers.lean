import Contracts.Common
import Compiler.CheckContract
import Contracts.Counter.Counter
import Contracts.SimpleStorage.SimpleStorage
import Contracts.Owned.Owned
import Contracts.SafeCounter.SafeCounter
import Contracts.OwnedCounter.OwnedCounter
import Contracts.Ledger.Ledger
import Contracts.Vault.Vault
import Contracts.SimpleToken.SimpleToken
import Contracts.ERC20.ERC20
import Contracts.ERC721.ERC721
import Compiler.Modules.Calls
import Compiler.Modules.Callbacks
import Compiler.Modules.Create2SSTORE2
import Compiler.Modules.ERC20
import Compiler.Modules.Oracle
import Compiler.Modules.Precompiles

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

def plusInt256Helper (a : Uint256) (b : Int256) : Uint256 :=
  if b < 0 then sub a (toUint256 (-b)) else add a (toUint256 b)

def eqWordHelper (a : Uint256) (b : Uint256) : Uint256 :=
  if a = b then 1 else 0

verity_contract ModifierInheritanceBase where
  types
    InheritedValue : Uint256
  storage
    owner : Address := slot 0

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  modifier onlyOwner := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"

  function virtual value () : Uint256 := do
    return 1

verity_contract ModifierInheritanceChild is ModifierInheritanceBase where
  storage
    counter : Uint256 := slot 1

  constructor (initialOwner : Address) ModifierInheritanceBase(initialOwner) := do
    setStorage counter 7

  function bump () with onlyOwner : Unit := do
    -- Modifier-local bindings have their own scope and may be reused here.
    let sender ← getStorage counter
    setStorage counter (sender + 1)

  -- Child signatures may use user-defined types declared by the parent.
  function setInherited (next : InheritedValue) : Unit := do
    setStorage counter next

  function override value () : Uint256 := do
    return 2

#check_contract ModifierInheritanceBase
#check_contract ModifierInheritanceChild

end Contracts.Smoke
