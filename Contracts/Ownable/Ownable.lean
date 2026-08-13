import Contracts.Common

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256

verity_mixin Ownable where
  storage
    owner : Address := slot 0

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  modifier onlyOwner := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"

  function transferOwnership (newOwner : Address) with onlyOwner modifies(owner) : Unit := do
    setStorageAddr owner newOwner

  function getOwner () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

end Contracts
