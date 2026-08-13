import Contracts.Common
import Contracts.Ownable.Ownable

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract OwnedCounterComposed include Ownable where
  storage
    count : Uint256 := slot 1

  constructor (initialOwner : Address) Ownable(initialOwner) := do
    setStorage count 0

  function increment () with onlyOwner modifies(count) : Unit := do
    let current ← getStorage count
    setStorage count (add current 1)

  function decrement () with onlyOwner modifies(count) : Unit := do
    let current ← getStorage count
    setStorage count (sub current 1)

  function getCount () : Uint256 := do
    let current ← getStorage count
    return current

end Contracts
