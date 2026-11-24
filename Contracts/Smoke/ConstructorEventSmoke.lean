import Contracts.Common

/-!
Deployment fixture for `test/ConstructorArgsTrailingBytes.t.sol`: the event
emission reads the free-memory pointer inside the constructor, so the
deployment fails if the constructor-argument copy clobbered it.
-/

namespace Contracts.Smoke

open Verity hiding pure bind

verity_contract ConstructorEventSmoke where
  storage
    stored : Uint256 := slot 0

  event_defs
    event Stored(value : Uint256)

  constructor (x : Uint256) := do
    setStorage stored x
    emit "Stored" [x]

  function view get () : Uint256 := do
    let v ← getStorage stored
    return v

end Contracts.Smoke
