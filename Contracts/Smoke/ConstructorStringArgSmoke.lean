import Contracts.Common

/-!
Deployment fixture for `test/ConstructorArgsDynamicOffset.t.sol`: the `String`
argument's ABI head offset must be bounds checked before it is rebased onto the
copied constructor arguments.
-/

namespace Contracts.Smoke

open Verity hiding pure bind

verity_contract ConstructorStringArgSmoke where
  storage
    supply : Uint256 := slot 0

  constructor (_name : String, initialSupply : Uint256) := do
    setStorage supply initialSupply

  function view get () : Uint256 := do
    let v ← getStorage supply
    return v

end Contracts.Smoke
