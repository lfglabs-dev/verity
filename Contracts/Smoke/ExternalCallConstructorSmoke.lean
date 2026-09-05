import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

verity_mixin ExternalCallConstructorMixin where
  storage
  linked_externals
    external initializeRemote(Uint256)
  constructor (seed : Uint256) := do
    initializeHelper(seed)
  function internal initializeHelper (seed : Uint256) : Unit := do
    callExternal initializeRemote(seed)

verity_contract ExternalCallConstructorHost include ExternalCallConstructorMixin where
  storage
  constructor (seed : Uint256) ExternalCallConstructorMixin(seed) := do
    pure ()

example : Contract Unit := ExternalCallConstructorMixin.constructor .stub 41
example : Contract Unit := ExternalCallConstructorHost.constructor .stub 41

end Contracts.Smoke
