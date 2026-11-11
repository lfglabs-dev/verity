import Contracts.Common
import Compiler.Modules.Precompiles

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

verity_mixin StaticCallConstructorMixin where
  storage
  constructor () := do
    ecmBind [sumX, sumY]
      (Compiler.Modules.Precompiles.bn256AddModule "sumX" "sumY")
      [1, 2, 3, 4]
    pure ()

verity_contract StaticCallConstructorHost include StaticCallConstructorMixin where
  storage
  constructor () StaticCallConstructorMixin() := do
    ecmBind [sumX, sumY]
      (Compiler.Modules.Precompiles.bn256AddModule "sumX" "sumY")
      [5, 6, 7, 8]
    pure ()

-- The precompile's answer comes from the adversary in the executable, so a
-- constructor making only a static ECM call takes the call context too.
example : Contract Unit := StaticCallConstructorMixin.constructor .stub
example : Contract Unit := StaticCallConstructorHost.constructor .stub

end Contracts.Smoke
