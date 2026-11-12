import Contracts.Common
import Compiler.CheckContract

set_option linter.unusedVariables false

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract TryCatchSmoke where
  storage
    last : Uint256 := slot 0

  function failHop () : Unit := do
    require false "fail"

  function okHop () : Unit := do
    setStorage last 3

  function reentrancy_trusted allow_post_interaction_writes catchFail ()
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compiles to an ABI-encoded CALL to this; the CALL-to-EDSL-hop refinement is manual."]
    : Uint256 := do
    tryCall (selfCall failHop) then
      (do setStorage last 1)
    catch
      (do setStorage last 2)
    let v ← getStorage last
    return v

  function reentrancy_trusted allow_post_interaction_writes catchOk ()
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compiles to an ABI-encoded CALL to this; the CALL-to-EDSL-hop refinement is manual."]
    : Uint256 := do
    tryCall (selfCall okHop) then
      (do setStorage last 4)
    catch
      (do setStorage last 5)
    let v ← getStorage last
    return v

#check_contract TryCatchSmoke

end Contracts.Smoke
