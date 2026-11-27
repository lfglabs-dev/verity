import Contracts.Common
import Compiler.CheckContract

set_option linter.unusedVariables false

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

-- A `strict_calls` contract swallows no callee failure. `tryCall … catch` stays
-- allowed: the source handles the failure explicitly. A low-level `call` or a
-- flag-returning module is rejected (`Compiler/CompilationModelFeatureTest.lean`).
verity_contract StrictCallsSmoke where
  strict_calls
  storage
    last : Uint256 := slot 0

  function failHop () : Unit := do
    require false "fail"

  function reentrancy_trusted allow_post_interaction_writes catchFail ()
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compiles to an ABI-encoded CALL to this; the CALL-to-EDSL-hop refinement is manual."]
    : Uint256 := do
    tryCall (selfCall failHop) then
      (do setStorage last 1)
    catch
      (do setStorage last 2)
    let v ← getStorage last
    return v

#check_contract StrictCallsSmoke

end Contracts.Smoke

namespace Contracts.Smoke.StrictCallsSmokeProofs

open Contracts.Smoke

/-- `strict_calls` reaches the compilation model. -/
example : StrictCallsSmoke.spec.strictCalls = true := rfl

end Contracts.Smoke.StrictCallsSmokeProofs
