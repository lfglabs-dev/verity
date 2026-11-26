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

  -- `catch err => … revert err` re-raises the callee's `Error("fail")`.
  function reentrancy_trusted allow_post_interaction_writes rethrowFail ()
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compiles to an ABI-encoded CALL to this; the CALL-to-EDSL-hop refinement is manual."]
    : Unit := do
    tryCall (selfCall failHop) then
      (do setStorage last 1)
    catch err =>
      (do
        setStorage last 6
        revert err)

#check_contract TryCatchSmoke

/-- The EDSL re-raises the callee's payload unchanged. -/
example :
    (match Contract.run (TryCatchSmoke.rethrowFail Contracts.ExecutableCallContext.stub)
        Verity.defaultState with
      | ContractResult.revert p _ => some p | ContractResult.success _ _ => none) =
      some (Verity.Core.RevertPayload.errorString "fail") := by
  decide

/--
error: catch payload 'err' can only be re-raised with `revert err`
-/
#guard_msgs in
verity_contract TryCatchPayloadMisuseRejected where
  storage
    last : Uint256 := slot 0

  function failHop () : Unit := do
    require false "fail"

  function reentrancy_trusted allow_post_interaction_writes useErr ()
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compiles to an ABI-encoded CALL to this; the CALL-to-EDSL-hop refinement is manual."]
    : Unit := do
    tryCall (selfCall failHop) then
      (do setStorage last 1)
    catch err =>
      (do setStorage last err)

/--
error: `catch err =>` needs a `selfCall` attempt: a word attempt has no revert payload
-/
#guard_msgs in
verity_contract TryCatchPayloadWordAttemptRejected where
  storage
    last : Uint256 := slot 0

  function reentrancy_trusted allow_post_interaction_writes wordAttempt ()
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compiles to an ABI-encoded CALL to this; the CALL-to-EDSL-hop refinement is manual."]
    : Unit := do
    tryCall 0 then
      (do setStorage last 1)
    catch err =>
      (do revert err)

end Contracts.Smoke
