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

  -- Two tries in one scope, and a try nested in a catch body, each get their
  -- own synthetic success/pointer locals.
  function reentrancy_trusted allow_post_interaction_writes sequentialTries ()
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compiles to an ABI-encoded CALL to this; the CALL-to-EDSL-hop refinement is manual."]
    : Uint256 := do
    tryCall (selfCall failHop) then
      (do setStorage last 1)
    catch
      (do setStorage last 2)
    tryCall (selfCall okHop) then
      (do setStorage last 4)
    catch
      (do setStorage last 5)
    let v ← getStorage last
    return v

  function reentrancy_trusted allow_post_interaction_writes nestedTry ()
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compiles to an ABI-encoded CALL to this; the CALL-to-EDSL-hop refinement is manual."]
    : Uint256 := do
    tryCall (selfCall failHop) then
      (do setStorage last 1)
    catch
      (do
        tryCall (selfCall okHop) then
          (do setStorage last 7)
        catch
          (do setStorage last 8))
    let v ← getStorage last
    return v

  -- A binder try nested in a binder's catch body: the inner one re-raises its
  -- own callee's payload, so the outer `revert err` is never reached.
  function reentrancy_trusted allow_post_interaction_writes rethrowNested ()
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compiles to an ABI-encoded CALL to this; the CALL-to-EDSL-hop refinement is manual."]
    : Unit := do
    tryCall (selfCall failHop) then
      (do setStorage last 1)
    catch err =>
      (do
        tryCall (selfCall failHop) then
          (do setStorage last 9)
        catch inner =>
          (do revert inner)
        revert err)

  function panicHop () : Unit := do
    panic(17)

  -- A caught failure leaves the callee's exact revert bytes in the EIP-211
  -- buffer: `revertReturndata` re-raises `Panic(0x11)` as its 36 bytes.
  function reentrancy_trusted allow_post_interaction_writes rethrowViaReturndata ()
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compiles to an ABI-encoded CALL to this; the CALL-to-EDSL-hop refinement is manual."]
    : Unit := do
    tryCall (selfCall panicHop) then
      (do setStorage last 1)
    catch
      (do revertReturndata)

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
error: nested catch payload 'err' shadows an enclosing one; rename it
-/
#guard_msgs in
verity_contract TryCatchPayloadShadowRejected where
  storage
    last : Uint256 := slot 0

  function failHop () : Unit := do
    require false "fail"

  function reentrancy_trusted allow_post_interaction_writes shadow ()
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compiles to an ABI-encoded CALL to this; the CALL-to-EDSL-hop refinement is manual."]
    : Unit := do
    tryCall (selfCall failHop) then
      (do setStorage last 1)
    catch err =>
      (do
        tryCall (selfCall failHop) then
          (do setStorage last 2)
        catch err =>
          (do revert err))

/--
error: `revert stray` re-raises a payload bound by `catch stray =>`; none is in scope
-/
#guard_msgs in
verity_contract TryCatchPayloadUnboundRejected where
  storage
    last : Uint256 := slot 0

  function unbound () : Unit := do
    revert stray

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

/-- `revertReturndata` after a caught `Panic(0x11)` re-raises its exact 36 bytes. -/
example :
    (match Contract.run (TryCatchSmoke.rethrowViaReturndata Contracts.ExecutableCallContext.stub)
        Verity.defaultState with
      | ContractResult.revert p _ => some p.encode | ContractResult.success _ _ => none) =
      some (Verity.Core.RevertPayload.encode (.panic 0x11)) := by
  decide

end Contracts.Smoke
