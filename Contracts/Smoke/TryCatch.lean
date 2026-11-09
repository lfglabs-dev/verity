import Contracts.Common
import Compiler.CheckContract
import Contracts.Smoke.TryCatchSmoke
import Contracts.Smoke.TryCatchArgSmoke

set_option linter.unusedVariables false

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

/--
error: selfCall 'hopWithArg' expects 1 argument(s), got 0; use `selfCall hopWithArg(...)`
-/
#guard_msgs in
verity_contract TryCatchMissingArgRejected where
  storage
    last : Uint256 := slot 0

  function hopWithArg (amount : Uint256) : Unit := do
    setStorage last amount

  function reentrancy_trusted allow_post_interaction_writes bad () : Unit := do
    tryCall (selfCall hopWithArg) then
      (do setStorage last 1)
    catch
      (do setStorage last 2)

/--
error: selfCall 'hopWithArg' expects 1 argument(s), got 2
-/
#guard_msgs in
verity_contract TryCatchExtraArgRejected where
  storage
    last : Uint256 := slot 0

  function hopWithArg (amount : Uint256) : Unit := do
    setStorage last amount

  function reentrancy_trusted allow_post_interaction_writes bad () : Unit := do
    tryCall (selfCall hopWithArg(1, 2)) then
      (do setStorage last 1)
    catch
      (do setStorage last 2)

/--
error: selfCall 'hop' targets an internal function; `this.f()` needs an external function
-/
#guard_msgs in
verity_contract TryCatchInternalTargetRejected where
  storage
    last : Uint256 := slot 0

  function internal hop () : Unit := do
    setStorage last 3

  function reentrancy_trusted allow_post_interaction_writes bad () : Unit := do
    tryCall (selfCall hop) then
      (do setStorage last 1)
    catch
      (do setStorage last 2)

/--
error: selfCall 'hopWithBytes' parameter 'payload' has type bytes; only single-word static parameters are ABI-encoded on the compilation path
-/
#guard_msgs in
verity_contract TryCatchDynamicArgRejected where
  storage
    last : Uint256 := slot 0

  function hopWithBytes (payload : Bytes) : Unit := do
    setStorage last 3

  function reentrancy_trusted allow_post_interaction_writes bad (payload : Bytes) : Unit := do
    tryCall (selfCall hopWithBytes(payload)) then
      (do setStorage last 1)
    catch
      (do setStorage last 2)

def writeLast (n : Uint256) : Contract Unit :=
  setStorage ⟨0⟩ n

def failHandler : String → Contract Unit := fun _ => writeLast 2
def okHandler : Unit → Contract Unit := fun _ => writeLast 1
def boomHandler : Unit → Contract Unit := fun _ => require false "success-body"

/-- One test for `caught_failure_starts_at_snapshot`. -/
theorem try_caught_failure_starts_at_snapshot (s : ContractState) :
    (Contract.selfCall TryCatchSmoke.failHop).run s =
      ContractResult.revert "fail" s →
    Contract.tryWith (Contract.selfCall TryCatchSmoke.failHop) okHandler failHandler s =
      failHandler "fail" s :=
  fun h =>
    caught_failure_starts_at_snapshot
      (Contract.selfCall TryCatchSmoke.failHop) okHandler failHandler s "fail" h

/-- One test for `success_body_failure_not_caught`. -/
theorem try_success_body_failure_not_caught (s s' s'' : ContractState) :
    (Contract.selfCall TryCatchSmoke.okHop).run s = ContractResult.success () s' →
    boomHandler () s' = ContractResult.revert "success-body" s'' →
    Contract.tryWith (Contract.selfCall TryCatchSmoke.okHop) boomHandler failHandler s =
      ContractResult.revert "success-body" s'' :=
  fun h hfail =>
    success_body_failure_not_caught
      (Contract.selfCall TryCatchSmoke.okHop) boomHandler failHandler s s' s'' ()
      "success-body" h hfail

/-- One test for `try_success_commits`. -/
theorem try_success_commits_test (s s' s'' : ContractState) :
    (Contract.selfCall TryCatchSmoke.okHop).run s = ContractResult.success () s' →
    okHandler () s' = ContractResult.success () s'' →
    Contract.tryWith (Contract.selfCall TryCatchSmoke.okHop) okHandler failHandler s =
      ContractResult.success () s'' :=
  fun h hok =>
    try_success_commits
      (Contract.selfCall TryCatchSmoke.okHop) okHandler failHandler s s' s'' () h hok

example :
    (TryCatchSmoke.spec.functions).any (fun fn =>
      fn.name == "catchFail") = true := by
  decide

end Contracts.Smoke
