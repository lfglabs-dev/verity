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
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compilation model is CALL-with-status to this; selector encoding is a documented gap."]
    : Uint256 := do
    tryCall (selfCall failHop) then
      (do setStorage last 1)
    catch
      (do setStorage last 2)
    let v ← getStorage last
    return v

  function reentrancy_trusted allow_post_interaction_writes catchOk ()
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compilation model is CALL-with-status to this; selector encoding is a documented gap."]
    : Uint256 := do
    tryCall (selfCall okHop) then
      (do setStorage last 4)
    catch
      (do setStorage last 5)
    let v ← getStorage last
    return v

#check_contract TryCatchSmoke

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
