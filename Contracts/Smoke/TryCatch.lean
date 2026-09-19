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

-- Argument-carrying self-call hops (`this.f(x)` in Solidity). The hop may
-- itself make external calls; the executable plane threads the call context
-- into it, so `tryCall (selfCall f(x))` works for the Pareto
-- `try this.sendFundsToBorrower(amount) {..} catch {..}` shape.
verity_contract TryCatchArgSmoke where
  storage
    last : Uint256 := slot 0

  interfaces
    interface ISink where
      function notify(Uint256)
    end

  function hopWithArg (amount : Uint256) : Unit := do
    require (amount != 0) "zero amount"
    setStorage last amount

  function reentrancy_trusted allow_post_interaction_writes hopWithCall (sink : ISink, amount : Uint256) : Unit := do
    sink.notify amount
    require (amount != 0) "zero amount"
    setStorage last amount

  function reentrancy_trusted allow_post_interaction_writes catchArg (amount : Uint256)
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compilation model is CALL-with-status to this; selector and argument encoding are a documented gap."]
    : Uint256 := do
    tryCall (selfCall hopWithArg(amount)) then
      (do setStorage last (add amount 100))
    catch
      (do setStorage last 2)
    let v ← getStorage last
    return v

  function reentrancy_trusted allow_post_interaction_writes catchArgWithCall (sink : ISink, amount : Uint256)
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compilation model is CALL-with-status to this; selector and argument encoding are a documented gap."]
    : Uint256 := do
    tryCall (selfCall hopWithCall(sink, amount)) then
      (do setStorage last (add amount 100))
    catch
      (do setStorage last 2)
    let v ← getStorage last
    return v

#check_contract TryCatchArgSmoke

/-- Reverting hop with an argument: the handler runs from the pre-call snapshot. -/
def tryCatchArgZeroValue : Bool :=
  match TryCatchArgSmoke.catchArg .stub 0 Verity.defaultState with
  | .success v _ => v == (2 : Uint256)
  | .revert _ _ => false

example : tryCatchArgZeroValue = true := by decide

/-- Succeeding hop with an argument: the success body sees the hop's writes. -/
def tryCatchArgSevenValue : Bool :=
  match TryCatchArgSmoke.catchArg .stub 7 Verity.defaultState with
  | .success v _ => v == (107 : Uint256)
  | .revert _ _ => false

example : tryCatchArgSevenValue = true := by decide

/-- A hop that makes an external call is still a self-call hop (context threaded). -/
def tryCatchArgWithCallValue : Bool :=
  match TryCatchArgSmoke.catchArgWithCall .stub (11 : Address) 0 Verity.defaultState with
  | .success v _ => v == (2 : Uint256)
  | .revert _ _ => false

example : tryCatchArgWithCallValue = true := by decide

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
