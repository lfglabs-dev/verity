import Contracts.Common
import Compiler.CheckContract

set_option linter.unusedVariables false

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

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
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compiles to an ABI-encoded CALL to this; the CALL-to-EDSL-hop refinement is manual."]
    : Uint256 := do
    tryCall (selfCall hopWithArg(amount)) then
      (do setStorage last (add amount 100))
    catch
      (do setStorage last 2)
    let v ← getStorage last
    return v

  function reentrancy_trusted allow_post_interaction_writes catchArgWithCall (sink : ISink, amount : Uint256)
    local_obligations [manual_low_level_refinement := assumed "tryCall/selfCall compiles to an ABI-encoded CALL to this; the CALL-to-EDSL-hop refinement is manual."]
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

end Contracts.Smoke
