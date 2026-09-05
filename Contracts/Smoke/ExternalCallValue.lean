import Contracts.Common
import Verity.Core.Model.DenoteFunctionCalls
import Verity.Core.Model.MultiContract

namespace Contracts.Smoke.ExternalCallValue

open Contracts
open Verity hiding pure bind
open Compiler.CompilationModel.DenoteFunctionCalls
open Compiler.CompilationModel.DenoteExternalCalls
open Compiler.CompilationModel.Denote (StmtOutcome)
open Verity.MultiContract

example :
    (lookup (fundedBus 5) busAddr).selfBalance = (5 : Uint256) :=
  fundedBus_bus_balance 5

/-! ### EIP-211 returndata in the call-aware denotation

Regressions for the widened-call lanes (`applyRawCall`,
`execExternalCallBind`, `execTryExternalCallBind`) and the multi-contract call
frame: every call-aware transition installs the observed result data as the
frame-local returndata buffer, and every frame entry starts it empty. -/

private def probeOracle : Compiler.CompilationModel.Denote.DenoteOracle :=
  { mappingSlot := fun _ _ => 0
    keccakMemorySlice := fun _ _ _ => 0 }

private def revertAdversary :
    Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel where
  stateTransition := fun _ w => w
  result := fun _ _ => .revert [5]
  gasUsed := fun _ _ => 0

private def failAdversary :
    Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel where
  stateTransition := fun _ w => w
  result := fun _ _ => .failure []
  gasUsed := fun _ _ => 0

private def echoEnv : CallEnv :=
  { oracle := probeOracle
    adversary := echoAdversary
    resolve := fun _ => some { target := 9, value := 0, siteId := 0 } }

private def revertEnv : CallEnv :=
  { oracle := probeOracle
    adversary := revertAdversary
    resolve := fun _ => some { target := 9, value := 0, siteId := 0 } }

private def failEnv : CallEnv :=
  { oracle := probeOracle
    adversary := failAdversary
    resolve := fun _ => some { target := 9, value := 0, siteId := 0 } }

/-- Caller state whose pre-call buffer is stale, so a lane that fails to
install the new call's data is caught reading `[3]`. -/
private def staleCaller : Compiler.CompilationModel.Denote.DenoteState :=
  { world := { Verity.defaultState with selfBalance := 100, returndata := [3] }
    bindings := [] }

private def rawCallSite : CallSite :=
  { siteId := 0, kind := .call, target := 9, value := 0, calldata := [7], gas := 1000 }

private def rawCallLetVarWorks : Bool :=
    match execStmtWithCalls echoEnv [] staleCaller
        (.letVar "ok" (.call (.literal 1000) (.literal 9) (.literal 0)
          (.literal 0) (.literal 0) (.literal 0) (.literal 0))) with
    | .continue post =>
        Compiler.CompilationModel.Denote.lookupValue post.bindings "ok" == 1 &&
          post.world.calls.length == 1
    | _ => false

example : rawCallLetVarWorks = true := by
  native_decide

private def callBitBuffer (r : Option (Nat × Compiler.CompilationModel.Denote.DenoteState)) :
    Option (Nat × List Nat) :=
  r.map (fun (b, s) => (b, s.world.returndata))

private def outcomeBuffer (r : StmtOutcome) : Option (List Nat) :=
  match r with | .continue s => some s.world.returndata | _ => none

private def outcomeBinding (name : String) (r : StmtOutcome) : Option Nat :=
  match r with | .continue s => s.bindings.lookup name | _ => none

/-- `applyRawCall` success installs the callee's words as the buffer. -/
example :
    callBitBuffer (applyRawCall echoEnv staleCaller rawCallSite 0 0) = some (1, [7]) := by
  native_decide

/-- Regression: a reverting callee refills the buffer with its revert payload
instead of leaving the caller's stale `[3]` in place. -/
example :
    callBitBuffer (applyRawCall revertEnv staleCaller rawCallSite 0 0) = some (0, [5]) := by
  native_decide

/-- Regression: a failing callee clears the buffer; the stale `[3]` cannot
survive the call. -/
example :
    callBitBuffer (applyRawCall failEnv staleCaller rawCallSite 0 0) = some (0, []) := by
  native_decide

/-- Regression: the linked success lane installs the returned words over the
stale buffer. -/
example :
    outcomeBuffer (execExternalCallBind echoEnv [] staleCaller ["x"] "linked"
      [.literal 7]) = some [7] := by
  native_decide

/-- Regression: the try-lane failure branch installs the observed payload,
mirroring the source-lane `tryExternalCallBind_failure_installs_returndata`. -/
example :
    outcomeBuffer (execTryExternalCallBind revertEnv [] staleCaller "ok" ["r"] "linked"
      [.literal 7]) = some [5] := by
  native_decide

example :
    outcomeBinding "r" (execTryExternalCallBind revertEnv [] staleCaller "ok" ["r"]
      "linked" [.literal 7]) = some 5 := by
  decide

/-- Regression: the try-lane success branch installs the returned words. -/
example :
    outcomeBuffer (execTryExternalCallBind echoEnv [] staleCaller "ok" ["r"] "linked"
      [.literal 7]) = some [7] := by
  native_decide

/-! #### Insufficient caller balance (PR #2400 Codex P1, round 2)

A value-bearing `call` the caller cannot fund fails with empty returndata;
the stale pre-call buffer must not survive the attempt. Reproduced first
against the pre-fix head: both lanes kept the caller's `[3]`. -/

private def unfundedCallSite : CallSite :=
  { siteId := 0, kind := .call, target := 9, value := 200, calldata := [7], gas := 1000 }

private def unaffordableEnv : CallEnv :=
  { oracle := probeOracle
    adversary := echoAdversary
    resolve := fun _ => some { target := 9, value := 200, siteId := 0 } }

/-- Regression: `applyRawCall` fails the unfundable `call` with bit 0 and
clears the buffer; the stale `[3]` cannot survive the attempt. -/
example :
    callBitBuffer (applyRawCall echoEnv staleCaller unfundedCallSite 0 0) = some (0, []) := by
  native_decide

/-- Regression: the try-lane insufficient-funds branch binds failure and
clears the buffer instead of preserving the pre-call `[3]`. -/
example :
    outcomeBuffer (execTryExternalCallBind unaffordableEnv [] staleCaller "ok" ["r"]
      "linked" [.literal 7]) = some [] := by
  native_decide

/-! #### Call-frame entry reset -/

/-- Two-account world whose callee still carries a stale buffer from an
earlier execution. -/
private def staleCalleeEntryWorld : MultiWorld :=
  { accounts :=
      [ { address := busAddr
          state := { Verity.defaultState with thisAddress := busAddr, selfBalance := 10 } }
        , { address := gatewayAddr
            state := { Verity.defaultState with thisAddress := gatewayAddr, returndata := [3, 3] } } ] }

private def busCallSite : CallSite :=
  { siteId := 0, kind := .call, target := gatewayAddr.toNat, value := 0,
    calldata := [], gas := 1000 }

/-- Regression: the callee enters its call frame with an empty buffer; the
caller-side stale data cannot cross the frame boundary. -/
example :
    (callEntry staleCalleeEntryWorld busAddr gatewayAddr busCallSite).map
      (fun frame => frame.calleeEntry.returndata) = some [] := by
  native_decide

/-! #### Round-3 Codex P1s: caller-side install and self-delegate entry

The framed multi-contract path must install the observed call result into
the *caller's* EIP-211 buffer on every outcome, and a self-delegate frame
must still enter with an empty buffer. Reproduced first against the
pre-fix head: the caller kept its stale `[3]` across its own outbound
call, and the self-delegate body inherited the account's `[3]`. -/

private def staleCallerEntryWorld : MultiWorld :=
  { accounts :=
      [ { address := busAddr
          state :=
            { Verity.defaultState with
              thisAddress := busAddr, selfBalance := 10, returndata := [3] } }
      , { address := gatewayAddr
          state := { Verity.defaultState with thisAddress := gatewayAddr } } ] }

private def framedSuccessBody (_frame : CallFrame) : CalleeExecution :=
  { result := .success [5], post := Verity.defaultState }

private def framedRevertBody (_frame : CallFrame) : CalleeExecution :=
  { result := .revert [5], post := Verity.defaultState }

/-- Regression: the framed call installs the callee's payload into the
caller's EIP-211 buffer; the caller's stale `[3]` cannot survive its own
outbound call. -/
example :
    (Verity.MultiContract.call staleCallerEntryWorld busAddr gatewayAddr busCallSite framedSuccessBody).map
      (fun observation => (lookup observation.world busAddr).returndata) = some [5] := by
  native_decide

/-- Regression: a reverting framed call installs the revert payload into
the caller's buffer. -/
example :
    (Verity.MultiContract.call staleCallerEntryWorld busAddr gatewayAddr busCallSite framedRevertBody).map
      (fun observation => (lookup observation.world busAddr).returndata) = some [5] := by
  native_decide

/-- Regression: `callValue` clears the caller's buffer, matching the empty
result it journals. -/
example :
    (callValue staleCallerEntryWorld busAddr gatewayAddr 0).map
      (fun world => (lookup world busAddr).returndata) = some [] := by
  native_decide

private def selfDelegateSite : CallSite :=
  { siteId := 0, kind := .delegatecall, target := busAddr.toNat, value := 0,
    calldata := [], gas := 1000 }

/-- Regression: a self-delegate frame enters with an empty buffer; the
account's stale `[3]` cannot cross the frame boundary. -/
example :
    (selfDelegateEntry staleCallerEntryWorld busAddr selfDelegateSite).map
      (fun frame => frame.calleeEntry.returndata) = some [] := by
  native_decide

/-! ### PR3 executable `evmCallWords` memory / value close-out -/

private def memState : ContractState :=
  { Verity.defaultState with
      selfBalance := 100
      memory := fun i => if i = 0 then 7 else 0
      returndata := [3] }

private def echoCallAdv :
    Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel where
  stateTransition := fun _ w => w
  result := fun site _ => .success site.calldata
  gasUsed := fun _ _ => 0

/-- Successful raw call reads caller memory as calldata, writes returndata,
and debits value. -/
example :
    let r := (Contracts.evmCallWords echoCallAdv 1000 9 10 0 1 2 1).run memState
    r.fst = (1 : Uint256) ∧
      r.snd.selfBalance = (90 : Uint256) ∧
      r.snd.returndata = [7] ∧
      r.snd.memory 2 = (7 : Uint256) := by
  native_decide

/-- Unfunded raw call returns bit 0 with an empty buffer and never invokes
the adversary (stale `[3]` does not survive). -/
example :
    let r := (Contracts.evmCallWords echoCallAdv 1000 9 200 0 1 0 0).run memState
    r.fst = (0 : Uint256) ∧ r.snd.returndata = [] ∧ r.snd.calls = [] := by
  native_decide

end Contracts.Smoke.ExternalCallValue
