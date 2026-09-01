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

private def callBitBuffer (r : Option (Nat × Compiler.CompilationModel.Denote.DenoteState)) :
    Option (Nat × List Nat) :=
  r.map (fun (b, s) => (b, s.world.returndata))

private def outcomeBuffer (r : StmtOutcome) : Option (List Nat) :=
  match r with | .continue s => some s.world.returndata | _ => none

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

/-- Regression: the try-lane success branch installs the returned words. -/
example :
    outcomeBuffer (execTryExternalCallBind echoEnv [] staleCaller "ok" ["r"] "linked"
      [.literal 7]) = some [7] := by
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

end Contracts.Smoke.ExternalCallValue
