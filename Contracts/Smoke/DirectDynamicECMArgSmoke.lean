import Contracts.Common

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

-- `ecmCall`, `ecmDo` and `ecmBind` pass a direct bytes/string/array parameter to the
-- module as two words, `data_offset` and `length`, on the model path and in the
-- compiled code alike (`test/DirectDynamicECMArgSmoke.t.sol`).
def directDynamicEcmResultModule (resultVar : String) : Compiler.ECM.ExternalCallModule where
  name := "directDynamicEcmResult"
  numArgs := 2
  resultVars := [resultVar]
  writesState := false
  readsState := false
  axioms := []
  -- Binds the dynamic argument's length (its second word), so the test can see that
  -- both `data_offset` and `length` reach the module.
  compile := fun _ctx args => do
    let some len := args[1]? | throw "directDynamicEcmResult expects data_offset and length"
    pure [.let_ resultVar len]

def directDynamicEcmEffectModule : Compiler.ECM.ExternalCallModule where
  name := "directDynamicEcmEffect"
  numArgs := 2
  resultVars := []
  writesState := false
  readsState := false
  axioms := []
  -- Reverts when the dynamic argument is longer than 3 bytes: an observable use of `length`.
  compile := fun _ctx args => do
    let some len := args[1]? | throw "directDynamicEcmEffect expects data_offset and length"
    pure [.if_ (.call "gt" [len, .lit 3]) [.exprStmt (.call "revert" [.lit 0, .lit 0])]]

verity_contract DirectDynamicECMArgSmoke where
  storage

  function fromCall (payload : Bytes) : Uint256 := do
    let result ← ecmCall directDynamicEcmResultModule [payload]
    return result

  function fromDo (message : String) : Unit := do
    ecmDo directDynamicEcmEffectModule [message]

  function fromBind (values : Array Uint256) : Unit := do
    ecmBind [result] (directDynamicEcmResultModule "result") [values]

/-- Executable ECM calls use the same synthetic `data_offset, length` key as
the model for direct bytes, string, and dynamic-array parameters. -/
example :
    ((DirectDynamicECMArgSmoke.fromCall (ByteArray.mk #[1, 2, 3])).run defaultState).getState.calls.head?.map
        (fun call => call.calldata) = some [0, 3] := by
  decide

example :
    ((DirectDynamicECMArgSmoke.fromDo "verity").run
      defaultState).getState.calls.head?.map (fun call => call.calldata) = some [0, 6] := by
  decide

example :
    ((DirectDynamicECMArgSmoke.fromBind #[4, 5]).run
      defaultState).getState.calls.head?.map (fun call => call.calldata) = some [0, 2] := by
  decide

end Contracts.Smoke
