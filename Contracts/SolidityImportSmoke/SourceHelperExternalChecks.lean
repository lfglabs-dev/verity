import Compiler.Proofs.IRGeneration.SourceSemantics

namespace SolidityImportSmoke.SourceHelperExternalChecks
open Compiler.CompilationModel Compiler.Proofs.IRGeneration SourceSemantics

private def leaf : FunctionSpec :=
  { name := "leaf", params := [], returnType := some .uint256, isInternal := true,
    body := [.externalCallBind ["receipt"] "oracle" [], .return (.localVar "receipt")] }
private def middle : FunctionSpec :=
  { name := "middle", params := [], returnType := some .uint256, isInternal := true,
    body := [.internalCallAssign ["first"] "leaf" [],
      .externalCallBind ["own"] "oracle" [], .return (.localVar "own")] }
private def caught : FunctionSpec :=
  { name := "caught", params := [], returnType := some .uint256, isInternal := true,
    body := [.tryExternalCallBind "ok" ["reason"] "oracle" [], .return (.localVar "reason")] }
private def stopping : FunctionSpec :=
  { name := "stopping", params := [], returnType := none, isInternal := true,
    body := [.externalCallBind ["receipt"] "oracle" [], .stop] }
private def falling : FunctionSpec :=
  { name := "falling", params := [], returnType := none, isInternal := true,
    body := [.externalCallBind ["receipt"] "oracle" []] }
private def model : CompilationModel :=
  { name := "HelperExternal", fields := [], functions := [leaf, middle, caught, stopping, falling], constructor := none }
private def context : Verity.Core.Model.ExecutionContext :=
  { opcode := { gas := 19, depth := 7, isStatic := false }, warm := fun _ => false }
private def oracle (index : Nat) : ExternalCallOutcome :=
  { succeeded := index != 5, returnValues := [100 + index],
    postCallWorld := some (Verity.defaultState.writeSlot 0 (700 + index)) }
private def initial : RuntimeState :=
  { world := Verity.defaultState, bindings := [("caller", 51)],
    externalCallOracle := oracle, externalCallIndex := 3, executionContext := some context }

private def checkIndex (state : RuntimeState) (index : Nat) : IO Unit := do
  unless state.externalCallIndex == index && state.executionContext.map (·.opcode.depth) == some 7 &&
      state.executionContext.map (·.opcode.gas) == some 19 &&
      lookupBinding? state.bindings "caller" == some 51 &&
      (state.externalCallOracle index).returnValues == [100 + index] do
    throw (IO.userError "helper lost external receipt cursor, actual oracle, context or caller locals")

def runChecks : IO Unit := do
  -- This checks only the legacy value projection; its Option boundary still
  -- cannot certify expression effects or failures. The typed executor is the
  -- integration target for full expression semantics.
  unless evalExprWithHelpers model [] 16 initial (.internalCall "leaf" []) == some 103 do
    throw (IO.userError "legacy helper value projection used the wrong oracle receipt")
  let result := interpretInternalFunctionFuel model 16 middle initial.world []
    (externalCallOracle := oracle) (externalCallIndex := 3) (executionContext := some context)
  unless result.success && result.returnValue == some 104 && result.externalCallIndex == 5 &&
      result.world.readSlot 0 == 704 do
    throw (IO.userError "nested helper lost actual oracle, entry cursor or terminal cursor")
  for helper in [falling, stopping] do
    let result := interpretInternalFunctionFuel model 16 helper initial.world []
      (externalCallOracle := oracle) (externalCallIndex := 3) (executionContext := some context)
    unless result.success && result.returnValue.isNone && result.externalCallIndex == 4 &&
        result.world.readSlot 0 == 703 do
      throw (IO.userError "continue/stop helper projection lost terminal receipt cursor")
  match execStmtWithHelpers model [] 16 initial (.internalCall "middle" []) with
  | .continue next =>
      checkIndex next 5
      unless next.world.readSlot 0 == 704 && next.bindings == initial.bindings do
        throw (IO.userError "void helper failed to preserve its world or caller bindings")
  | _ => throw (IO.userError "void nested helper did not continue")
  match execStmtListWithHelpers model [] 16 initial
      [.internalCallAssign ["value"] "middle" [],
       .internalCallAssign ["failure"] "caught" []] with
  | .continue next =>
      checkIndex next 6
      unless lookupBinding? next.bindings "value" == some 104 &&
          lookupBinding? next.bindings "failure" == some 105 &&
          next.world.readSlot 0 == 704 && next.world.returndata == [105] &&
          (lookupBinding? next.bindings "first").isNone &&
          (lookupBinding? next.bindings "receipt").isNone do
        throw (IO.userError "caught external failure changed world, cursor, returndata or scoped locals")
      match execStmtWithHelpers model [] 16 next (.externalCallBind ["final"] "oracle" []) with
      | .continue finalState =>
          checkIndex finalState 7
          unless lookupBinding? finalState.bindings "final" == some 106 &&
              finalState.world.readSlot 0 == 706 && finalState.world.returndata == [106] do
            throw (IO.userError "caller replayed an already-consumed helper receipt")
      | _ => throw (IO.userError "caller did not continue after nested receipts")
  | _ => throw (IO.userError "assigning nested helper did not continue")
  IO.println "Source helper actual oracle, nested receipt cursor, caught failure and resume checks passed"

end SolidityImportSmoke.SourceHelperExternalChecks

def main : IO Unit := SolidityImportSmoke.SourceHelperExternalChecks.runChecks
