import Compiler.Proofs.IRGeneration.SourceSemantics

namespace SolidityImportSmoke.SourceHelperContextChecks
open Compiler.CompilationModel Compiler.Proofs.IRGeneration
open SourceSemantics

private def leaf : FunctionSpec :=
  { name := "leaf", params := [], returnType := some .uint256, isInternal := true,
    body := [.returndataCopy (.literal 0) (.literal 33) (.literal 0), .return (.literal 99)] }
private def middle : FunctionSpec :=
  { name := "middle", params := [], returnType := none, isInternal := true,
    body := [.internalCall "leaf" [], .stop] }
private def returning : FunctionSpec :=
  { name := "returning", params := [], returnType := some .uint256, isInternal := true,
    body := [.return (.literal 42)] }
private def model : CompilationModel :=
  { name := "SourceHelperContext", fields := [], functions := [leaf, middle, returning], constructor := none }
private def context : Verity.Core.Model.ExecutionContext :=
  { opcode := { gas := 19, depth := 7, isStatic := false }, warm := fun _ => false }
private def initial : RuntimeState :=
  { world := { Verity.defaultState with returndata := [0x1234] }
    bindings := [("caller", 51)], executionContext := some context }

private def checkException (result : StmtResult) : IO Unit := do
  match result with
  | .exceptional terminal =>
      unless terminal.executionContext.map (·.opcode.gas) == some 0 &&
          terminal.executionContext.map (·.opcode.depth) == some 7 &&
          terminal.executionContext.map (·.opcode.isStatic) == some false do
        throw (IO.userError "actual helper exception context changed")
      let publicResult := exceptionalResult model initial.world terminal
      unless publicResult.interpretationError.isNone && publicResult.exceptionalContext.map (·.opcode.gas) == some 0 do
        throw (IO.userError "actual helper exception failed public projection")
  | _ => throw (IO.userError "actual helper exception became revert, refusal or success")

def runChecks : IO Unit := do
  let direct := interpretInternalFunctionFuel model 8 leaf initial.world []
    (executionContext := initial.executionContext)
  checkException (failedInternalOutcome direct)
  for call in [.internalCall "leaf" [], .internalCall "middle" [],
      .internalCallAssign ["value"] "leaf" []] do
    checkException (execStmtWithHelpers model [] 8 initial call)
    match execStmtWithHelpers model [] 8 { initial with executionContext := none } call with
    | .interpretationError message =>
        unless message == "returndata copy exceptional exit requires actual opcode context" do
          throw (IO.userError "contextless nested helper diagnostic changed")
    | _ => throw (IO.userError "contextless nested helper acquired EVM status")
  let directSuccess := interpretInternalFunctionFuel model 8 returning initial.world []
    (executionContext := initial.executionContext)
  unless directSuccess.success && directSuccess.returnValue == some 42 &&
      directSuccess.executionContext.map (·.opcode.gas) == some 19 &&
      directSuccess.executionContext.map (·.opcode.depth) == some 7 do
    throw (IO.userError "successful helper result lost caller frame context")
  match execStmtWithHelpers model [] 8 initial (.internalCallAssign ["value"] "returning" []) with
  | .continue next =>
      unless next.executionContext.map (·.opcode.gas) == some 19 &&
          next.executionContext.map (·.opcode.depth) == some 7 &&
          lookupBinding? next.bindings "caller" == some 51 &&
          lookupBinding? next.bindings "value" == some 42 do
        throw (IO.userError "successful helper did not restore caller frame and bindings")
  | _ => throw (IO.userError "successful helper assignment did not continue")
  match execStmtWithHelpers model [] 8 initial (.internalCall "returning" []) with
  | .continue next =>
      unless next.executionContext.map (·.opcode.gas) == some 19 && next.bindings == initial.bindings do
        throw (IO.userError "successful void helper lost frame or caller locals")
  | _ => throw (IO.userError "successful void helper did not continue")
  IO.println "Source helper actual-context entry, nested exception and success checks passed"

end SolidityImportSmoke.SourceHelperContextChecks

def main : IO Unit := SolidityImportSmoke.SourceHelperContextChecks.runChecks
