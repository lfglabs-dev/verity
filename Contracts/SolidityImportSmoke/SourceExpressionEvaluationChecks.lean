import Compiler.Proofs.IRGeneration.SourceExpressionEvaluation
namespace SolidityImportSmoke.SourceExpressionEvaluationChecks
open Compiler.CompilationModel Compiler.Proofs.IRGeneration
open SourceSemantics SourceExpressionOutcome
private def refusalHelper : FunctionSpec :=
  { name := "refused", params := [], returnType := some .uint256, isInternal := true,
    body := [.create2 "created" (.literal 0) (.literal 0) (.literal 0), .return (.literal 1)] }
private def valueHelper : FunctionSpec :=
  { name := "value", params := [], returnType := some .uint256, isInternal := true,
    body := [.letVar "local" (.literal 8), .mstore (.literal 96) (.literal 9), .return (.literal 7)] }
private def model : CompilationModel :=
  { name := "TypedExpressions", fields := [], constructor := none,
    functions := [refusalHelper, valueHelper] }
private def caller : RuntimeState :=
  { world := Verity.defaultState.writeSlot 0 19, bindings := [("outer", 11)] }
private def runBody := execStmtListWithHelpers model [] 3
private def expected := "CREATE2 requires an actual opcode-entry execution context"
private def expectRefusal (result : StmtResult) : IO Unit := do
  match result with
  | .interpretationError message => unless message == expected do throw (IO.userError message)
  | _ => throw (IO.userError "typed expression refusal became an EVM result")
def runChecks : IO Unit := do
  expectRefusal (assign "result" (invoke runBody model caller "refused" []))
  expectRefusal (assign "result" ((invoke runBody model caller "refused" []).bind
    (fun value state => .value (value + 1) state)))
  match invoke runBody model caller "value" [] with
  | .value value next =>
      unless value == 7 && lookupValue next.bindings "outer" == 11 &&
          next.bindings.length == 1 && (next.world.memory 96).val == 9 && (next.world.memory 0).val == 7 &&
          next.world.readSlot 0 == caller.world.readSlot 0 do
        throw (IO.userError "typed helper dropped returned world or leaked locals")
  | _ => throw (IO.userError "typed helper success failed")
  let context : Verity.Core.Model.ExecutionContext :=
    { opcode := { gas := 0, depth := 0, isStatic := false }, warm := fun _ => false }
  let exceptional : RuntimeState := { caller with executionContext := some context }
  match assign "result" (ofHelperBody caller (.exceptional exceptional)) with
  | .exceptional next =>
      unless next.executionContext.isSome && next.bindings == caller.bindings do
        throw (IO.userError "typed expression lost exceptional state")
  | _ => throw (IO.userError "typed expression exceptional result became ordinary revert")
  match assign "result" (ofHelperBody caller .revert) with
  | .revert => pure ()
  | _ => throw (IO.userError "ordinary expression revert changed")
  match ofHelperBody caller (.stop caller) with
  | .interpretationError _ => pure ()
  | _ => throw (IO.userError "void helper fabricated expression value")
  let evaluate : RuntimeState → Expr → Result Nat := fun state expr =>
    match expr with
    | .internalCall name args =>
        if args.isEmpty then invoke runBody model state name []
        else .interpretationError "test evaluator requires no arguments"
    | .literal value => .value value { state with world := state.world.writeSlot 1 value }
    | .storage _ => .value (state.world.readSlot 1).val state
    | _ => .interpretationError "test evaluator unsupported expression"
  match evalList evaluate caller [.literal 23, .storage "probe"] with
  | .value values next =>
      unless values == [23, 23] && (next.world.readSlot 1).val == 23 do
        throw (IO.userError "typed expression arguments lost order or threaded state")
  | _ => throw (IO.userError "typed expression argument list failed")
  match evalList evaluate caller [.internalCall "refused" [], .literal 99] with
  | .interpretationError message => unless message == expected do throw (IO.userError message)
  | _ => throw (IO.userError "typed expression list continued after refusal")
  match invoke runBody model caller "absent" [] with
  | .interpretationError _ => pure ()
  | _ => throw (IO.userError "missing typed expression helper accepted")
  let checked := SourceExpressionEvaluation.eval runBody model [] 64 caller
  expectRefusal (assign "result" (checked (.internalCall "refused" [])))
  expectRefusal (assign "result" (checked (.add (.literal 1) (.internalCall "refused" []))))
  match checked (.add (.internalCall "value" []) (.mload (.literal 96))) with
  | .value value next =>
      unless value == 16 && (next.world.memory 96).val == 9 && next.bindings == caller.bindings do
        throw (IO.userError "recursive typed expression lost helper poststate")
  | _ => throw (IO.userError "recursive typed expression success refused")
  match checked (.ite (.literal 0) (.internalCall "refused" []) (.literal 17)) with
  | .value value _ => unless value == 17 do throw (IO.userError "typed conditional wrong result")
  | _ => throw (IO.userError "typed conditional evaluated untaken helper")
  match SourceExpressionEvaluation.eval runBody model [] 0 caller (.literal 1) with
  | .interpretationError _ => pure ()
  | _ => throw (IO.userError "typed expression fuel became EVM outcome")
  IO.println "recursive typed source expression checks passed"
end SolidityImportSmoke.SourceExpressionEvaluationChecks
def main : IO Unit := SolidityImportSmoke.SourceExpressionEvaluationChecks.runChecks
