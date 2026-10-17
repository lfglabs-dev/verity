import Compiler.Proofs.IRGeneration.SourceSemantics

namespace SolidityImportSmoke.SourceInternalExceptionChecks
open Compiler.CompilationModel Compiler.Proofs.IRGeneration
open SourceSemantics

example (initial : Verity.ContractState) (terminal : RuntimeState) :
    failedInternalOutcome (exceptionalInternalResult initial terminal) = .exceptional terminal :=
  exceptionalInternalResult_failedOutcome initial terminal

example (initial : Verity.ContractState) (terminal : RuntimeState) :
    (exceptionalInternalResult initial terminal).world = initial ∧
      (exceptionalInternalResult initial terminal).success = false ∧
      (exceptionalInternalResult initial terminal).returnValue = none ∧
      (exceptionalInternalResult initial terminal).revertData = [] :=
  exceptionalInternalResult_rollback initial terminal

private def model : CompilationModel :=
  { name := "SourceInternalException", fields := [], functions := [], constructor := none }
private def context : Verity.Core.Model.ExecutionContext :=
  { opcode := { gas := 19, depth := 7, isStatic := false }, warm := fun _ => false }
private def initial : RuntimeState :=
  { world := { Verity.defaultState with returndata := [0x1234] }
    bindings := [("local", 51)], executionContext := some context }

def runChecks : IO Unit := do
  let terminal ← match execReturndataCopy initial 0 33 0 with
    | .exceptional state => pure state
    | _ => throw (IO.userError "actual copy failed to produce exception")
  let terminal := { terminal with world := terminal.world.writeSlot 0 0xdead }
  let projected := exceptionalInternalResult initial.world terminal
  unless !projected.success && projected.returnValue.isNone && projected.revertData == [] &&
      projected.interpretationError.isNone && projected.world.readSlot 0 == initial.world.readSlot 0 do
    throw (IO.userError "helper exception rollback or result metadata changed")
  match failedInternalOutcome projected with
  | .exceptional observed =>
      unless observed.executionContext.map (·.opcode.gas) == some 0 &&
          observed.executionContext.map (·.opcode.depth) == some 7 &&
          observed.bindings == terminal.bindings && observed.world.readSlot 0 == 0xdead do
        throw (IO.userError "helper lost actual terminal exception state")
  | _ => throw (IO.userError "helper exception became revert or refusal")
  let badContext := exceptionalInternalResult initial.world { terminal with executionContext := none }
  match failedInternalOutcome badContext with
  | .exceptional observed =>
      unless (exceptionalResult model initial.world observed).interpretationError ==
          some "exceptional exit requires actual opcode context" do
        throw (IO.userError "helper exception fabricated missing context")
  | _ => throw (IO.userError "helper raw exceptional carrier disappeared")
  let refused := { projected with interpretationError := some "instrument refusal" }
  match failedInternalOutcome refused with
  | .interpretationError message =>
      unless message == "instrument refusal" do throw (IO.userError "helper refusal changed")
  | _ => throw (IO.userError "helper refusal acquired EVM status")
  let copyFn : FunctionSpec :=
    { name := "copy", params := [], returnType := none,
      body := [.returndataCopy (.literal 0) (.literal 33) (.literal 0), .stop] }
  let copy := interpretInternalFunctionFuel model 4 copyFn initial.world []
  unless !copy.success && copy.exceptionalState.isNone do
    throw (IO.userError "missing-context helper run claimed exception")
  match failedInternalOutcome copy with
  | .interpretationError message =>
      unless message == "returndata copy exceptional exit requires actual opcode context" do
        throw (IO.userError "actual helper refusal message changed")
  | _ => throw (IO.userError "actual helper refusal became revert")
  let revertFn : FunctionSpec :=
    { name := "reverting", params := [], returnType := none,
      body := [.require (.literal 0) "helper failure", .stop] }
  let reverted := interpretInternalFunctionFuel model 4 revertFn initial.world []
  unless !reverted.success && reverted.exceptionalState.isNone && reverted.interpretationError.isNone do
    throw (IO.userError "ordinary helper revert metadata changed")
  match failedInternalOutcome reverted with
  | .revertWithData bytes =>
      unless bytes == Compiler.CompilationModel.Denote.errorStringBytes "helper failure" do
        throw (IO.userError "helper revert bytes changed")
  | _ => throw (IO.userError "ordinary helper revert became exception")
  let stopFn : FunctionSpec :=
    { name := "stopping", params := [], returnType := none, body := [.stop] }
  let stopped := interpretInternalFunctionFuel model 4 stopFn initial.world []
  unless stopped.success && stopped.exceptionalState.isNone && stopped.interpretationError.isNone do
    throw (IO.userError "ordinary helper success changed")
  IO.println "Source internal exception carrier, rollback, refusal and revert checks passed"

end SolidityImportSmoke.SourceInternalExceptionChecks

def main : IO Unit := SolidityImportSmoke.SourceInternalExceptionChecks.runChecks
