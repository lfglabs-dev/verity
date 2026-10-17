import Compiler.Proofs.IRGeneration.SourcePublicContextLaws

namespace SolidityImportSmoke.SourcePublicContextChecks
open Compiler.CompilationModel Compiler.Proofs.IRGeneration SourceSemantics

private def context : Verity.Core.Model.ExecutionContext :=
  { opcode := { gas := 73, depth := 9, isStatic := false }, warm := fun _ => false }
private def world : Verity.ContractState := Verity.defaultState.writeSlot 0 17
private def tx : IRTransaction := { sender := 23, functionSelector := 7, args := [] }
private def oracle (index : Nat) : ExternalCallOutcome :=
  { succeeded := true, returnValues := [100 + index] }
private def fields : List Field := [{ name := "value", ty := .uint256, slot := some 0 }]
private def probe : FunctionSpec :=
  { name := "probe", params := [], returnType := none,
    body := [.setStorage "value" (.literal 99),
      .returndataCopy (.literal 0) (.literal 33) (.literal 0), .stop] }
private def model : CompilationModel :=
  { name := "PublicContext", fields := fields, functions := [probe], constructor := none }

private def checkException (result : SourceContractResult) : IO Unit := do
  unless !result.success && result.returnValue == none && result.revertData == [] &&
      result.interpretationError.isNone && result.finalStorage 0 == 17 &&
      result.exceptionalContext.map (·.opcode.gas) == some 0 &&
      result.exceptionalContext.map (·.opcode.depth) == some 9 do
    throw (IO.userError "public entry lost actual context, exception kind or rollback")

def runChecks : IO Unit := do
  let ctor : ConstructorSpec := { params := [], body := probe.body }
  for result in [
      interpretFunction model probe tx world
        (executionContext := some context) (externalCallIndex := 3),
      interpretFunctionWithHelpers model 8 probe tx world
        (executionContext := some context) (externalCallIndex := 3),
      interpretContract model [7] tx world
        (executionContext := some context) (externalCallIndex := 3),
      interpretContractWithHelpers model [7] 8 tx world
        (executionContext := some context) (externalCallIndex := 3),
      interpretConstructor model ctor tx world
        (executionContext := some context) (externalCallIndex := 3),
      interpretConstructorWithHelpers model 8 ctor tx world
        (executionContext := some context) (externalCallIndex := 3)] do
    checkException result
  -- Omission still means missing context, never a fabricated default frame.
  for result in [interpretFunction model probe tx world,
      interpretFunctionWithHelpers model 8 probe tx world,
      interpretContract model [7] tx world,
      interpretContractWithHelpers model [7] 8 tx world,
      interpretConstructor model ctor tx world,
      interpretConstructorWithHelpers model 8 ctor tx world] do
    unless !result.success && result.exceptionalContext.isNone &&
        result.interpretationError == some "returndata copy exceptional exit requires actual opcode context" &&
        result.finalStorage 0 == 17 do
      throw (IO.userError "omitted public context fabricated execution or lost rollback")
  let receiptProbe : FunctionSpec := { probe with body :=
    [.externalCallBind ["receipt"] "oracle" [],
     .require (.eq (.localVar "receipt") (.literal 103)) "wrong external cursor",
     .stop] }
  let receiptModel := { model with functions := [receiptProbe] }
  let receiptCtor : ConstructorSpec := { params := [], body := receiptProbe.body }
  for result in [
      interpretFunction receiptModel receiptProbe tx world oracle
        (executionContext := some context) (externalCallIndex := 3),
      interpretFunctionWithHelpers receiptModel 8 receiptProbe tx world oracle
        (executionContext := some context) (externalCallIndex := 3),
      interpretContract receiptModel [7] tx world oracle
        (executionContext := some context) (externalCallIndex := 3),
      interpretContractWithHelpers receiptModel [7] 8 tx world oracle
        (executionContext := some context) (externalCallIndex := 3),
      interpretConstructor receiptModel receiptCtor tx world oracle
        (executionContext := some context) (externalCallIndex := 3),
      interpretConstructorWithHelpers receiptModel 8 receiptCtor tx world oracle
        (executionContext := some context) (externalCallIndex := 3)] do
    unless result.success && result.interpretationError.isNone && result.exceptionalContext.isNone do
      throw (IO.userError "public entry reset supplied external oracle or cursor")
  IO.println "Source six public entry context, cursor, refusal and rollback checks passed"
end SolidityImportSmoke.SourcePublicContextChecks

def main : IO Unit := SolidityImportSmoke.SourcePublicContextChecks.runChecks
