import Compiler.Proofs.IRGeneration.SourceSemantics

namespace SolidityImportSmoke.SourcePublicExceptionChecks
open Compiler.CompilationModel Compiler.Proofs.IRGeneration
open SourceSemantics

example (spec : CompilationModel) (initialWorld : Verity.ContractState)
    (terminal : RuntimeState) (context : Verity.Core.Model.ExecutionContext)
    (hcontext : terminal.executionContext = some context)
    (hgas : context.opcode.gas = 0) :
    exceptionalResult spec initialWorld terminal =
      { revertedResult spec initialWorld with exceptionalContext := some context } :=
  exceptionalResult_of_exhausted_context spec initialWorld terminal context hcontext hgas

example (spec : CompilationModel) (initialWorld : Verity.ContractState)
    (terminal : RuntimeState) :
    (exceptionalResult spec initialWorld terminal).finalStorage = encodeStorage spec initialWorld ∧
      (exceptionalResult spec initialWorld terminal).events = encodeEvents initialWorld.events ∧
      (exceptionalResult spec initialWorld terminal).success = false ∧
      (exceptionalResult spec initialWorld terminal).revertData = [] :=
  exceptionalResult_rollback spec initialWorld terminal

private def model : CompilationModel :=
  { name := "SourcePublicException", fields := [], functions := [], constructor := none }
private def context : Verity.Core.Model.ExecutionContext :=
  { opcode := { gas := 19, depth := 2, isStatic := false }, warm := fun _ => false }
private def initial : RuntimeState :=
  { world := { Verity.defaultState with returndata := [0x1234] }
    bindings := [], executionContext := some context }

private def checkRollback (result : SourceContractResult) : IO Unit := do
  unless !result.success && result.returnValue == none && result.revertData == [] &&
      result.events == encodeEvents initial.world.events do
    throw (IO.userError "exception/refusal rollback or return metadata changed")
  for slot in [0, 1, 7, 32] do
    unless result.finalStorage slot == encodeStorage model initial.world slot do
      throw (IO.userError "exception/refusal storage did not roll back")

def runChecks : IO Unit := do
  let terminal ← match execReturndataCopy initial 0 33 0 with
    | .exceptional state => pure state
    | _ => throw (IO.userError "actual bounds failure did not produce exception")
  let terminal := { terminal with world := terminal.world.writeSlot 0 0xdead }
  let result := exceptionalResult model initial.world terminal
  checkRollback result
  unless result.interpretationError == none &&
      result.exceptionalContext.map (·.opcode.gas) == some 0 &&
      result.exceptionalContext.map (·.opcode.depth) == some 2 do
    throw (IO.userError "actual public exception context erased")
  for (state, message) in
      [({ terminal with executionContext := none },
        "exceptional exit requires actual opcode context"),
       ({ terminal with executionContext := some context },
        "exceptional exit requires exhausted opcode gas")] do
    let refusal := exceptionalResult model initial.world state
    checkRollback refusal
    unless refusal.exceptionalContext.isNone && refusal.interpretationError == some message do
      throw (IO.userError "invalid exception context became certified EVM outcome")
  let fn : FunctionSpec :=
    { name := "probe", params := [], returnType := none,
      body := [.returndataCopy (.literal 0) (.literal 33) (.literal 0), .stop] }
  let tx : IRTransaction := { sender := 0, functionSelector := 0, args := [] }
  for publicResult in [interpretFunction model fn tx initial.world,
      interpretFunctionWithHelpers model 4 fn tx initial.world] do
    checkRollback publicResult
    unless publicResult.exceptionalContext.isNone && publicResult.interpretationError ==
        some "returndata copy exceptional exit requires actual opcode context" do
      throw (IO.userError "public function missing context became EVM revert")
  IO.println "Source public exception context, refusal and rollback checks passed"

end SolidityImportSmoke.SourcePublicExceptionChecks

def main : IO Unit := SolidityImportSmoke.SourcePublicExceptionChecks.runChecks
