import Compiler.Proofs.IRGeneration.DenoteFunctionAgreement

namespace SolidityImportSmoke.DenotePublicExceptionChecks
open Compiler.CompilationModel
open Denote

private def oracle : DenoteOracle :=
  { mappingSlot := fun _ _ => 0, keccakMemorySlice := fun _ _ _ => 0 }

private def model : CompilationModel :=
  { name := "DenotePublicException", fields := [], functions := [], constructor := none }
private def context : Verity.Core.Model.ExecutionContext :=
  { opcode := { gas := 19, depth := 2, isStatic := false }, warm := fun _ => false }
private def initial : DenoteState :=
  { world := { Verity.defaultState with returndata := [0x1234] }
    bindings := [], executionContext := some context }

private def checkRollback (result : DenoteResult) : IO Unit := do
  unless !result.success && result.returnValue == none && result.revertData == [] &&
      result.events == encodeEvents initial.world.events do
    throw (IO.userError "exception/refusal rollback or return metadata changed")
  for slot in [0, 1, 7, 32] do
    unless result.finalStorage slot == encodeStorage oracle model initial.world slot do
      throw (IO.userError "exception/refusal storage did not roll back")

def runChecks : IO Unit := do
  let terminal ← match execReturndataCopy initial 0 33 0 with
    | .exceptional state => pure state
    | _ => throw (IO.userError "actual bounds failure did not produce exception")
  let terminal := { terminal with world := terminal.world.writeSlot 0 0xdead }
  let result := exceptionalResult oracle model initial.world terminal
  checkRollback result
  unless result.interpretationError == none &&
      result.exceptionalContext.map (·.opcode.gas) == some 0 &&
      result.exceptionalContext.map (·.opcode.depth) == some 2 do
    throw (IO.userError "actual public exception context erased")
  let projected := Compiler.Proofs.IRGeneration.DenoteAgreement.toSourceResult result
  unless projected.exceptionalContext.map (·.opcode.gas) == some 0 &&
      projected.exceptionalContext.map (·.opcode.depth) == some 2 &&
      projected.finalStorage 0 == encodeStorage oracle model initial.world 0 do
    throw (IO.userError "Source projection erased exception context or rollback")
  for (state, message) in
      [({ terminal with executionContext := none },
        "exceptional exit requires actual opcode context"),
       ({ terminal with executionContext := some context },
        "exceptional exit requires exhausted opcode gas")] do
    let refusal := exceptionalResult oracle model initial.world state
    checkRollback refusal
    unless refusal.exceptionalContext.isNone && refusal.interpretationError == some message do
      throw (IO.userError "invalid exception context became certified EVM outcome")
  let fn : FunctionSpec :=
    { name := "probe", params := [], returnType := none,
      body := [.returndataCopy (.literal 0) (.literal 33) (.literal 0), .stop] }
  let tx : DenoteTransaction := { sender := 0, functionSelector := 0, args := [] }
  for publicResult in [denoteFunction oracle model fn tx initial.world] do
    checkRollback publicResult
    unless publicResult.exceptionalContext.isNone && publicResult.interpretationError ==
        some "returndata copy exceptional exit requires actual opcode context" do
      throw (IO.userError "public function missing context became EVM revert")
  IO.println "Denote public exception context, refusal and rollback checks passed"

end SolidityImportSmoke.DenotePublicExceptionChecks

def main : IO Unit := SolidityImportSmoke.DenotePublicExceptionChecks.runChecks
