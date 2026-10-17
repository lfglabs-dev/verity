import Compiler.Proofs.IRGeneration.DenoteFunctionAgreement
import Compiler.Proofs.IRGeneration.SourcePublicRevertLaws

namespace SolidityImportSmoke.PublicRevertChecks
open Compiler.CompilationModel Compiler.Proofs.IRGeneration SourceSemantics

def runChecks : IO Unit := do
  let fn : FunctionSpec := { name := "probe", params := [], returnType := none, body := [.setStorage "count" (.literal 99), .require (.literal 0) "denied"] }
  let model : CompilationModel := { name := "PublicRevert", constructor := none, fields := [{ name := "count", ty := .uint256, slot := some 3 }], functions := [fn] }
  let initial := Verity.defaultState.writeSlot 3 19
  let tx : IRTransaction := { sender := 7, functionSelector := 0, args := [] }
  let denoted := Denote.denoteFunction DenoteAgreement.sourceOracle model fn
    (DenoteAgreement.ofIRTransaction tx) initial
  let source := SourceSemantics.interpretFunction model fn tx initial
  unless !denoted.success && !source.success && denoted.interpretationError == none &&
      source.interpretationError == none && denoted.revertData == Denote.errorStringBytes "denied" &&
      source.revertData == denoted.revertData && denoted.finalStorage 3 == 19 &&
      source.finalStorage 3 == 19 && denoted.events == [] && source.events == [] do
    throw (IO.userError "public entry revert lost bytes or failed storage/event rollback")
  IO.println "public entry revert bytes and rollback passed"
end SolidityImportSmoke.PublicRevertChecks

def main : IO Unit := SolidityImportSmoke.PublicRevertChecks.runChecks
