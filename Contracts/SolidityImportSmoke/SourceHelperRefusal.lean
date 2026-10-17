import Compiler.Proofs.IRGeneration.SourceSemantics

namespace SolidityImportSmoke.SourceHelperRefusal
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration.SourceSemantics

private def helper : FunctionSpec :=
  { name := "helper", params := [], returnType := none, isInternal := true,
    body := [.create2 "created" (.literal 0) (.literal 0) (.literal 0)] }
private def model : CompilationModel :=
  { name := "HelperRefusal", fields := [], constructor := none, functions := [helper] }
private def expected := "CREATE2 requires an actual opcode-entry execution context"

private def expectRefusal (result : StmtResult) : IO Unit := do
  match result with
  | .interpretationError message => unless message == expected do throw (IO.userError message)
  | _ => throw (IO.userError "source helper refusal became EVM outcome")

def runChecks : IO Unit := do
  let state : RuntimeState := { world := Verity.defaultState, bindings := [] }
  expectRefusal (execStmtWithHelpers model [] 3 state (.internalCall "helper" []))
  expectRefusal (execStmtWithHelpers model [] 3 state (.internalCallAssign ["result"] "helper" []))
  expectRefusal (execStmtListWithHelpers model [] 3 state
    [.internalCall "helper" [], .stop])
  expectRefusal (failedInternalOutcome
    { interpretationError := some expected, success := false,
      returnValue := none, world := Verity.defaultState })
  match failedInternalOutcome
    { success := false, returnValue := none, world := Verity.defaultState } with
  | .revertWithData data => unless data.isEmpty do throw (IO.userError "empty helper revert gained bytes")
  | _ => throw (IO.userError "ordinary helper revert became refusal")
  IO.println "Source helper statement refusals preserved"
end SolidityImportSmoke.SourceHelperRefusal

def main : IO Unit := SolidityImportSmoke.SourceHelperRefusal.runChecks
