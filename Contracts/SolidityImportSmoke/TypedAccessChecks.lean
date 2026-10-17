import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Access

namespace SolidityImportSmoke.TypedAccessChecks
open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport

solidity_import imported from "Contracts/SolidityImportSmoke" entry "TypedAccessFixture.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract TypedAccessFixture
  function read()
  function noop()
  function fail()

private def oracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
private def creation : FunctionSpec :=
  { name := "creation", params := [], returnType := none,
    body := [.create2 "created" (.literal 0) (.literal 0) (.literal 0)] }
private def creationModel : CompilationModel :=
  { name := "CreationRefusal", fields := [], constructor := none, functions := [creation] }

def runChecks : IO Unit := do
  let world := Verity.defaultState
  match imported.read oracle world with
  | .ok (some result) => unless result.val == 45 do throw (IO.userError "typed read value differs")
  | _ => throw (IO.userError "typed read lost successful return")
  match imported.noop oracle world with
  | .ok (some ()) => pure ()
  | _ => throw (IO.userError "typed void success became failure")
  match imported.fail oracle world with
  | .ok none => pure ()
  | _ => throw (IO.userError "typed ordinary revert became interpretation refusal")
  match runFunction oracle creationModel "creation" world [] with
  | .error message => unless message == "CREATE2 requires an actual opcode-entry execution context" do
      throw (IO.userError message)
  | .ok _ => throw (IO.userError "typed access converted interpretation refusal to EVM result")
  match runFunction oracle creationModel "missing" world [] with
  | .error message => unless message == "unknown imported function: missing" do throw (IO.userError message)
  | .ok _ => throw (IO.userError "typed access accepted missing function")
  match finishAccessOutcome (.interpretationError "precise refusal") with
  | .error message => unless message == "precise refusal" do throw (IO.userError message)
  | .ok _ => throw (IO.userError "typed outcome swallowed refusal")
  let state : DenoteState := { world, bindings := [] }
  match finishAccessOutcome (.continue state) with
  | .ok (some []) => pure ()
  | _ => throw (IO.userError "typed fallthrough without words became failure")
  match finishAccessOutcome (.stop state) with
  | .ok (some []) => pure ()
  | _ => throw (IO.userError "typed stop without words became failure")
  match finishAccessOutcome (.exceptional state) with
  | .error message => unless message == "Denote exceptional exit requires an actual execution context" do
      throw (IO.userError message)
  | .ok _ => throw (IO.userError "typed outcome invented context")
  let context : Verity.Core.Model.ExecutionContext :=
    { opcode := { gas := 1, depth := 0, isStatic := false }, warm := fun _ => false }
  match finishAccessOutcome (.exceptional { state with executionContext := some context }) with
  | .error message => unless message == "Denote exceptional exit has nonzero terminal gas" do
      throw (IO.userError message)
  | .ok _ => throw (IO.userError "typed outcome accepted nonzero exceptional gas")
  match finishAccessOutcome (.exceptional
    { state with executionContext := some { context with opcode := { context.opcode with gas := 0 } } }) with
  | .ok none => pure ()
  | _ => throw (IO.userError "typed exhausted exception was misclassified")
  IO.println "typed access precise refusals and generated wrappers passed"
end SolidityImportSmoke.TypedAccessChecks

def main : IO Unit := SolidityImportSmoke.TypedAccessChecks.runChecks
