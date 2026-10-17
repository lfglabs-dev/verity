import Verity.Core.Model.DenoteFunctionCalls

namespace SolidityImportSmoke.CallRefusal
open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.DenoteFunctionCalls
open Compiler.CompilationModel.DenoteExternalCalls
open Verity.MultiContract

private def oracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
private def env : CallEnv :=
  { oracle, adversary := identityAdversary, resolve := fun _ => none }
private def creation : Stmt := .create2 "created" (.literal 0) (.literal 0) (.literal 0)
private def refusal : String := "CREATE2 requires an actual opcode-entry execution context"
private def fn (body : List Stmt) : FunctionSpec :=
  { name := "probe", params := [], returnType := none, body }
private def model : CompilationModel :=
  { name := "CallRefusal", fields := [{ name := "stored", ty := .uint256 }],
    constructor := none, functions := [] }
private def before : MultiWorld :=
  { accounts := [
    { address := 1, state := { Verity.defaultState with selfBalance := 10 } },
    { address := 2, state := (Verity.defaultState.writeSlot 0 7) }] }
private def site : CallSite :=
  { siteId := 0, kind := .call, target := 2, value := 1, calldata := [], gas := 100 }
private def compiled (body : List Stmt) : CompiledCall :=
  { env, spec := model, fn := fn body, selector := 0, caller := 1, callee := 2, site }
private def expectError {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error message => unless message == refusal do throw (IO.userError message)
  | .ok _ => throw (IO.userError "interpreter refusal became an EVM result")

def runChecks : IO Unit := do
  let state : DenoteState := { world := Verity.defaultState, bindings := [] }
  match execStmtListWithCalls env [] state [creation, .stop] with
  | .interpretationError message =>
      unless message == refusal do throw (IO.userError message)
  | _ => throw (IO.userError "statement list swallowed refusal")
  for stmt in [Stmt.ite (.literal 1) [creation] [],
      Stmt.forEach "i" (.literal 1) [creation],
      Stmt.forEachSetBit "i" (.literal 1) [creation]] do
    match execStmtWithCalls env [] state stmt with
    | .interpretationError message =>
        unless message == refusal do throw (IO.userError message)
    | _ => throw (IO.userError "nested control swallowed refusal")
  expectError (finishFunctionExecution Verity.defaultState (.interpretationError refusal))
  let initial := Verity.defaultState.writeSlot 0 7
  let dirty := (initial.writeSlot 0 99).writePhysicalMemoryValue 0 123
  let exceptional : DenoteState := { world := dirty, bindings := [] }
  match finishFunctionExecution initial (.exceptional exceptional) with
  | .error message =>
      unless message == "Denote exceptional exit requires an actual execution context" do
        throw (IO.userError message)
  | .ok _ => throw (IO.userError "exceptional outcome invented a context")
  let context : Verity.Core.Model.ExecutionContext :=
    { opcode := { gas := 1, depth := 0, isStatic := false }, warm := fun _ => false }
  match finishFunctionExecution initial (.exceptional
      { exceptional with executionContext := some context }) with
  | .error message =>
      unless message == "Denote exceptional exit has nonzero terminal gas" do
        throw (IO.userError message)
  | .ok _ => throw (IO.userError "exceptional outcome accepted nonzero gas")
  let exhausted ← IO.ofExcept (finishFunctionExecution initial (.exceptional
    { exceptional with executionContext := some { context with opcode := { context.opcode with gas := 0 } } }))
  match exhausted.result with
  | .failure [] => pure ()
  | _ => throw (IO.userError "exhausted exception was not empty EVM failure")
  unless exhausted.revertBytes == some [] && exhausted.world.readSlot 0 == 7 &&
      (exhausted.world.memory 0).val == 0 do
    throw (IO.userError "exhausted exception leaked output, storage or memory")
  expectError (executeFunctionWithCalls env model (fn [creation])
    { sender := 1, functionSelector := 0, args := [] } Verity.defaultState)
  let projected := denoteFunctionWithCalls env model (fn [creation])
    { sender := 1, functionSelector := 0, args := [] } Verity.defaultState
  unless projected.interpretationError == some refusal do
    throw (IO.userError "public denotation lost interpretation error")
  let frame ← IO.ofExcept (match callEntry before 1 2 site with
    | some frame => Except.ok frame
    | none => Except.error "invalid test frame")
  expectError (runFunctionInFrame env model (fn [creation]) 0 frame)
  expectError (callFunction env model (fn [creation]) 0 before 1 2 site)
  let success := compiled [.setStorage "stored" (.literal 99), .stop]
  let failed := compiled [creation]
  let committed :=  denoteTransaction before [success]
  unless (lookup committed.world 2).readSlot 0 == 99 &&
      (lookup committed.world 1).selfBalance == 9 &&
      (lookup committed.world 2).selfBalance == 1 do
    throw (IO.userError "successful prefix failed to commit storage/value")
  let rolled := denoteTransaction before [success, failed]
  match rolled.control with
  | .interpretationError 1 message =>
      unless message == refusal do throw (IO.userError message)
  | _ => throw (IO.userError "transaction converted refusal to call failure")
  unless (lookup rolled.world 2).readSlot 0 == 7 &&
      (lookup rolled.world 1).selfBalance == 10 &&
      (lookup rolled.world 2).selfBalance == 0 &&
      (lookup rolled.world 1).calls == [] && rolled.calls.length == 1 do
    throw (IO.userError "interpretation error did not roll back prior commits or added an EVM row")
  let reverted := denoteTransaction before [compiled [.require (.literal 0) "ordinary revert"]]
  match reverted.control with
  | .callFailed 0 (.revert _) => pure ()
  | _ => throw (IO.userError "ordinary revert was reclassified as interpreter error")
  unless reverted.calls.length == 1 do throw (IO.userError "ordinary revert lost its observation")
  IO.println "call-aware refusal propagation and atomic rollback passed"
end SolidityImportSmoke.CallRefusal

def main : IO Unit := SolidityImportSmoke.CallRefusal.runChecks
