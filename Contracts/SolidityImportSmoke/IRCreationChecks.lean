import Compiler.Proofs.IRGeneration.IRCreationInterpreter

namespace SolidityImportSmoke.IRCreationChecks
open Compiler.Yul Compiler.Proofs.IRGeneration
open Compiler.Proofs.IRGeneration.IRCreationInterpreter
open Compiler.CompilationModel.DenoteMemory Verity.Core.Model

private def context (gas : Nat) : ExecutionContext :=
  { opcode := { gas, depth := 0, isStatic := false }, warm := fun query => query == 1 }
private def world : Verity.ContractState :=
  let code := MidnightInitcode.initcode ByteArray.empty
  let memory := Memory.empty.copyFrom (MidnightInitcode.codeByte code) 0 0 code.size
  { (Verity.defaultState.writeSlot 0 7).installPhysicalMemory memory with
    thisAddress := Verity.Core.Address.ofNat 1 }
private def runtime (gas : Nat) : Runtime :=
  ofBoundary (CreationIR.project world
    { IRState.initial 0 with vars := [("outer", 10)] } (some (context gas)))
private def creation : YulExpr :=
  .call "create2" [.lit 0, .lit 0, .lit MidnightInitcode.header.size, .lit 7]
private def expectError {α : Type} (result : Outcome α) (expected : String) : IO Unit :=
  match result with
  | .interpretationError message =>
      unless message == expected do throw (IO.userError message)
  | _ => throw (IO.userError "effectful IR refusal became an execution result")
private def expectValue {α : Type} : Outcome α → IO (α × Runtime)
  | .value value next => pure (value, next)
  | .interpretationError message => throw (IO.userError message)
  | _ => throw (IO.userError "unexpected effectful IR terminal outcome")

def runChecks : IO Unit := do
  let initial := runtime 1000000
  let empty : Runtime := { initial with state := { initial.state with byteMemory := Memory.empty } }
  let (_, stored) ← expectValue (execStmt 32 empty
    (.exprStmt (.call "mstore" [.lit 1, .lit 0x1234])))
  unless stored.state.byteMemory.size == 64 &&
      (stored.state.byteMemory.readByte 31).val == 0x12 &&
      (stored.state.byteMemory.readByte 32).val == 0x34 &&
      stored.state.memory 1 == 0x1234 && stored.creationContexts.length == 1 &&
      stored.state.storage (IRStorageSlot.ofNat 0) == empty.state.storage (IRStorageSlot.ofNat 0) &&
      stored.state.getVar "outer" == some 10 do
    throw (IO.userError "IR mstore lost unaligned bytes, size, frame or schedule")
  let (_, overlapped) ← expectValue (execStmt 32 stored
    (.exprStmt (.call "mstore8" [.lit (Compiler.Constants.evmModulus + 31), .lit 0x1ff])))
  unless (overlapped.state.byteMemory.readByte 31).val == 255 &&
      (overlapped.state.byteMemory.readByte 32).val == 0x34 &&
      overlapped.state.memory 1 == 0xff34 && overlapped.state.byteMemory.size == 64 &&
      overlapped.creationContexts.length == 1 do
    throw (IO.userError "IR mstore8 lost offset/byte normalization or overlapping word view")
  for value in [0, 1, 127, 128, 255, 256, 511, 512, Compiler.Constants.evmModulus - 1] do
    let (_, byteStored) ← expectValue (execStmt 32 empty
      (.exprStmt (.call "mstore8" [.lit 31, .lit value])))
    unless (byteStored.state.byteMemory.readByte 31).val == value % 256 &&
        byteStored.state.byteMemory.size == 32 && byteStored.creationContexts.length == 1 do
      throw (IO.userError s!"IR mstore8 boundary value diverged: {value}")
  expectError (execStmt 32 empty (.exprStmt (.call "mstore" [.lit 0])))
    "effectful IR mstore requires exactly two operands"
  expectError (execStmt 32 empty (.exprStmt (.call "mstore8" [])))
    "effectful IR mstore8 requires exactly two operands"
  expectError (execStmt 32 empty (.exprStmt (.call "mstore"
    [.ident "left_missing", .ident "right_missing"])))
    "unbound effectful IR variable: right_missing"
  let (_, next) ← expectValue (execStmt 64 initial (.let_ "created" creation))
  let address ← IO.ofExcept (match next.state.getVar "created" with
    | none => Except.error "CREATE2 destination missing"
    | some value => Except.ok value)
  let after ← IO.ofExcept (match next.state.creationWorld with
    | none => Except.error "CREATE2 canonical world missing"
    | some value => Except.ok value)
  unless address != 0 && (after.creationAccounts 1).nonce == 1 &&
      (after.creationAccounts address).nonce == 1 &&
      next.state.getVar "outer" == some 10 && next.creationContexts.isEmpty do
    throw (IO.userError "CREATE2 expression lost computed world, bindings or schedule consumption")
  match next.state.executionContext with
  | none => throw (IO.userError "CREATE2 expression lost actual post-opcode context")
  | some actual => unless actual.opcode.gas < 1000000 do
      throw (IO.userError "CREATE2 expression lost computed gas")
  expectError (evalExpr 64 next creation)
    "CREATE2 requires the next actual opcode-entry execution context"
  expectError (evalArgs 16 initial [.ident "left_missing", .ident "right_missing"])
    "unbound effectful IR variable: right_missing"
  expectError (evalExpr 32 initial (.call "add" [creation, .ident "right_missing"]))
    "unbound effectful IR variable: right_missing"
  expectError (execStmt 32 initial (.assign "missing" (.lit 9)))
    "assignment to unbound effectful IR variable: missing"
  expectError (execStmt 32 initial (.let_ "outer" (.lit 9)))
    "effectful IR variable already declared: outer"
  expectError (evalExpr 0 initial (.lit 1)) "effectful IR expression fuel exhausted"
  expectError (execStmt 32 initial (.exprStmt (.call "sstore" [.lit 0, .lit 9])))
    "unsupported effectful IR builtin or arity: sstore"
  let (_, blocked) ← expectValue (execStmt 64 initial (.block [
    .let_ "local" (.lit 19), .assign "outer" (.ident "local")]))
  unless blocked.state.getVar "local" == none && blocked.state.getVar "outer" == some 19 do
    throw (IO.userError "IR block leaked local or lost outer assignment")
  let (_, looped) ← expectValue (execStmt 256 initial (.for_
    [.let_ "i" (.lit 0)] (.call "lt" [.ident "i", .lit 3])
    [.assign "i" (.call "add" [.ident "i", .lit 1])]
    [.let_ "temporary" (.ident "i"), .assign "outer" (.ident "temporary")]))
  unless looped.state.getVar "outer" == some 2 && looped.state.getVar "i" == none &&
      looped.state.getVar "temporary" == none && looped.creationContexts.length == 1 do
    throw (IO.userError "IR loop leaked scope, lost assignment or consumed an unused creation context")
  let (_, branch) ← expectValue (execStmt 64 initial (.if_ (.lit 0)
    [.let_ "created" creation]))
  unless branch.creationContexts.length == 1 && branch.state.getVar "created" == none do
    throw (IO.userError "untaken IR branch consumed creation context")
  match execStmts 64 (runtime 0) [.let_ "created" creation, .let_ "after" (.lit 9)] with
  | .exceptional failed =>
      unless failed.state.getVar "created" == none && failed.state.getVar "after" == none &&
          failed.creationContexts.isEmpty do
        throw (IO.userError "IR exceptional outcome bound destination or continued execution")
      match failed.state.executionContext with
      | none => throw (IO.userError "IR exceptional outcome lost actual context")
      | some actual => unless actual.opcode.gas == 0 do
          throw (IO.userError "IR exceptional outcome retained gas")
  | _ => throw (IO.userError "IR exhausted creation became success or interpretation error")
  IO.println "generic IR creation, ordering, scope and refusal checks passed"
end SolidityImportSmoke.IRCreationChecks

def main : IO Unit := SolidityImportSmoke.IRCreationChecks.runChecks
