import Compiler.Proofs.IRGeneration.IRInterpreter

namespace SolidityImportSmoke.CanonicalIRReturndataChecks
open Compiler.Yul Compiler.Proofs.IRGeneration

private def copy : YulStmt :=
  .exprStmt (.call "returndatacopy" [.lit 1, .lit 33, .lit 0])

example (fuel : Nat) (state : IRState)
    (context : Verity.Core.Model.ExecutionContext)
    (empty : state.returndata = []) (actual : state.executionContext = some context) :
    execIRStmt (fuel + 1) state copy = .exceptional
      { state with executionContext := some { context with opcode := { context.opcode with gas := 0 } } } := by
  simp [copy, execIRStmt, evalIRExpr, empty, actual, Compiler.Constants.evmModulus]

example (fuel : Nat) (state : IRState)
    (empty : state.returndata = []) (missing : state.executionContext = none) :
    execIRStmt (fuel + 1) state copy = .interpretationError
      "returndata copy exceptional exit requires actual opcode context" := by
  simp [copy, execIRStmt, evalIRExpr, empty, missing, Compiler.Constants.evmModulus]

example (fuel : Nat) (state : IRState) (rest : List YulStmt) (message : String)
    (failed : execIRStmt fuel state copy = .interpretationError message) :
    execIRStmts (fuel + 1) state (copy :: rest) = .interpretationError message := by
  simp only [execIRStmts, failed]

example (fuel : Nat) (state next : IRState) (rest : List YulStmt)
    (failed : execIRStmt fuel state copy = .exceptional next) :
    execIRStmts (fuel + 1) state (copy :: rest) = .exceptional next := by
  simp only [execIRStmts, failed]

example (contract : Compiler.IRContract) (fuel : Nat) (state next : IRState)
    (rest : List YulStmt)
    (failed : execIRStmtWithInternals contract fuel state copy = .exceptional next) :
    execIRStmtsWithInternals contract (fuel + 1) state (copy :: rest) = .exceptional next := by
  simp only [execIRStmtsWithInternals, failed]

example (fn : Compiler.IRFunction) (args : List Nat) (state next : IRState)
    (failed : execIRStmts (sizeOf fn.body + 1)
      (fn.params.zip args |>.foldl (fun s (p, v) => s.setVar p.name v) state)
      fn.body = .exceptional next) :
    (execIRFunction fn args state).exceptionalContext = next.executionContext ∧
    (execIRFunction fn args state).revertData = none ∧
    (execIRFunction fn args state).interpretationError = none ∧
    (execIRFunction fn args state).success = false ∧
    (execIRFunction fn args state).finalStorage = state.storage ∧
    (execIRFunction fn args state).events = state.events := by
  simp only [execIRFunction, failed]
  trivial

example (fn : Compiler.IRFunction) (args : List Nat) (state : IRState) (message : String)
    (failed : execIRStmts (sizeOf fn.body + 1)
      (fn.params.zip args |>.foldl (fun s (p, v) => s.setVar p.name v) state)
      fn.body = .interpretationError message) :
    (execIRFunction fn args state).interpretationError = some message ∧
    (execIRFunction fn args state).exceptionalContext = none ∧
    (execIRFunction fn args state).revertData = none ∧
    (execIRFunction fn args state).success = false ∧
    (execIRFunction fn args state).finalStorage = state.storage ∧
    (execIRFunction fn args state).events = state.events := by
  simp only [execIRFunction, failed]
  trivial

example (contract : Compiler.IRContract) (fuel : Nat) (caller final : IRState)
    (helper : IRInternalFunctionDef) (args : List Nat)
    (arity : helper.params.length = args.length)
    (failed : execIRStmtsWithInternals contract fuel
      (prepareInternalCalleeState caller helper args) helper.body = .revert final) :
    execIRInternalFunctionWithInternals contract (fuel + 1) caller helper args =
      .revert (restoreCallerVars caller final) := by
  rw [execIRInternalFunctionWithInternals_succ_of_params_match contract fuel caller helper args arity]
  simp only [failed]

private def initial : IRState :=
  { ((IRState.initial 17).writePhysicalMemoryValue 0 0xabcdef) with
    returndata := [0x1234]
    vars := [("outer", 7)]
    executionContext := some
      { opcode := { gas := 999, depth := 2, isStatic := false }
        warm := fun _ => false } }

private def contract : Compiler.IRContract :=
  { name := "CanonicalCopy", deploy := [], functions := [], usesMapping := false
    internalFunctions := [.funcDef "capture" [] []
      [.exprStmt (.call "mstore" [.lit 0, .lit 0x9876]),
        .exprStmt (.call "revert" [.lit 30, .lit 2])]] }

private def checkCopy (result : IRExecResult) (source : Nat) : IO Unit := do
  match result with
  | .continue next =>
      unless source == 30 && (next.byteMemory.readByte 1).val == 0x12 &&
          (next.byteMemory.readByte 2).val == 0x34 && next.getVar "outer" == some 7 &&
          next.returndata == [0x1234] && next.executionContext.map (·.opcode.gas) == some 999 do
        throw (IO.userError "canonical IR copy bytes/frame mismatch")
  | .exceptional next =>
      unless source == 31 && next.executionContext.map (·.opcode.gas) == some 0 &&
          next.executionContext.map (·.opcode.depth) == some 2 && next.observedRevert == none &&
          next.getVar "outer" == some 7 && next.byteMemory.size == initial.byteMemory.size &&
          (List.range initial.byteMemory.size).all (fun offset =>
            next.byteMemory.readByte offset == initial.byteMemory.readByte offset) &&
          next.returndata == initial.returndata do
        throw (IO.userError "canonical IR exception context/frame mismatch")
  | _ => throw (IO.userError "canonical IR copy became revert/refusal")

private def externalResult : IRExecResultWithInternals → IRExecResult
  | .continue next => .continue next
  | .return value next => .return value next
  | .stop next => .stop next
  | .revert next => .revert next
  | .exceptional next => .exceptional next
  | .interpretationError message => .interpretationError message
  | .leave _ => .interpretationError "unexpected external leave"

def runChecks : IO Unit := do
  for source in [30, 31] do
    let stmt := YulStmt.exprStmt (.call "returndatacopy" [.lit 1, .lit source, .lit 2])
    for body in [[stmt], [.block [stmt]], [.if_ (.lit 1) [stmt]]] do
      checkCopy (execIRStmts 128 initial body) source
      checkCopy (externalResult (execIRStmtsWithInternals contract 128 initial body)) source
  checkCopy (execIRStmt 16 initial (.exprStmt (.call "returndatacopy"
    [.lit (Compiler.Constants.evmModulus + 1), .lit (Compiler.Constants.evmModulus + 30),
      .lit (Compiler.Constants.evmModulus + 2)]))) 30
  checkCopy (externalResult (execIRStmtWithInternals contract 16 initial
    (.exprStmt (.call "returndatacopy"
      [.lit (Compiler.Constants.evmModulus + 1), .lit (Compiler.Constants.evmModulus + 30),
        .lit (Compiler.Constants.evmModulus + 2)])))) 30
  for source in [32, 33] do
    match execIRStmt 16 initial (.exprStmt (.call "returndatacopy" [.lit 0, .lit source, .lit 0])) with
    | .continue _ => unless source == 32 do throw (IO.userError "zero size ignored bounds")
    | .exceptional next => unless source == 33 && next.executionContext.map (·.opcode.gas) == some 0 do
        throw (IO.userError "zero size edge lost gas exception")
    | _ => throw (IO.userError "zero size edge became revert/refusal")
  let missing := { initial with executionContext := none }
  let tail := [copy, .assign "outer" (.lit 99)]
  for result in [execIRStmts 128 missing tail,
      externalResult (execIRStmtsWithInternals contract 128 missing tail)] do
    match result with
    | .interpretationError message =>
        unless message == "returndata copy exceptional exit requires actual opcode context" do
          throw (IO.userError "canonical IR refusal diagnostic mismatch")
    | _ => throw (IO.userError "canonical IR refusal became EVM outcome")
  match execIRStmtsWithInternals contract 128 initial
      [.exprStmt (.call "capture" []), .assign "outer" (.lit 99)] with
  | .revert next =>
      unless next.revertBytes == some [0x98, 0x76] && next.getVar "outer" == some 7 &&
          next.storage (IRStorageSlot.ofNat 0) == initial.storage (IRStorageSlot.ofNat 0) do
        throw (IO.userError "helper REVERT lost callee bytes/frame or continued tail")
  | _ => throw (IO.userError "helper byteful REVERT became another result")
  IO.println "canonical IR copy bytes, context, refusal, suffix and helper capture checks passed"

end SolidityImportSmoke.CanonicalIRReturndataChecks
