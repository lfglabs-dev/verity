import Compiler.Proofs.IRGeneration.IRCreationInterpreter
import Compiler.Proofs.IRGeneration.PhysicalReturndataBytes

namespace SolidityImportSmoke.EffectfulReturndataChecks
open Compiler.Yul Compiler.Proofs.IRGeneration IRCreationInterpreter
open Verity.Core.Model

example (fuel : Nat) (runtime next : Runtime) (stmt : YulStmt)
    (rest : List YulStmt) (data : List UInt8)
    (failed : execStmt fuel runtime stmt = .revert data next) :
    execStmts (fuel + 1) runtime (stmt :: rest) = .revert data next :=
  execStmts_revert fuel runtime next stmt rest data failed

example (runtime : Runtime) (offset size : Nat) :
    ∃ data next, invokeRevert runtime [offset, size] = .revert data next ∧
      next.state.revertBytes = some data := invokeRevert_payload runtime offset size

private def initial : Runtime :=
  { state :=
      { ((IRState.initial 17).writePhysicalMemoryValue 0 0xabcdef) with
        returndata := [0x1234]
        vars := [("outer", 7)]
        executionContext := some
          { opcode := { gas := 999, depth := 2, isStatic := false }
            warm := fun _ => false } }
    creationContexts := [] }

private def expectError {α : Type} (outcome : Outcome α) (expected : String) : IO Unit :=
  match outcome with
  | .interpretationError message => unless message == expected do throw (IO.userError message)
  | _ => throw (IO.userError "returndata refusal became an EVM outcome")

def runChecks : IO Unit := do
  let runtime := initial
  match invokeReturndatacopy runtime [1, 30, 2] with
  | .value _ copied =>
      unless (copied.state.byteMemory.readByte 1).val == 0x12 &&
          (copied.state.byteMemory.readByte 2).val == 0x34 &&
          (copied.state.byteMemory.readByte 31).val == 0xef &&
          copied.state.getVar "outer" == some 7 && copied.state.returndata == [0x1234] do
        throw (IO.userError "returndata copy lost bytes or frame")
      match invokeRevert copied [1, 2] with
      | .revert data final =>
          unless data == [0x12, 0x34] && final.state.revertBytes == some data &&
              final.state.storage (IRStorageSlot.ofNat 0) == runtime.state.storage (IRStorageSlot.ofNat 0) do
            throw (IO.userError "actual revert bytes or storage frame were lost")
      | _ => throw (IO.userError "actual revert became refusal or exception")
  | _ => throw (IO.userError "valid unaligned returndata copy failed")
  for source in [32, 33] do
    match invokeReturndatacopy runtime [0, source, 0] with
    | .value _ next =>
        unless source == 32 && next.state.observedRevert == none do
          throw (IO.userError "zero-sized copy ignored out-of-bounds source")
    | .exceptional next =>
        unless source == 33 && next.state.executionContext.map (·.opcode.gas) == some 0 &&
            next.state.observedRevert == none && next.state.getVar "outer" == some 7 &&
            next.state.byteMemory.size == runtime.state.byteMemory.size &&
            (List.range runtime.state.byteMemory.size).all (fun offset =>
              next.state.byteMemory.readByte offset == runtime.state.byteMemory.readByte offset) do
          throw (IO.userError "exceptional copy fabricated revert bytes or lost frame/gas")
    | _ => throw (IO.userError "copy bounds became an interpreter refusal with context present")
  expectError (invokeReturndatacopy { runtime with state := { runtime.state with executionContext := none } }
    [0, 33, 0]) "effectful IR returndata copy exceptional exit requires actual opcode context"
  expectError (invokeReturndatacopy runtime [0, 0])
    "effectful IR returndatacopy requires exactly three operands"
  expectError (invokeRevert runtime [0]) "effectful IR revert requires exactly two operands"
  expectError (execStmt 16 runtime (.exprStmt (.call "revert" [.ident "left", .ident "right"])))
    "unbound effectful IR variable: right"
  let sequence : List YulStmt :=
    [.exprStmt (.call "returndatacopy" [.lit 1, .lit 30, .lit 2]),
      .exprStmt (.call "revert" [.lit 1, .lit 2]), .assign "outer" (.lit 99)]
  for variant in [sequence, [.block sequence], [.if_ (.lit 1) sequence]] do
    match execStmts 128 runtime variant with
    | .revert data next =>
        unless data == [0x12, 0x34] && next.state.revertBytes == some data &&
            next.state.getVar "outer" == some 7 do
          throw (IO.userError "byteful revert transport lost payload or continued suffix")
    | _ => throw (IO.userError "byteful revert wrapper changed terminal outcome")
  match execStmts 64 runtime [.exprStmt (.call "revert" [.lit 0, .lit 0]),
      .assign "outer" (.lit 99)] with
  | .revert data next =>
      unless data.isEmpty && next.state.revertBytes == some [] && next.state.getVar "outer" == some 7 do
        throw (IO.userError "empty observed revert lost payload or continued suffix")
  | _ => throw (IO.userError "empty observed revert lost its distinct result kind")
  match execStmts 64 runtime [.exprStmt (.call "returndatacopy" [.lit 0, .lit 31, .lit 2]),
      .assign "outer" (.lit 99)] with
  | .exceptional next =>
      unless next.state.getVar "outer" == some 7 && next.state.executionContext.map (·.opcode.gas) == some 0 do
        throw (IO.userError "exceptional copy continued suffix or retained gas")
  | _ => throw (IO.userError "exceptional copy was coerced to ordinary revert")
  match invokeReturndatacopy runtime [Compiler.Constants.evmModulus + 1,
      Compiler.Constants.evmModulus + 30, Compiler.Constants.evmModulus + 2] with
  | .value _ next =>
      unless (next.state.byteMemory.readByte 1).val == 0x12 &&
          (next.state.byteMemory.readByte 2).val == 0x34 do
        throw (IO.userError "copy did not normalize actual EVM operands")
  | _ => throw (IO.userError "normalized copy operands failed")
  IO.println "effectful returndata bytes, exceptional gas, frame and terminal checks passed"

end SolidityImportSmoke.EffectfulReturndataChecks

def main : IO Unit := SolidityImportSmoke.EffectfulReturndataChecks.runChecks
