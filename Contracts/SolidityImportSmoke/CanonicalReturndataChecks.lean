import Compiler.Proofs.IRGeneration.DenoteAgreement
import Compiler.Proofs.IRGeneration.SourceErrorDeclarations

namespace SolidityImportSmoke.CanonicalReturndataChecks
open Compiler.CompilationModel Compiler.Proofs.IRGeneration
open Verity.Core.Model

example (state : Denote.DenoteState) (destination source size : Nat) :
    DenoteAgreement.toStmtResult (Denote.execReturndataCopy state destination source size) =
      SourceSemantics.execReturndataCopy (DenoteAgreement.toRuntimeState state)
        destination source size :=
  DenoteAgreement.execReturndataCopy_eq state destination source size

example (state : SourceSemantics.RuntimeState) (destination source size : Nat)
    (errorPrefix : String) :
    SourceErrorDeclarations.Preserves state.errors
      (SourceSemantics.execReturndataCopy state destination source size errorPrefix) :=
  SourceErrorDeclarations.copy_errors state destination source size errorPrefix

private def initial : Denote.DenoteState :=
  { world := { Verity.defaultState with returndata := [0x1234] }
    bindings := [("outer", 7)]
    executionContext := some
      { opcode := { gas := 999, depth := 2, isStatic := false }
        warm := fun _ => false } }

private def check (result : SourceSemantics.StmtResult) (source : Nat) : IO Unit := do
  match result with
  | .continue next =>
      unless source == 30 &&
          (next.world.byteMemory.readByte 1).val == 0x12 &&
          (next.world.byteMemory.readByte 2).val == 0x34 &&
          next.bindings == [("outer", 7)] && next.world.returndata == [0x1234] &&
          next.executionContext.map (·.opcode.gas) == some 999 do
        throw (IO.userError "canonical copy bytes/frame mismatch")
  | .exceptional next =>
      unless source == 31 && next.executionContext.map (·.opcode.gas) == some 0 &&
          next.executionContext.map (·.opcode.depth) == some 2 &&
          next.bindings == [("outer", 7)] && next.world.returndata == [0x1234] &&
          next.world.byteMemory.size == initial.world.byteMemory.size do
        throw (IO.userError "canonical exception gas/frame mismatch")
  | _ => throw (IO.userError "canonical copy became revert or refusal")

def runChecks : IO Unit := do
  let state := DenoteAgreement.toRuntimeState initial
  for source in [30, 31] do
    let stmt := Stmt.returndataCopy (.literal 1) (.literal source) (.literal 2)
    check (SourceSemantics.execStmt [] state stmt) source
    check (SourceSemantics.execStmtWithEvents [] [] state stmt) source
    check (SourceSemantics.execStmtWithHelpers { name := "CanonicalCopy", fields := [], functions := [], constructor := none } [] 16 state stmt) source
    check (DenoteAgreement.toStmtResult
      (Denote.execStmt DenoteAgreement.sourceOracle [] initial stmt)) source
  for result in [SourceSemantics.execReturndataCopy { state with executionContext := none } 0 33 0,
      DenoteAgreement.toStmtResult
        (Denote.execReturndataCopy { initial with executionContext := none } 0 33 0)] do
    match result with
    | .interpretationError message =>
        unless message == "returndata copy exceptional exit requires actual opcode context" do
          throw (IO.userError "canonical copy refusal diagnostic changed")
    | _ => throw (IO.userError "missing context became EVM outcome")
  check (SourceSemantics.execReturndataCopy state
    (Verity.Core.Uint256.modulus + 1) (Verity.Core.Uint256.modulus + 30)
    (Verity.Core.Uint256.modulus + 2)) 30
  IO.println "canonical Source/Denote copy bytes, exception, refusal and frame checks passed"

end SolidityImportSmoke.CanonicalReturndataChecks
