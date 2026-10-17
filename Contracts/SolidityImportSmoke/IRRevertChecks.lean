import Compiler.Proofs.IRGeneration.FunctionBody.RequireBytes
import Compiler.Proofs.IRGeneration.IRRevertObservation
import Compiler.Proofs.IRGeneration.PhysicalErrorStringBytes
import Compiler.Proofs.IRGeneration.PhysicalCopyRevert
import Compiler.Proofs.IRGeneration.PhysicalReturndataExecution
import Verity.Core.Model.Denote

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace SolidityImportSmoke.IRRevertChecks
open Compiler.Proofs.IRGeneration Compiler.Yul

def state : IRState := (IRState.initial 0).writePhysicalMemoryValue 0 0x0102030405

example : state.revertBytes = none := rfl

example (runtime : IRState) (extra : Nat)
    (extent : 32 * runtime.returndata.length < Verity.Core.Uint256.modulus) :
    ∃ final, execIRStmts (extra + 6) runtime PhysicalReturndataExecution.body =
      .revert final ∧ final.revertBytes =
        some (runtime.returndata.flatMap Compiler.CompilationModel.Denote.wordBytes) :=
  PhysicalReturndataExecution.execute_payload_unbounded runtime extra extent

/-- Includes a legacy Nat above uint256; the actual physical source and ABI
encoder must retain the same bytes rather than rejecting it by assumption. -/
example :
    (List.range 64).map (fun index => UInt8.ofNat
      (Compiler.CompilationModel.DenoteMemory.wordListByte
        [Verity.Core.Uint256.modulus + 0x010203, 0xff] index).val) =
      [Verity.Core.Uint256.modulus + 0x010203, 0xff].flatMap
        Compiler.CompilationModel.Denote.wordBytes :=
  PhysicalReturndataBytes.buffer_encoding_unbounded _

example (runtime : IRState) (extra : Nat)
    (extent : 32 * runtime.returndata.length < Verity.Core.Uint256.modulus)
    (bounded : ∀ value ∈ runtime.returndata, value < Verity.Core.Uint256.modulus) :
    ∃ final, execIRStmts (extra + 6) runtime PhysicalReturndataExecution.body =
      .revert final ∧ final.revertBytes =
        some (runtime.returndata.flatMap Compiler.CompilationModel.Denote.wordBytes) :=
  PhysicalReturndataExecution.execute_payload runtime extra extent bounded

example (source : Nat → Compiler.CompilationModel.DenoteMemory.Byte)
    (destOffset sourceOffset size : Nat) :
    ((state.copyPhysicalBytes source destOffset sourceOffset size).captureRevert
      destOffset size).revertBytes =
      some ((List.range size).map (fun index =>
        UInt8.ofNat (source (sourceOffset + index)).val)) :=
  PhysicalCopyRevert.copied_payload state source destOffset sourceOffset size

example : ((state.copyPhysicalReturndata 0 0 0).captureRevert 0 0).revertBytes =
    some [] := rfl

example : (state.captureRevert 27 5).revertBytes =
    some [1, 2, 3, 4, 5] := by decide

example : (state.captureRevert 30 5).revertBytes =
    some [4, 5, 0, 0, 0] := by decide

example (fuel : Nat) :
    execIRStmt (fuel + 1) state
      (.exprStmt (.call "revert" [.lit 27, .lit 5])) =
    .revert (state.captureRevert 27 5) :=
  IRRevertObservation.literal_revert state fuel 27 5

example (fuel : Nat) :
    execIRStmt (fuel + 1) state
      (.exprStmt (.call "revert" [.lit 255, .lit 0])) =
    .revert (state.captureRevert 255 0) :=
  IRRevertObservation.literal_revert state fuel 255 0

/-- Actual compiler payload stores, including overlapping headers, agree
with the Source ABI encoder at empty, UTF-8, and chunk-boundary inputs. -/
private def payloadBytes (message : String) : Option (List UInt8) :=
  let post := PhysicalRevertWrites.applyStores state
    (PhysicalErrorStringExecution.writes message)
  (post.captureRevert 0
    (68 + ((Compiler.CompilationModel.bytesFromString message).length + 31) / 32 * 32)).revertBytes

theorem errorString_empty : payloadBytes "" = some (Compiler.CompilationModel.Denote.errorStringBytes "") := by
  decide +kernel
theorem errorString_utf8 : payloadBytes "é🙂" = some (Compiler.CompilationModel.Denote.errorStringBytes "é🙂") := by
  decide +kernel
theorem errorString_31 : payloadBytes "1234567890123456789012345678901" =
    some (Compiler.CompilationModel.Denote.errorStringBytes "1234567890123456789012345678901") := by
  decide +kernel
theorem errorString_32 : payloadBytes "12345678901234567890123456789012" =
    some (Compiler.CompilationModel.Denote.errorStringBytes "12345678901234567890123456789012") := by
  decide +kernel
theorem errorString_33 : payloadBytes "123456789012345678901234567890123" =
    some (Compiler.CompilationModel.Denote.errorStringBytes "123456789012345678901234567890123") := by
  decide +kernel

/-- A failed require terminates before a continuation that would STOP,
retaining the actual nonempty Error(string) bytes. -/
example : ∃ finalState,
    execIRStmts ((PhysicalErrorStringExecution.writes "é🙂").length + 4) state
      [.if_ (.lit 1) (Compiler.CompilationModel.revertWithMessage "é🙂"),
       .exprStmt (.call "stop" [])] = .revert finalState ∧
    finalState.revertBytes = some (Compiler.CompilationModel.Denote.errorStringBytes "é🙂") := by
  exact FunctionBody.failed_require_ir_bytes state (.lit 1) "é🙂"
    [.exprStmt (.call "stop" [])] 0 (by simp [evalIRExpr]) (by decide +kernel)

/-- The old outer-list budget exhausts before the REVERT opcode: it cannot
certify the same payload even though the legacy result says revert. -/
example : execIRStmts 2 state
    [.if_ (.lit 1) (Compiler.CompilationModel.revertWithMessage "é🙂")] = .revert state := by
  simp only [execIRStmts, execIRStmt, evalIRExpr]
  have exhausted : execIRStmts 0 state
      (Compiler.CompilationModel.revertWithMessage "é🙂") = .revert state := by
    rw [PhysicalErrorStringExecution.shape]
    simp only [PhysicalErrorStringExecution.payloadStores, List.cons_append, execIRStmts]
  rw [exhausted]
  simp

end SolidityImportSmoke.IRRevertChecks
