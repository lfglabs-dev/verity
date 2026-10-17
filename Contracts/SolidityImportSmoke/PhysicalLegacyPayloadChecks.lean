import Compiler.Proofs.IRGeneration.CustomErrorPayloadIR

namespace SolidityImportSmoke.PhysicalLegacyPayloadChecks
open Compiler.Proofs.IRGeneration Compiler.Yul

/-- Obtain the lock through the actual interpreter's TSTORE instruction, rather
than writing a storage channel directly in the fixture. -/
noncomputable def locked : IRState :=
  match execIRStmt 1 (IRState.initial 0)
      (.exprStmt (.call "tstore" [.lit 0, .lit 1])) with
  | .continue state => state
  | _ => IRState.initial 0

@[simp] theorem locked_slot_zero : locked.transientStorage 0 = 1 := by
  simp [locked, execIRStmt, evalIRExpr]
example : locked.transientStorage 1 = 0 := by
  simp [locked, execIRStmt, evalIRExpr, IRState.initial]

example : execIRStmts 3 locked (guardPrologueStmts 0) = .revert locked := by
  simpa using execIRStmts_guardPrologue_locked 0 locked 0 (by decide) (by simp)

example : execIRStmts 4 locked (guardPrologueStmts 0) =
    .revert (locked.captureRevert 0 0) := by
  simpa using execIRStmts_guardPrologue_locked 1 locked 0 (by decide) (by simp)

example : locked.revertBytes = none := by
  simp [locked, execIRStmt, evalIRExpr, IRState.initial, IRState.revertBytes]
example : (locked.captureRevert 0 0).revertBytes = some [] := rfl

example (message : String) (fuel : Nat) (state : IRState)
    (extent : 68 + 32 * (Compiler.CompilationModel.chunkBytes32
      (Compiler.CompilationModel.bytesFromString message)).length ≤ Verity.Core.Uint256.modulus) :
    ∃ finalState,
      execIRStmts ((errorStringStmts message).length + fuel + 2) state
          (Compiler.ECM.revertWithMessage message) = .revert finalState ∧
      finalState.memory 0 = Compiler.Constants.errorStringSelectorWord ∧
      finalState.memory 4 = 32 ∧
      finalState.memory 36 = (Compiler.ECM.bytesFromString message).length ∧
      finalState.revertBytes = some (Compiler.CompilationModel.Denote.errorStringBytes message) :=
  execIRStmts_revertWithMessage message fuel state extent

end SolidityImportSmoke.PhysicalLegacyPayloadChecks
