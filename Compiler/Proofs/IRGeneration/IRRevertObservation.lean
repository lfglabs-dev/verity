import Compiler.Proofs.IRGeneration.IRInterpreter

/-! Exact observed REVERT slice for canonical IR execution. Failure without
an observed slice has no byte certificate; it is never projected to empty data. -/
namespace Compiler.Proofs.IRGeneration.IRRevertObservation
open Compiler.Yul

theorem capture_bytes (state : IRState) (offset size : Nat) :
    (state.captureRevert offset size).revertBytes =
      some ((List.range size).map (fun index =>
        UInt8.ofNat (state.byteMemory.readByte (offset + index)).val)) := rfl

theorem capture_empty (state : IRState) (offset : Nat) :
    (state.captureRevert offset 0).revertBytes = some [] := rfl

theorem unobserved (state : IRState) (absent : state.observedRevert = none) :
    state.revertBytes = none := by
  simp only [IRState.revertBytes, absent, Option.map_none]

theorem literal_revert (state : IRState) (fuel offset size : Nat) :
    execIRStmt (fuel + 1) state
      (.exprStmt (.call "revert" [.lit offset, .lit size])) =
      .revert (state.captureRevert offset size) := by
  simp only [execIRStmt, evalIRExpr]

end Compiler.Proofs.IRGeneration.IRRevertObservation
