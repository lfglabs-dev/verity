import Compiler.Proofs.IRGeneration.GenericInduction.ResultRelation
import Compiler.Proofs.IRGeneration.PhysicalReturndataExecution

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel Compiler.Yul

/-- Actual Source and compiler bubbling agree on the exact payload, with the
buffer-size obligation visible. No empty-buffer or word-value bound is used. -/
theorem compiled_revertReturndata_exact_bytes
    {fields : List Field} {scope : List String}
    (runtime : SourceSemantics.RuntimeState) (state : IRState) (extraFuel : Nat)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (extent : 32 * state.returndata.length < Verity.Core.Uint256.modulus)
    (slack : sizeOf PhysicalReturndataExecution.body -
      PhysicalReturndataExecution.body.length ≤ extraFuel) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmt fields runtime .revertReturndata = sourceResult ∧
      execIRStmts (PhysicalReturndataExecution.body.length + extraFuel + 1)
        state PhysicalReturndataExecution.body = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope .revertReturndata)
        sourceResult irExec := by
  have enough : 4 ≤ extraFuel := by
    have bodySize : 5 ≤ sizeOf PhysicalReturndataExecution.body := by decide
    have bodyLength : PhysicalReturndataExecution.body.length = 1 := rfl
    omega
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  obtain ⟨final, executed, bytes⟩ :=
    PhysicalReturndataExecution.execute_payload_unbounded state extra extent
  have sameBuffer := FunctionBody.runtimeStateMatchesIR_returndata hruntime
  refine ⟨.revertWithData (runtime.world.returndata.flatMap Denote.wordBytes),
    .revert final, rfl, ?_, ?_⟩
  · have fuel : PhysicalReturndataExecution.body.length + (4 + extra) + 1 =
        extra + 6 := by
      have bodyLength : PhysicalReturndataExecution.body.length = 1 := rfl
      omega
    simpa only [fuel] using executed
  · simpa only [stmtStepMatchesIRExec, sameBuffer] using bytes

theorem compile_revertReturndata_body (fields : List Field) (scope : List String) :
    CompilationModel.compileStmt fields [] [] .calldata [] false scope []
      .revertReturndata = Except.ok PhysicalReturndataExecution.body := by
  simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    PhysicalReturndataExecution.body, pure, Except.pure]

end Compiler.Proofs.IRGeneration
