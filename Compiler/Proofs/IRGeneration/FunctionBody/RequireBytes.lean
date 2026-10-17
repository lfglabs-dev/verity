import Compiler.Proofs.IRGeneration.FunctionBody.Base
import Compiler.Proofs.IRGeneration.PhysicalErrorStringBytes

/-! Exact failed-require correspondence, including physical revert bytes.
The fuel covers the nested payload body, not only the outer singleton list. -/
namespace Compiler.Proofs.IRGeneration.FunctionBody
open Compiler.CompilationModel Compiler.Yul

/-- A genuinely evaluated failed guard terminates before any continuation,
with the exact payload and enough fuel for its nested stores and REVERT. -/
theorem failed_require_ir_bytes (state : IRState) (failCond : YulExpr)
    (message : String) (tail : List YulStmt) (extraFuel : Nat)
    (failed : evalIRExpr state failCond = some 1)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus) :
    ∃ finalState,
      execIRStmts ((PhysicalErrorStringExecution.writes message).length + extraFuel + 4)
        state (.if_ failCond (revertWithMessage message) :: tail) = .revert finalState ∧
      finalState.revertBytes = some (Denote.errorStringBytes message) := by
  obtain ⟨finalState, executed, bytes⟩ :=
    PhysicalErrorStringBytes.execute_payload state message extraFuel extent
  refine ⟨finalState, ?_, bytes⟩
  rw [show (PhysicalErrorStringExecution.writes message).length + extraFuel + 4 =
      ((PhysicalErrorStringExecution.writes message).length + extraFuel + 2) + 1 + 1 by omega]
  simp only [execIRStmts, execIRStmt, failed]
  rw [executed]
  simp

/-- Any caller budget covering the complete nested payload is sufficient;
this form integrates with whole-body fuel bounds without changing observations. -/
theorem failed_require_ir_bytes_of_fuel (state : IRState) (failCond : YulExpr)
    (message : String) (tail : List YulStmt) (fuel : Nat)
    (enough : (PhysicalErrorStringExecution.writes message).length + 4 ≤ fuel)
    (failed : evalIRExpr state failCond = some 1)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus) :
    ∃ finalState,
      execIRStmts fuel state (.if_ failCond (revertWithMessage message) :: tail) = .revert finalState ∧
      finalState.revertBytes = some (Denote.errorStringBytes message) := by
  have budget : (PhysicalErrorStringExecution.writes message).length +
      (fuel - ((PhysicalErrorStringExecution.writes message).length + 4)) + 4 = fuel := by omega
  simpa only [budget] using failed_require_ir_bytes state failCond message tail
    (fuel - ((PhysicalErrorStringExecution.writes message).length + 4)) failed extent

private theorem store_trace_length {statements writes}
    (trace : PhysicalRevertWrites.StoreTrace statements writes) :
    statements.length = writes.length := by
  induction trace with
  | nil => rfl
  | consLit offset value trace ih => simpa only [List.length_cons] using congrArg Nat.succ ih
  | consHex offset value trace ih => simpa only [List.length_cons] using congrArg Nat.succ ih

private theorem yul_length_lt_size (statements : List YulStmt) :
    statements.length < sizeOf statements := by
  induction statements with
  | nil => simp only [List.length_nil, List.nil.sizeOf_spec]; omega
  | cons head tail ih =>
      simp only [List.length_cons, List.cons.sizeOf_spec]
      omega

/-- Whole-body structural fuel honestly covers the complete nested payload. -/
theorem failed_require_sizeOf_budget (failCond : YulExpr) (message : String)
    (tail : List YulStmt) (extraFuel : Nat) :
    (PhysicalErrorStringExecution.writes message).length + 4 ≤
      sizeOf (.if_ failCond (revertWithMessage message) :: tail) + extraFuel + 1 := by
  have traceLength := store_trace_length (PhysicalErrorStringExecution.trace message)
  have bodyLength : (revertWithMessage message).length =
      (PhysicalErrorStringExecution.writes message).length + 1 := by
    rw [PhysicalErrorStringExecution.shape]
    simp only [List.length_append, List.length_cons, List.length_nil, traceLength]
  have bodySize := yul_length_lt_size (revertWithMessage message)
  simp only [List.cons.sizeOf_spec, YulStmt.if_.sizeOf_spec]
  omega

/-- Exact failed require observation under the existing structural whole-body
fuel convention; only actual message address safety remains a premise. -/
theorem failed_require_ir_bytes_sizeOf (state : IRState) (failCond : YulExpr)
    (message : String) (tail : List YulStmt) (extraFuel : Nat)
    (failed : evalIRExpr state failCond = some 1)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus) :
    ∃ finalState,
      execIRStmts (sizeOf (.if_ failCond (revertWithMessage message) :: tail) + extraFuel + 1)
        state (.if_ failCond (revertWithMessage message) :: tail) = .revert finalState ∧
      finalState.revertBytes = some (Denote.errorStringBytes message) := by
  exact failed_require_ir_bytes_of_fuel state failCond message tail _
    (failed_require_sizeOf_budget failCond message tail extraFuel) failed extent

/-- A failed core require compiles and executes to the exact Source payload.
Neither a refusal nor an exhausted interpreter is admitted by this theorem. -/
theorem compiled_require_failure_bytes
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {cond : Expr} (message : String) (extraFuel : Nat)
    (core : ExprCompileCore cond)
    (exactBindings : bindingsExactlyMatchIRVarsOnExpr cond runtime.bindings state)
    (bounded : bindingsBounded runtime.bindings)
    (present : exprBoundNamesPresent cond runtime.bindings)
    (matching : runtimeStateMatchesIR fields runtime state)
    (failed : SourceSemantics.evalExpr fields runtime cond = some 0)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus) :
    ∃ bodyIR finalState,
      compileStmt fields [] [] .calldata [] false [] [] (.require cond message) = .ok bodyIR ∧
      SourceSemantics.execStmt fields runtime (.require cond message) =
        .revertWithData (Denote.errorStringBytes message) ∧
      execIRStmts ((PhysicalErrorStringExecution.writes message).length + extraFuel + 4)
        state bodyIR = .revert finalState ∧
      finalState.revertBytes = some (Denote.errorStringBytes message) := by
  obtain ⟨failCond, compiled, evaluated⟩ :=
    eval_compileRequireFailCond_core_onExpr core exactBindings bounded present matching
  have condition : evalIRExpr state failCond = some 1 := by
    simpa only [failed, SourceSemantics.boolWord, decide_true, if_true] using evaluated
  obtain ⟨finalState, executed, bytes⟩ :=
    PhysicalErrorStringBytes.execute_payload state message extraFuel extent
  refine ⟨[.if_ failCond (revertWithMessage message)], finalState, ?_, ?_, ?_, bytes⟩
  · have internal := compiled
    rw [← compileRequireFailCondWithInternals_nil_eq] at internal
    simp only [compileStmt, compileStmtWithFork, internal]
    rfl
  · simp only [SourceSemantics.execStmt, failed, bne_self_eq_false, Bool.false_eq_true, if_false]
  · rw [show (PhysicalErrorStringExecution.writes message).length + extraFuel + 4 =
        ((PhysicalErrorStringExecution.writes message).length + extraFuel + 2) + 1 + 1 by omega]
    simp only [execIRStmts, execIRStmt, condition]
    rw [executed]
    simp

end Compiler.Proofs.IRGeneration.FunctionBody
