import Compiler.Proofs.IRGeneration.FunctionBody.Stmt

namespace Compiler.Proofs.IRGeneration.FunctionBody
open Compiler.CompilationModel Compiler.Yul

private theorem list_size_append (left right : List YulStmt) :
    sizeOf (left ++ right) + 1 = sizeOf left + sizeOf right := by
  induction left with
  | nil => simp [Nat.add_comm]
  | cons head tail ih =>
      simp only [List.cons_append, List.cons.sizeOf_spec]
      omega

private theorem list_length_lt_size (body : List YulStmt) : body.length < sizeOf body := by
  induction body with
  | nil => simp
  | cons head tail ih =>
      simp only [List.length_cons, List.cons.sizeOf_spec]
      omega

/-- Structural fuel slack never decreases when compiled statements are added. -/
theorem yul_slack_append (left right : List YulStmt) :
    sizeOf left - left.length ≤ sizeOf (left ++ right) - (left ++ right).length ∧
    sizeOf right - right.length ≤ sizeOf (left ++ right) - (left ++ right).length := by
  have sum := list_size_append left right
  have leftSize := list_length_lt_size left
  have rightSize := list_length_lt_size right
  simp only [List.length_append]
  omega

/-- The existing whole-body structural fuel covers every core require payload.
No additional reserve assumption is needed by a concrete function caller. -/
theorem requireFuelReserve_of_core_compile
    {fields : List Field} {scope : List String} {statements : List Stmt}
    (core : StmtListCompileCore scope statements)
    (inScope : List String) (body : List YulStmt)
    (compiled : compileStmtList fields [] [] .calldata [] false inScope [] statements = .ok body) :
    requireFuelReserve statements ≤ sizeOf body - body.length := by
  induction core generalizing inScope body with
  | nil => simp [requireFuelReserve]
  | @require_ scope condition message rest _ _ _ ih =>
      obtain ⟨head, tail, headCompiled, tailCompiled, shape⟩ := compileStmtList_cons_ok_inv compiled
      subst body
      have tailBudget := ih _ _ tailCompiled
      have slack := yul_slack_append head tail
      unfold compileStmt compileStmtWithFork at headCompiled
      cases fail : compileRequireFailCondWithInternals fields .calldata [] condition with
      | error error => simp [fail] at headCompiled
      | ok expression =>
          simp [fail] at headCompiled
          subst head
          have budget := failed_require_sizeOf_budget expression message [] 0
          simp only [List.length_cons, List.length_nil] at slack
          simp only [requireFuelReserve]
          apply max_le
          · omega
          · omega
  | _ =>
      obtain ⟨head, tail, headCompiled, tailCompiled, shape⟩ := compileStmtList_cons_ok_inv compiled
      subst body
      have slack := (yul_slack_append head tail).2
      simp only [requireFuelReserve]
      apply le_trans _ slack
      apply_assumption
      exact tailCompiled

end Compiler.Proofs.IRGeneration.FunctionBody
