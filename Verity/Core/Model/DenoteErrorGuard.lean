import Verity.Core.Model.Denote

/-! Literal-zero custom-error guards are terminal, even if argument evaluation
or error encoding fails. These lemmas concern the existing Denote semantics;
they do not alter statement execution or compiler lowering. -/

namespace Compiler.CompilationModel.DenoteErrorGuard
open Compiler.CompilationModel Denote

/-- Terminal metadata retains every argument for the other structural audits. -/
theorem require_error_zero_metadata (name : String) (args : List Expr) :
    (Stmt.requireError (.literal 0) name args).directMetadata.termination = .alwaysTerminates ∧
    (Stmt.requireError (.literal 0) name args).directMetadata.controlFlow = .reverts ∧
    (Stmt.requireError (.literal 0) name args).directMetadata.subexpressions =
      .literal 0 :: args := by
  exact ⟨rfl, rfl, rfl⟩

/-- Direct metadata and recursive analysis classify every error guard identically. -/
theorem require_error_control_flow_eq_metadata (condition : Expr)
    (name : String) (args : List Expr) :
    (Stmt.requireError condition name args).controlFlow =
      (Stmt.requireError condition name args).directMetadata.controlFlow := by
  rw [Stmt.controlFlow]

/-- An unreachable suffix cannot introduce a successful exit or fallthrough. -/
theorem require_error_zero_cons_control_flow (name : String) (args : List Expr)
    (rest : List Stmt) :
    Stmt.controlFlowList (.requireError (.literal 0) name args :: rest) = .reverts := by
  rw [Stmt.controlFlowList, Stmt.controlFlow]
  rfl

/-- Exact error bytes and evaluation failures are preserved by the zero guard. -/
theorem exec_require_error_zero_eq (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name : String) (args : List Expr) :
    execStmt oracle fields state (.requireError (.literal 0) name args) =
      (match evalExprList oracle fields state args with
      | none => .revert
      | some values => match customErrorBytes oracle state.errors name values with
        | none => .revert
        | some bytes => .revertWithData bytes) := by
  rw [execStmt, evalExpr]
  cases hargs : evalExprList oracle fields state args with
  | none => rfl
  | some values =>
      dsimp only
      cases hbytes : customErrorBytes oracle state.errors name values <;> rfl

/-- No argument or error-encoding result allows this guard to continue or return. -/
theorem exec_require_error_zero_reverts (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name : String) (args : List Expr) :
    execStmt oracle fields state (.requireError (.literal 0) name args) = .revert ∨
      ∃ bytes, execStmt oracle fields state (.requireError (.literal 0) name args) =
        .revertWithData bytes := by
  simp only [exec_require_error_zero_eq]
  cases hargs : evalExprList oracle fields state args with
  | none => exact Or.inl rfl
  | some values =>
      dsimp only
      cases hbytes : customErrorBytes oracle state.errors name values with
      | none => exact Or.inl rfl
      | some bytes => exact Or.inr ⟨bytes, rfl⟩

/-- A terminal custom error prevents all later statement effects from executing. -/
theorem exec_require_error_zero_cons (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name : String) (args : List Expr) (rest : List Stmt) :
    execStmtList oracle fields state (.requireError (.literal 0) name args :: rest) =
      execStmt oracle fields state (.requireError (.literal 0) name args) := by
  rcases exec_require_error_zero_reverts oracle fields state name args with
    failure | ⟨bytes, failure⟩
  · rw [execStmtList, failure]
  · rw [execStmtList, failure]

end Compiler.CompilationModel.DenoteErrorGuard
