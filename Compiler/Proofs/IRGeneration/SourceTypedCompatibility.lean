import Compiler.Proofs.IRGeneration.SourceStatementEvaluation

/-! Compatibility steps for migrating canonical Source execution. These laws
retain the entire runtime, rather than projecting effectful results to Option.
They characterize successful helper-free primitives and resolved scalar
consumers; they do not equate refusals with ordinary EVM reverts. -/
namespace Compiler.Proofs.IRGeneration.SourceTypedCompatibility
open Compiler.CompilationModel
open SourceSemantics SourceExpressionOutcome

theorem primitive_success (fields : List Field) (state : RuntimeState)
    (expr : Expr) (value : Nat) (h : evalExpr fields state expr = some value) :
    SourceExpressionEvaluation.primitive fields state expr = .value value state := by
  simp only [SourceExpressionEvaluation.primitive, h]

theorem primitive_success_iff (fields : List Field) (state final : RuntimeState)
    (expr : Expr) (value : Nat) :
    SourceExpressionEvaluation.primitive fields state expr = .value value final ↔
      evalExpr fields state expr = some value ∧ final = state := by
  unfold SourceExpressionEvaluation.primitive
  cases h : evalExpr fields state expr with
  | none => simp
  | some resolved => simp only [Result.value.injEq, Option.some.injEq]
                     constructor
                     · rintro ⟨hv, hs⟩; exact ⟨hv, hs.symm⟩
                     · rintro ⟨hv, hs⟩; exact ⟨hv, hs.symm⟩

theorem resolved_consumer (fields : List Field) (events : List EventDef)
    (state : RuntimeState) (expr : Expr) (value : Nat)
    (consumer : Nat → Stmt) (h : evalExpr fields state expr = some value) :
    SourceStatementEvaluation.consume (SourceExpressionEvaluation.primitive fields state expr)
      (fun resolved next => execStmtWithEvents fields events next (consumer resolved)) =
      execStmtWithEvents fields events state (consumer value) := by
  rw [primitive_success fields state expr value h]
  rfl

/-- The arithmetic compatibility step requires the actual poststate of the
left operand as the input to the right. The helper-free final primitive cannot
silently revert or discard either operand's effects. -/
theorem add_success (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (fields : List Field) (fuel : Nat)
    (initial leftState rightState : RuntimeState) (left right : Expr)
    (leftValue rightValue result : Nat)
    (hl : SourceExpressionEvaluation.eval runBody spec fields fuel initial left =
      .value leftValue leftState)
    (hr : SourceExpressionEvaluation.eval runBody spec fields fuel leftState right =
      .value rightValue rightState)
    (hp : evalExpr fields rightState (.add (.literal leftValue) (.literal rightValue)) =
      some result) :
    SourceExpressionEvaluation.eval runBody spec fields (fuel + 1) initial (.add left right) =
      .value result rightState := by
  rw [SourceExpressionEvaluation.eval_add, hl]
  simp only [Result.bind]
  rw [hr]
  simp only [Result.bind]
  exact primitive_success fields rightState _ result hp

theorem require_compatibility (fields : List Field) (events : List EventDef)
    (state : RuntimeState) (expr : Expr) (value : Nat) (message : String)
    (h : evalExpr fields state expr = some value)
    (normalized : wordNormalize value = value) :
    SourceStatementEvaluation.consume (SourceExpressionEvaluation.primitive fields state expr)
      (fun resolved next => execStmtWithEvents fields events next (.require (.literal resolved) message)) =
      execStmtWithEvents fields events state (.require expr message) := by
  rw [resolved_consumer fields events state expr value (fun v => .require (.literal v) message) h]
  simp only [execStmtWithEvents, evalExpr, h, normalized]

theorem return_compatibility (fields : List Field) (events : List EventDef)
    (state : RuntimeState) (expr : Expr) (value : Nat)
    (h : evalExpr fields state expr = some value)
    (normalized : wordNormalize value = value) :
    SourceStatementEvaluation.consume (SourceExpressionEvaluation.primitive fields state expr)
      (fun resolved next => execStmtWithEvents fields events next (.return (.literal resolved))) =
      execStmtWithEvents fields events state (.return expr) := by
  rw [resolved_consumer fields events state expr value (fun v => .return (.literal v)) h]
  simp only [execStmtWithEvents, evalExpr, h, normalized]

/-- A successful argument trace records every computed operand poststate.
Fuel is the evaluator's resource bound, not EVM gas. -/
inductive ArgumentTrace (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (fields : List Field) :
    Nat → RuntimeState → List Expr → List Nat → RuntimeState → Prop where
  | nil (fuel : Nat) (state : RuntimeState) :
      ArgumentTrace runBody spec fields fuel state [] [] state
  | cons {fuel : Nat} {state next final : RuntimeState}
      {expr : Expr} {rest : List Expr} {value : Nat} {values : List Nat}
      (head : SourceExpressionEvaluation.eval runBody spec fields fuel state expr = .value value next)
      (tail : ArgumentTrace runBody spec fields fuel next rest values final) :
      ArgumentTrace runBody spec fields (fuel + 1) state (expr :: rest) (value :: values) final

theorem argumentTrace_execution (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (fields : List Field)
    {fuel : Nat} {state final : RuntimeState} {exprs : List Expr} {values : List Nat}
    (trace : ArgumentTrace runBody spec fields fuel state exprs values final) :
    SourceExpressionEvaluation.evalArgs runBody spec fields fuel state exprs = .value values final := by
  induction trace with
  | nil fuel state => cases fuel <;> rfl
  | cons head tail ih =>
      simp only [SourceExpressionEvaluation.evalArgs, head, Result.bind, ih]

theorem argumentTrace_of_execution (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (fields : List Field)
    {fuel : Nat} {state final : RuntimeState} {exprs : List Expr} {values : List Nat}
    (executed : SourceExpressionEvaluation.evalArgs runBody spec fields fuel state exprs =
      .value values final) :
    ArgumentTrace runBody spec fields fuel state exprs values final := by
  induction fuel generalizing state final exprs values with
  | zero =>
      cases exprs with
      | nil => simp only [SourceExpressionEvaluation.evalArgs, Result.value.injEq] at executed
               rcases executed with ⟨rfl, rfl⟩
               exact .nil 0 state
      | cons => simp only [SourceExpressionEvaluation.evalArgs] at executed; cases executed
  | succ fuel ih =>
      cases exprs with
      | nil => simp only [SourceExpressionEvaluation.evalArgs, Result.value.injEq] at executed
               rcases executed with ⟨rfl, rfl⟩
               exact .nil (fuel + 1) state
      | cons expr rest =>
          rw [SourceExpressionEvaluation.evalArgs] at executed
          cases head : SourceExpressionEvaluation.eval runBody spec fields fuel state expr with
          | value value next =>
              rw [head] at executed
              simp only [Result.bind] at executed
              cases tail : SourceExpressionEvaluation.evalArgs runBody spec fields fuel next rest with
              | value words finalState =>
                  rw [tail] at executed
                  simp only [Result.bind] at executed
                  cases executed
                  exact .cons head (ih tail)
              | revertWithData => simp only [tail, Result.bind] at executed; cases executed
              | revert => simp only [tail, Result.bind] at executed; cases executed
              | halt => simp only [tail, Result.bind] at executed; cases executed
              | interpretationError => simp only [tail, Result.bind] at executed; cases executed
              | exceptional => simp only [tail, Result.bind] at executed; cases executed
          | revertWithData => simp only [head, Result.bind] at executed; cases executed
          | revert => simp only [head, Result.bind] at executed; cases executed
          | halt => simp only [head, Result.bind] at executed; cases executed
          | interpretationError => simp only [head, Result.bind] at executed; cases executed
          | exceptional => simp only [head, Result.bind] at executed; cases executed

theorem argumentTrace_length (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (fields : List Field)
    {fuel : Nat} {state final : RuntimeState} {exprs : List Expr} {values : List Nat}
    (trace : ArgumentTrace runBody spec fields fuel state exprs values final) :
    exprs.length = values.length := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem argumentTrace_iff_execution (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (state final : RuntimeState) (exprs : List Expr) (values : List Nat) :
    ArgumentTrace runBody spec fields fuel state exprs values final ↔
      SourceExpressionEvaluation.evalArgs runBody spec fields fuel state exprs = .value values final :=
  ⟨argumentTrace_execution runBody spec fields, argumentTrace_of_execution runBody spec fields⟩

/-- Compose a state invariant across the actual operand trace, including
helper effects. The premise must hold for each successful operand execution. -/
theorem argumentTrace_preserves (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (fields : List Field) (invariant : RuntimeState → Prop)
    (step : ∀ (fuel : Nat) (state next : RuntimeState) (expr : Expr) (value : Nat),
      invariant state →
      SourceExpressionEvaluation.eval runBody spec fields fuel state expr = .value value next →
      invariant next)
    {fuel : Nat} {state final : RuntimeState} {exprs : List Expr} {values : List Nat}
    (trace : ArgumentTrace runBody spec fields fuel state exprs values final)
    (initial : invariant state) : invariant final := by
  induction trace with
  | nil => exact initial
  | cons head tail ih => exact ih (step _ _ _ _ _ initial head)

theorem argumentTrace_mstore (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (state final : RuntimeState) (offset value : Expr) (dst word : Nat)
    (trace : ArgumentTrace (SourceStatementEvaluation.execInternalStmts spec fields fuel)
      spec fields fuel state [offset, value] [dst, word] final) :
    SourceStatementEvaluation.execStmt spec fields (fuel + 1) state (.mstore offset value) =
      execStmtWithEvents fields spec.events final (.mstore (.literal dst) (.literal word)) := by
  have executed := argumentTrace_execution _ _ _ trace
  simp only [SourceStatementEvaluation.execInternalStmts] at executed
  simp only [SourceStatementEvaluation.execStmt, SourceStatementEvaluation.execStmtFrame, SourceStatementEvaluation.execInternalStmts, executed, SourceStatementEvaluation.consume]

/-- Only successful source outcomes commit this local postcondition.
Exceptional/refused/reverting executions still require the separate frame
rollback proof; this predicate does not certify their partially computed state. -/
def SuccessInvariant (invariant : RuntimeState → Prop) : StmtResult → Prop
  | .continue state | .stop state | .return _ state => invariant state
  | .revert | .revertWithData _ | .interpretationError _ | .exceptional _ => True

theorem statementList_preserves (spec : CompilationModel) (fields : List Field)
    (invariant : RuntimeState → Prop)
    (step : ∀ (fuel : Nat) (state : RuntimeState) (stmt : Stmt),
      invariant state → SuccessInvariant invariant
        (SourceStatementEvaluation.execStmt spec fields fuel state stmt))
    (fuel : Nat) (state : RuntimeState) (stmts : List Stmt)
    (initial : invariant state) :
    SuccessInvariant invariant (SourceStatementEvaluation.execStmts spec fields fuel state stmts) := by
  induction fuel generalizing state stmts with
  | zero => cases stmts <;> simpa only [SourceStatementEvaluation.execStmts, SourceStatementEvaluation.execStmtsFrame, SuccessInvariant] using initial
  | succ fuel ih =>
      cases stmts with
      | nil => exact initial
      | cons stmt rest =>
          have atom := step fuel state stmt initial
          cases executed : SourceStatementEvaluation.execStmt spec fields fuel state stmt with
          | «continue» next =>
              simp only [SourceStatementEvaluation.execStmt] at executed
              have nextInvariant : invariant next := by simpa only [SourceStatementEvaluation.execStmt, executed, SuccessInvariant] using atom
              simpa only [SourceStatementEvaluation.execStmts, SourceStatementEvaluation.execStmtsFrame, executed] using ih next rest nextInvariant
          | stop next =>
              simp only [SourceStatementEvaluation.execStmt] at executed
              simpa only [SourceStatementEvaluation.execStmts, SourceStatementEvaluation.execStmtsFrame, SourceStatementEvaluation.execStmt, executed, SuccessInvariant] using atom
          | «return» value next =>
              simp only [SourceStatementEvaluation.execStmt] at executed
              simpa only [SourceStatementEvaluation.execStmts, SourceStatementEvaluation.execStmtsFrame, SourceStatementEvaluation.execStmt, executed, SuccessInvariant] using atom
          | revertWithData =>
              simp only [SourceStatementEvaluation.execStmt] at executed
              simp only [SourceStatementEvaluation.execStmts, SourceStatementEvaluation.execStmtsFrame, executed, SuccessInvariant]
          | revert =>
              simp only [SourceStatementEvaluation.execStmt] at executed
              simp only [SourceStatementEvaluation.execStmts, SourceStatementEvaluation.execStmtsFrame, executed, SuccessInvariant]
          | interpretationError =>
              simp only [SourceStatementEvaluation.execStmt] at executed
              simp only [SourceStatementEvaluation.execStmts, SourceStatementEvaluation.execStmtsFrame, executed, SuccessInvariant]
          | exceptional =>
              simp only [SourceStatementEvaluation.execStmt] at executed
              simp only [SourceStatementEvaluation.execStmts, SourceStatementEvaluation.execStmtsFrame, executed, SuccessInvariant]

theorem argumentTrace_create2 (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (state final : RuntimeState) (destination : String)
    (offset size salt : Expr) (dst extent nonce : Nat)
    (trace : ArgumentTrace (SourceStatementEvaluation.execInternalStmts spec fields fuel)
      spec fields fuel state [offset, size, salt] [dst, extent, nonce] final) :
    SourceStatementEvaluation.execStmt spec fields (fuel + 1) state
      (.create2 destination offset size salt) =
      execCreation fields final destination (.literal dst) (.literal extent) (.literal nonce) := by
  have executed := argumentTrace_execution _ _ _ trace
  simp only [SourceStatementEvaluation.execInternalStmts] at executed
  simp only [SourceStatementEvaluation.execStmt, SourceStatementEvaluation.execStmtFrame, SourceStatementEvaluation.execInternalStmts, executed, SourceStatementEvaluation.consume]

end Compiler.Proofs.IRGeneration.SourceTypedCompatibility
