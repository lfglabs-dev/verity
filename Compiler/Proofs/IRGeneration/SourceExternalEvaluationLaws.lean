import Compiler.Proofs.IRGeneration.SourceStatementEvaluation

/-! Exact staging equations for typed external-call argument evaluation.
These laws expose the actual argument executor and its terminal state. They
certify neither the abstract receipt oracle nor an arbitrary external callee. -/
namespace Compiler.Proofs.IRGeneration.SourceExternalEvaluationLaws
open Compiler.CompilationModel SourceSemantics SourceExpressionOutcome

/-- A direct external call consumes its receipt after typed argument effects. -/
theorem externalCallBind_after_arguments
    (spec : CompilationModel) (fields : List Field) (fuel : Nat)
    (state next : RuntimeState) (names : List String) (name : String)
    (args : List Expr) (values : List Nat)
    (evaluated : SourceExpressionEvaluation.evalArgs
      (SourceStatementEvaluation.execStmtsFrame true spec fields fuel)
      spec fields fuel state args = .value values next) :
    SourceStatementEvaluation.execStmt spec fields (fuel + 1) state
      (.externalCallBind names name args) =
    SourceSemantics.execStmtWithEvents fields spec.events next
      (.externalCallBind names name (values.map Expr.literal)) := by
  simp only [SourceStatementEvaluation.execStmt,
    SourceStatementEvaluation.execStmtFrame, evaluated,
    SourceStatementEvaluation.consume]

/-- Catching a callee failure does not discard earlier argument effects. -/
theorem tryExternalCallBind_after_arguments
    (spec : CompilationModel) (fields : List Field) (fuel : Nat)
    (state next : RuntimeState) (successName : String) (names : List String) (name : String)
    (args : List Expr) (values : List Nat)
    (evaluated : SourceExpressionEvaluation.evalArgs
      (SourceStatementEvaluation.execStmtsFrame true spec fields fuel)
      spec fields fuel state args = .value values next) :
    SourceStatementEvaluation.execStmt spec fields (fuel + 1) state
      (.tryExternalCallBind successName names name args) =
    SourceSemantics.execStmtWithEvents fields spec.events next
      (.tryExternalCallBind successName names name (values.map Expr.literal)) := by
  simp only [SourceStatementEvaluation.execStmt,
    SourceStatementEvaluation.execStmtFrame, evaluated,
    SourceStatementEvaluation.consume]

/-- An ECM receives the actual post-argument state and resolved operands. -/
theorem ecm_after_arguments
    (spec : CompilationModel) (fields : List Field) (fuel : Nat)
    (state next : RuntimeState) (mod : Compiler.ECM.ExternalCallModule)
    (args : List Expr) (values : List Nat)
    (evaluated : SourceExpressionEvaluation.evalArgs
      (SourceStatementEvaluation.execStmtsFrame true spec fields fuel)
      spec fields fuel state args = .value values next) :
    SourceStatementEvaluation.execStmt spec fields (fuel + 1) state (.ecm mod args) =
    SourceSemantics.execStmtWithEvents fields spec.events next
      (.ecm mod (values.map Expr.literal)) := by
  simp only [SourceStatementEvaluation.execStmt,
    SourceStatementEvaluation.execStmtFrame, evaluated,
    SourceStatementEvaluation.consume]
end Compiler.Proofs.IRGeneration.SourceExternalEvaluationLaws
