import Compiler.Proofs.IRGeneration.SourceStatementEvaluation

/-! Global halting propagation in the staged typed source executor.
These equations do not claim canonical dispatch or compiler correspondence. -/
namespace Compiler.Proofs.IRGeneration.SourceHaltingLaws
open Compiler.CompilationModel SourceSemantics SourceExpressionOutcome

theorem bind_halt (state : RuntimeState) (next : α → RuntimeState → Result β) :
    Result.bind (.halt state) next = .halt state := rfl

theorem assign_halt (name : String) (state : RuntimeState) :
    assign name (.halt state) = .stop state := rfl

theorem consume_halt (state : RuntimeState) (next : α → RuntimeState → StmtResult) :
    SourceStatementEvaluation.consume (.halt state) next = .stop state := rfl

theorem helper_stop (caller final : RuntimeState)
    (marker : final.observedReturnWords = none) :
    ofHelperBody caller (.stop final) = .halt { final with bindings := caller.bindings } := by
  simp only [ofHelperBody, marker]

theorem evalList_halt (eval : RuntimeState → Expr → Result Nat)
    (state final : RuntimeState) (expr : Expr) (rest : List Expr)
    (halted : eval state expr = .halt final) :
    evalList eval state (expr :: rest) = .halt final := by
  simp only [evalList, halted, Result.bind]

theorem statementList_stop (internalFrame : Bool) (spec : CompilationModel)
    (fields : List Field) (fuel : Nat) (state final : RuntimeState)
    (stmt : Stmt) (rest : List Stmt)
    (halted : SourceStatementEvaluation.execStmtFrame internalFrame spec fields fuel state stmt =
      .stop final) :
    SourceStatementEvaluation.execStmtsFrame internalFrame spec fields (fuel + 1)
      state (stmt :: rest) = .stop final := by
  simp only [SourceStatementEvaluation.execStmtsFrame, halted]

theorem loop_stop (internalFrame : Bool) (spec : CompilationModel)
    (fields : List Field) (fuel : Nat) (state final : RuntimeState)
    (name : String) (body : List Stmt) (index remaining : Nat)
    (halted : SourceStatementEvaluation.execStmtsFrame internalFrame spec fields fuel
      { state with bindings := bindValue state.bindings name (wordNormalize index) } body =
      .stop final) :
    SourceStatementEvaluation.execLoopFrame internalFrame spec fields (fuel + 1)
      state name body index (remaining + 1) = .stop final := by
  simp only [SourceStatementEvaluation.execLoopFrame, halted]

end Compiler.Proofs.IRGeneration.SourceHaltingLaws
