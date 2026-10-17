import Compiler.Proofs.IRGeneration.SourceStatementEvaluation

/-! Exact byte transport in Source outcomes. Encoding and caller rollback are
separate obligations; these equations never classify a refusal as a revert. -/
namespace Compiler.Proofs.IRGeneration.SourceRevertTransport
open Compiler.CompilationModel SourceSemantics SourceExpressionOutcome

theorem bind_bytes (data : List UInt8) (next : α → RuntimeState → Result β) :
    Result.bind (.revertWithData data) next = .revertWithData data := rfl

theorem helper_bytes (caller : RuntimeState) (data : List UInt8) :
    ofHelperBody caller (.revertWithData data) = .revertWithData data := rfl

theorem assign_bytes (name : String) (data : List UInt8) :
    assign name (.revertWithData data) = .revertWithData data := rfl

theorem consume_bytes (data : List UInt8) (next : α → RuntimeState → StmtResult) :
    SourceStatementEvaluation.consume (.revertWithData data) next = .revertWithData data := rfl

theorem discarded_helper_bytes (caller : RuntimeState) (data : List UInt8) :
    SourceStatementEvaluation.restoreCaller caller (.revertWithData data) = .revertWithData data := rfl

theorem assigned_helper_bytes (caller : RuntimeState) (names : List String) (data : List UInt8) :
    SourceStatementEvaluation.assignHelperResult caller names (.revertWithData data) = .revertWithData data := rfl

theorem statement_list_bytes (internalFrame : Bool) (spec : CompilationModel)
    (fields : List Field) (fuel : Nat) (state : RuntimeState) (data : List UInt8)
    (stmt : Stmt) (rest : List Stmt)
    (failed : SourceStatementEvaluation.execStmtFrame internalFrame spec fields fuel state stmt =
      .revertWithData data) :
    SourceStatementEvaluation.execStmtsFrame internalFrame spec fields (fuel + 1)
      state (stmt :: rest) = .revertWithData data := by
  simp only [SourceStatementEvaluation.execStmtsFrame, failed]

end Compiler.Proofs.IRGeneration.SourceRevertTransport
