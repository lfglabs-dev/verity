import Verity.Core.Model.Denote

/-! Public equations for actual canonical CREATE2 statement dispatch. These
preserve interpreter errors and exhausted exceptional frames rather than
substituting an external-call receipt or reporting unsupported code as revert. -/
namespace Compiler.CompilationModel.Denote
open Compiler.CompilationModel

theorem execStmt_create2 (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (destination : String) (offset size salt : Expr) :
    execStmt oracle fields state (.create2 destination offset size salt) =
      execCreation oracle fields state destination offset size salt := rfl

theorem execCreation_missing_context (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (destination : String) (offset size salt : Expr) (o n s : Nat)
    (resolved : evalExprList oracle fields state [offset, size, salt] = some [o,n,s])
    (missing : state.executionContext = none) :
    execCreation oracle fields state destination offset size salt =
      .interpretationError "CREATE2 requires an actual opcode-entry execution context" := by
  simp only [execCreation, resolved, missing]

theorem execCreation_arguments_fail (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (destination : String) (offset size salt : Expr)
    (failed : evalExprList oracle fields state [offset, size, salt] = none) :
    execCreation oracle fields state destination offset size salt =
      .interpretationError "CREATE2 argument evaluation failed" := by
  simp only [execCreation, failed]

theorem execStmtList_interpretationError (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (stmt : Stmt) (rest : List Stmt) (message : String)
    (failed : execStmt oracle fields state stmt = .interpretationError message) :
    execStmtList oracle fields state (stmt :: rest) = .interpretationError message := by
  simp only [execStmtList, failed]

theorem execStmtList_exceptional (oracle : DenoteOracle) (fields : List Field)
    (state next : DenoteState) (stmt : Stmt) (rest : List Stmt)
    (failed : execStmt oracle fields state stmt = .exceptional next) :
    execStmtList oracle fields state (stmt :: rest) = .exceptional next := by
  simp only [execStmtList, failed]

end Compiler.CompilationModel.Denote
