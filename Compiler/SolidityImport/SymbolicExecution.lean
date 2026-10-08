import Compiler.SolidityImport.Proofs

/-! Bounded composition of already-proved Denote steps. These rules preserve
complete states and outcomes. They do not unfold expression evaluation or
reduce an imported body in the kernel. -/
namespace Compiler.CompilationModel.SolidityImport.SymbolicExecution
open Compiler.CompilationModel Compiler.CompilationModel.Denote

variable {o : DenoteOracle} {fs : List Field}

/-- Consume exactly one continuing instruction using its established result. -/
theorem step_continue {state next : DenoteState} {stmt : Stmt} {rest : List Stmt}
    (h : execStmt o fs state stmt = .continue next) :
    execStmtList o fs state (stmt :: rest) = execStmtList o fs next rest := by
  simp only [execStmtList, h]

/-- A terminal instruction makes the suffix unreachable, without erasing the
return state, revert bytes, or any other part of the outcome. -/
theorem step_terminal {state : DenoteState} {stmt : Stmt} {rest : List Stmt}
    {outcome : StmtOutcome} (h : execStmt o fs state stmt = outcome)
    (terminal : ∀ next, outcome ≠ .continue next) :
    execStmtList o fs state (stmt :: rest) = outcome := by
  cases outcome with
  | «continue» next => exact False.elim (terminal next rfl)
  | stop next => simp only [execStmtList, h]
  | «return» value next => simp only [execStmtList, h]
  | revert => simp only [execStmtList, h]
  | revertWithData data => simp only [execStmtList, h]

/-- Compose an already-proved bounded block with its remaining suffix. -/
theorem prefix_continue {state next : DenoteState} {pre suffix : List Stmt}
    (h : execStmtList o fs state pre = .continue next) :
    execStmtList o fs state (pre ++ suffix) = execStmtList o fs next suffix := by
  rw [SolidityImport.exec_append, h]

/-- Fail rather than invoke an unbounded simplifier when no matching step is
present. The supplied proof determines the exact transition. -/
macro "denote_step" " using " h:term : tactic =>
  `(tactic| rw [Compiler.CompilationModel.SolidityImport.SymbolicExecution.step_continue $h])

macro "denote_prefix" " using " h:term : tactic =>
  `(tactic| rw [Compiler.CompilationModel.SolidityImport.SymbolicExecution.prefix_continue $h])

end Compiler.CompilationModel.SolidityImport.SymbolicExecution
