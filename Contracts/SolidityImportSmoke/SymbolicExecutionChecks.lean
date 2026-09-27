import Compiler.SolidityImport.SymbolicExecution

namespace Compiler.CompilationModel.SolidityImport.SymbolicExecution.Checks
open Compiler.CompilationModel Compiler.CompilationModel.Denote

/-- Composition preserves an arbitrary suffix and the entire intermediate state. -/
theorem two_steps (o : DenoteOracle) (fs : List Field)
    (initial middle final : DenoteState) (first second : Stmt) (suffix : List Stmt)
    (hfirst : execStmt o fs initial first = .continue middle)
    (hsecond : execStmt o fs middle second = .continue final) :
    execStmtList o fs initial (first :: second :: suffix) =
      execStmtList o fs final suffix := by
  denote_step using hfirst
  denote_step using hsecond

/-- An already checked block can be followed by another checked step. -/
theorem prefix_then_step (o : DenoteOracle) (fs : List Field)
    (initial middle final : DenoteState) (pre : List Stmt)
    (stmt : Stmt) (suffix : List Stmt)
    (hp : execStmtList o fs initial pre = .continue middle)
    (hs : execStmt o fs middle stmt = .continue final) :
    execStmtList o fs initial (pre ++ (stmt :: suffix)) =
      execStmtList o fs final suffix := by
  denote_prefix using hp
  denote_step using hs

/-- No evaluation of the suffix is necessary after a terminal instruction. -/
theorem stop_skips_suffix (o : DenoteOracle) (fs : List Field)
    (initial final : DenoteState) (stmt : Stmt) (suffix : List Stmt)
    (h : execStmt o fs initial stmt = .stop final) :
    execStmtList o fs initial (stmt :: suffix) = .stop final := by
  exact step_terminal h (by intro next impossible; cases impossible)

/-- The byte list is retained exactly, not projected to a boolean failure. -/
theorem revert_keeps_payload (o : DenoteOracle) (fs : List Field)
    (initial : DenoteState) (stmt : Stmt) (suffix : List Stmt) (bytes : List UInt8)
    (h : execStmt o fs initial stmt = .revertWithData bytes) :
    execStmtList o fs initial (stmt :: suffix) = .revertWithData bytes := by
  exact step_terminal h (by intro next impossible; cases impossible)

/-- A lemma about STOP cannot be used as a continuing transition. -/
theorem rejects_terminal_step (o : DenoteOracle) (fs : List Field)
    (initial final : DenoteState) (stmt : Stmt) (suffix : List Stmt)
    (h : execStmt o fs initial stmt = .stop final) :
    execStmtList o fs initial (stmt :: suffix) = .stop final := by
  fail_if_success denote_step using h
  exact stop_skips_suffix o fs initial final stmt suffix h

/-- A concrete instruction sequence, with an arbitrary input state and value.
The arbitrary suffix is unreachable and all other state fields are retained. -/
theorem bind_then_stop (o : DenoteOracle) (fs : List Field)
    (initial : DenoteState) (value : Nat) (suffix : List Stmt) :
    execStmtList o fs initial (.letVar "saved" (.literal value) :: .stop :: suffix) =
      .stop { initial with
        bindings := bindValue initial.bindings "saved" (wordNormalize value)
        observedStop := true } := by
  let next : DenoteState := { initial with
    bindings := bindValue initial.bindings "saved" (wordNormalize value) }
  have first : execStmt o fs initial (.letVar "saved" (.literal value)) =
      .continue next := rfl
  denote_step using first
  exact step_terminal
    (show execStmt o fs next .stop = .stop { next with observedStop := true } from rfl)
    (by intro state impossible; cases impossible)

end Compiler.CompilationModel.SolidityImport.SymbolicExecution.Checks
