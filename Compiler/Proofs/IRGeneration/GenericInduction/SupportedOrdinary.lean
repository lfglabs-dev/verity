import Compiler.Proofs.IRGeneration.SupportedFragment
import Compiler.Proofs.IRGeneration.GenericInduction.OrdinaryHelperTrace
import Compiler.Proofs.IRGeneration.GenericInduction.OrdinaryTrace

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel SourceSemantics Verity.Core.Free

/-- Only the actual continued prefix executes the suffix. -/
theorem ordinary_list_cons (fields : List Field) (state : RuntimeState)
    (stmt : Stmt) (rest : List Stmt)
    (head : stmtOutcomeIsOrdinary (execStmt fields state stmt))
    (tail : ∀ next, stmtOutcomeIsOrdinary (execStmtList fields next rest)) :
    stmtOutcomeIsOrdinary (execStmtList fields state (stmt :: rest)) := by
  cases executed : execStmt fields state stmt <;>
    simp only [execStmtList, executed, stmtOutcomeIsOrdinary] at head ⊢
  all_goals exact tail _

theorem compile_core_ordinary {scope : List String} {stmts : List Stmt}
    (supported : FunctionBody.StmtListCompileCore scope stmts)
    (fields : List Field) (state : RuntimeState) :
    stmtOutcomeIsOrdinary (execStmtList fields state stmts) := by
  induction supported generalizing state with
  | nil => trivial
  | _ =>
    apply ordinary_list_cons
    · simp only [execStmt]
      all_goals repeat' first | split | (solve | trivial)
    · intro next
      apply_assumption

theorem terminal_core_ordinary {scope : List String} {stmts : List Stmt}
    (supported : FunctionBody.StmtListTerminalCore scope stmts)
    (fields : List Field) (state : RuntimeState) :
    stmtOutcomeIsOrdinary (execStmtList fields state stmts) := by
  induction supported generalizing state with
  | ite _ _ yes no rest ihYes ihNo =>
      apply ordinary_list_cons
      · simp only [execStmt]
        split
        · split
          · exact ihYes state
          · exact ihNo state
        · trivial
      · exact fun next => compile_core_ordinary rest fields next
  | return_ _ _ rest =>
      apply ordinary_list_cons
      · simp only [execStmt]; split <;> trivial
      · exact fun next => compile_core_ordinary rest fields next
  | stop rest =>
      apply ordinary_list_cons
      · trivial
      · exact fun next => compile_core_ordinary rest fields next
  | _ =>
      apply ordinary_list_cons
      · simp only [execStmt]
        all_goals repeat' first | split | (solve | trivial)
      · intro next
        apply_assumption

/-- Ordinary prefix execution and every possible continuation admit append. -/
theorem ordinary_list_append (fields : List Field) (state : RuntimeState)
    (pfx sfx : List Stmt)
    (head : stmtOutcomeIsOrdinary (execStmtList fields state pfx))
    (tail : ∀ next, stmtOutcomeIsOrdinary (execStmtList fields next sfx)) :
    stmtOutcomeIsOrdinary (execStmtList fields state (pfx ++ sfx)) := by
  induction pfx generalizing state with
  | nil => exact tail state
  | cons stmt rest ih =>
      cases executed : execStmt fields state stmt <;>
        simp only [execStmtList, executed, stmtOutcomeIsOrdinary] at head
      all_goals simp only [List.cons_append, execStmtList, executed, stmtOutcomeIsOrdinary]
      all_goals exact ih _ head

theorem empty_loop_ordinary (fields : List Field) (name : String)
    (state : RuntimeState) (index remaining : Nat) :
    stmtOutcomeIsOrdinary (execForEachLoop name (fun next => execStmtList fields next []) state index remaining) := by
  induction remaining generalizing state index with
  | zero => trivial
  | succ remaining ih =>
      simp only [execForEachLoop, execStmtList]
      exact ih _ _

/-- The full supported grammar excludes exceptional/refused Source bodies.
This proves the obligation rather than adding it to compiler correctness. -/
theorem SupportedStmtList.outcome_is_ordinary {fields : List Field}
    {scope : List String} {stmts : List Stmt}
    (supported : SupportedStmtList fields scope stmts) (state : RuntimeState) :
    stmtOutcomeIsOrdinary (execStmtList fields state stmts) := by
  induction supported generalizing state with
  | compileCore core => exact compile_core_ordinary core fields state
  | terminalCore core => exact terminal_core_ordinary core fields state
  | append _ _ ihPfx ihSfx => exact ordinary_list_append fields state _ _ (ihPfx state) ihSfx
  | iteTerminal _ _ yes no =>
      apply ordinary_list_cons
      · simp only [execStmt]
        split
        · split
          · exact terminal_core_ordinary yes fields state
          · exact terminal_core_ordinary no fields state
        · trivial
      · intro next; trivial
  | forEachLiteralEmpty n =>
      apply ordinary_list_cons
      · simp only [execStmt, evalExpr]
        exact empty_loop_ordinary fields _ _ _ _
      · intro next; trivial
  | @returndataCopyEmptySingle scope destOffset _ _ =>
      apply ordinary_list_cons
      · cases evaluated : evalExpr fields state destOffset <;>
          simp [execStmt, evalExpr, evaluated, execReturndataCopy,
            Verity.Core.Model.ReturndataCopy.run, wordNormalize, stmtOutcomeIsOrdinary]
      · intro next; trivial
  | requireClause clause _ ih =>
      apply ordinary_list_cons
      · simp only [RequireLiteralGuardFamilyClause.toStmt, execStmt]
        all_goals repeat' first | split | (solve | trivial)
      · exact ih
  | _ =>
      apply ordinary_list_cons
      · simp only [execStmt, evalExpr]
        all_goals repeat' first | split | (solve | simp [stmtOutcomeIsOrdinary, wordNormalize])
      · intro next; trivial

/-- Derive actual helper admission through the proved conservative extension.
The event-free condition is the existing caller domain, not a trace premise. -/
theorem SupportedStmtList.ordinary_helper_trace {fields : List Field}
    {scope : List String} {stmts : List Stmt}
    (supported : SupportedStmtList fields scope stmts)
    (spec : CompilationModel) (fuel : Nat) (state : RuntimeState)
    (closed : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (noEvents : spec.events = []) :
    OrdinaryHelperTrace spec fields fuel state stmts := by
  apply OrdinaryHelperTrace.of_ordinary_outcome
  rw [execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed spec fields fuel state stmts closed,
    noEvents, execStmtListWithEvents_nil_eq_execStmtList]
  exact supported.outcome_is_ordinary state

end Compiler.Proofs.IRGeneration
