import Compiler.Proofs.IRGeneration.SupportedFragment
import Compiler.Proofs.IRGeneration.GenericInduction.OrdinaryHelperTrace
import Compiler.Proofs.IRGeneration.GenericInduction.OrdinaryTrace

namespace Compiler.Proofs.IRGeneration.EventOrdinary
open Compiler.CompilationModel SourceSemantics Verity.Core.Free

/-- Only the actual continued prefix executes the suffix. -/
theorem ordinary_list_cons (fields : List Field) (events : List EventDef) (state : RuntimeState)
    (stmt : Stmt) (rest : List Stmt)
    (head : stmtOutcomeIsOrdinary (execStmtWithEvents fields events state stmt))
    (tail : ∀ next, stmtOutcomeIsOrdinary (execStmtListWithEvents fields events next rest)) :
    stmtOutcomeIsOrdinary (execStmtListWithEvents fields events state (stmt :: rest)) := by
  cases executed : execStmtWithEvents fields events state stmt <;>
    simp only [execStmtListWithEvents, executed, stmtOutcomeIsOrdinary] at head ⊢
  all_goals exact tail _

theorem compile_core_ordinary {scope : List String} {stmts : List Stmt}
    (supported : FunctionBody.StmtListCompileCore scope stmts)
    (fields : List Field) (events : List EventDef) (state : RuntimeState) :
    stmtOutcomeIsOrdinary (execStmtListWithEvents fields events state stmts) := by
  induction supported generalizing state with
  | nil => trivial
  | _ =>
    apply ordinary_list_cons
    · simp only [execStmtWithEvents]
      all_goals repeat' first | split | (solve | trivial)
    · intro next
      apply_assumption

theorem terminal_core_ordinary {scope : List String} {stmts : List Stmt}
    (supported : FunctionBody.StmtListTerminalCore scope stmts)
    (fields : List Field) (events : List EventDef) (state : RuntimeState) :
    stmtOutcomeIsOrdinary (execStmtListWithEvents fields events state stmts) := by
  induction supported generalizing state with
  | ite _ _ yes no rest ihYes ihNo =>
      apply ordinary_list_cons
      · simp only [execStmtWithEvents]
        split
        · split
          · exact ihYes state
          · exact ihNo state
        · trivial
      · exact fun next => compile_core_ordinary rest fields events next
  | return_ _ _ rest =>
      apply ordinary_list_cons
      · simp only [execStmtWithEvents]; split <;> trivial
      · exact fun next => compile_core_ordinary rest fields events next
  | stop rest =>
      apply ordinary_list_cons
      · trivial
      · exact fun next => compile_core_ordinary rest fields events next
  | _ =>
      apply ordinary_list_cons
      · simp only [execStmtWithEvents]
        all_goals repeat' first | split | (solve | trivial)
      · intro next
        apply_assumption

/-- Ordinary prefix execution and every possible continuation admit append. -/
theorem ordinary_list_append (fields : List Field) (events : List EventDef) (state : RuntimeState)
    (pfx sfx : List Stmt)
    (head : stmtOutcomeIsOrdinary (execStmtListWithEvents fields events state pfx))
    (tail : ∀ next, stmtOutcomeIsOrdinary (execStmtListWithEvents fields events next sfx)) :
    stmtOutcomeIsOrdinary (execStmtListWithEvents fields events state (pfx ++ sfx)) := by
  induction pfx generalizing state with
  | nil => exact tail state
  | cons stmt rest ih =>
      cases executed : execStmtWithEvents fields events state stmt <;>
        simp only [execStmtListWithEvents, executed, stmtOutcomeIsOrdinary] at head
      all_goals simp only [List.cons_append, execStmtListWithEvents, executed, stmtOutcomeIsOrdinary]
      all_goals exact ih _ head

theorem empty_loop_ordinary (fields : List Field) (events : List EventDef) (name : String)
    (state : RuntimeState) (index remaining : Nat) :
    stmtOutcomeIsOrdinary (execForEachLoop name (fun next => execStmtListWithEvents fields events next []) state index remaining) := by
  induction remaining generalizing state index with
  | zero => trivial
  | succ remaining ih =>
      simp only [execForEachLoop, execStmtListWithEvents]
      exact ih _ _

/-- The full supported grammar excludes exceptional/refused Source bodies.
This proves the obligation rather than adding it to compiler correctness. -/
theorem SupportedStmtList.outcome_is_ordinary {fields : List Field}
    {scope : List String} {stmts : List Stmt}
    (supported : SupportedStmtList fields scope stmts) (events : List EventDef) (state : RuntimeState) :
    stmtOutcomeIsOrdinary (execStmtListWithEvents fields events state stmts) := by
  induction supported generalizing state with
  | compileCore core => exact compile_core_ordinary core fields events state
  | terminalCore core => exact terminal_core_ordinary core fields events state
  | append _ _ ihPfx ihSfx => exact ordinary_list_append fields events state _ _ (ihPfx state) ihSfx
  | iteTerminal _ _ yes no =>
      apply ordinary_list_cons
      · simp only [execStmtWithEvents]
        split
        · split
          · exact terminal_core_ordinary yes fields events state
          · exact terminal_core_ordinary no fields events state
        · trivial
      · intro next; trivial
  | forEachLiteralEmpty n =>
      apply ordinary_list_cons
      · simp only [execStmtWithEvents, evalExpr]
        exact empty_loop_ordinary fields events _ _ _ _
      · intro next; trivial
  | @returndataCopyEmptySingle scope destOffset _ _ =>
      apply ordinary_list_cons
      · cases evaluated : evalExpr fields state destOffset <;>
          simp [execStmtWithEvents, evalExpr, evaluated, execReturndataCopy,
            Verity.Core.Model.ReturndataCopy.run, wordNormalize, stmtOutcomeIsOrdinary]
      · intro next; trivial
  | requireClause clause _ ih =>
      apply ordinary_list_cons
      · simp only [RequireLiteralGuardFamilyClause.toStmt, execStmtWithEvents]
        all_goals repeat' first | split | (solve | trivial)
      · exact ih
  | _ =>
      apply ordinary_list_cons
      · simp only [execStmtWithEvents, evalExpr]
        all_goals repeat' first | split | (solve | simp [stmtOutcomeIsOrdinary, wordNormalize])
      · intro next; trivial

end Compiler.Proofs.IRGeneration.EventOrdinary

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel SourceSemantics

/-- Eventful supported programs derive helper admission from their actual
catalog-aware execution; no event-free or ordinary-outcome premise is added. -/
theorem SupportedStmtList.ordinary_helper_trace_with_events {fields : List Field}
    {scope : List String} {stmts : List Stmt}
    (supported : SupportedStmtList fields scope stmts)
    (spec : CompilationModel) (fuel : Nat) (state : RuntimeState)
    (closed : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    OrdinaryHelperTrace spec fields fuel state stmts := by
  apply OrdinaryHelperTrace.of_ordinary_outcome
  rw [execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed spec fields fuel state stmts closed]
  exact EventOrdinary.SupportedStmtList.outcome_is_ordinary supported spec.events state

end Compiler.Proofs.IRGeneration
