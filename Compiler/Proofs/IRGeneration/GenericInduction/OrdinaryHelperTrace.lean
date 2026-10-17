import Compiler.Proofs.IRGeneration.GenericInduction.ResultRelation

/-! Compositional ordinary-outcome admission for actual Source execution.
A trace must discharge each executed step; matching a refusal or an exception
is not a trace constructor and cannot be used as an ordinary EVM certificate. -/
namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel

/-- An ordinary admission records actual head executions and follows the
actual continuation state. Terminal steps do not require unreachable suffixes. -/
inductive OrdinaryHelperTrace (spec : CompilationModel) (fields : List Field) (fuel : Nat) :
    SourceSemantics.RuntimeState → List Stmt → Prop where
  | nil (runtime : SourceSemantics.RuntimeState) : OrdinaryHelperTrace spec fields fuel runtime []
  | continued {runtime final : SourceSemantics.RuntimeState} {stmt : Stmt} {rest : List Stmt}
      (executed : SourceSemantics.execStmtWithHelpers spec fields fuel runtime stmt = .continue final)
      (tail : OrdinaryHelperTrace spec fields fuel final rest) :
      OrdinaryHelperTrace spec fields fuel runtime (stmt :: rest)
  | stopped {runtime final : SourceSemantics.RuntimeState} {stmt : Stmt} {rest : List Stmt}
      (executed : SourceSemantics.execStmtWithHelpers spec fields fuel runtime stmt = .stop final) :
      OrdinaryHelperTrace spec fields fuel runtime (stmt :: rest)
  | returned {runtime final : SourceSemantics.RuntimeState} {stmt : Stmt} {rest : List Stmt}
      {value : Nat}
      (executed : SourceSemantics.execStmtWithHelpers spec fields fuel runtime stmt = .return value final) :
      OrdinaryHelperTrace spec fields fuel runtime (stmt :: rest)
  | reverted {runtime : SourceSemantics.RuntimeState} {stmt : Stmt} {rest : List Stmt}
      (executed : SourceSemantics.execStmtWithHelpers spec fields fuel runtime stmt = .revert) :
      OrdinaryHelperTrace spec fields fuel runtime (stmt :: rest)
  | revertedWithData {runtime : SourceSemantics.RuntimeState} {stmt : Stmt} {rest : List Stmt}
      {data : List UInt8}
      (executed : SourceSemantics.execStmtWithHelpers spec fields fuel runtime stmt = .revertWithData data) :
      OrdinaryHelperTrace spec fields fuel runtime (stmt :: rest)

/-- Admission is derived from the actual step equations, including the actual
states after every continued step. No ordinary outcome is postulated. -/
theorem OrdinaryHelperTrace.outcome_is_ordinary
    {spec : CompilationModel} {fields : List Field} {fuel : Nat} {runtime : SourceSemantics.RuntimeState} {stmts : List Stmt}
    (trace : OrdinaryHelperTrace spec fields fuel runtime stmts) :
    stmtOutcomeIsOrdinary (SourceSemantics.execStmtListWithHelpers spec fields fuel runtime stmts) := by
  induction trace with
  | nil => simp only [SourceSemantics.execStmtListWithHelpers, stmtOutcomeIsOrdinary]
  | continued executed _ ih => simp only [SourceSemantics.execStmtListWithHelpers, executed]; exact ih
  | stopped executed => simp only [SourceSemantics.execStmtListWithHelpers, executed, stmtOutcomeIsOrdinary]
  | returned executed => simp only [SourceSemantics.execStmtListWithHelpers, executed, stmtOutcomeIsOrdinary]
  | reverted executed => simp only [SourceSemantics.execStmtListWithHelpers, executed, stmtOutcomeIsOrdinary]
  | revertedWithData executed => simp only [SourceSemantics.execStmtListWithHelpers, executed, stmtOutcomeIsOrdinary]

/-- The unchanged ordinary certificate follows only after actual admission. -/
theorem OrdinaryHelperTrace.certify
    {spec : CompilationModel} {fields : List Field} {fuel : Nat} {runtime : SourceSemantics.RuntimeState} {stmts : List Stmt}
    {ir : IRExecResult} (trace : OrdinaryHelperTrace spec fields fuel runtime stmts)
    (matched : stmtOutcomeMatchesIRExec fields
      (SourceSemantics.execStmtListWithHelpers spec fields fuel runtime stmts) ir) :
    FunctionBody.stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtListWithHelpers spec fields fuel runtime stmts) ir :=
  (stmtOutcomeMatchesIRExec_certified_iff _ _ _).mpr
    ⟨matched, trace.outcome_is_ordinary⟩

theorem OrdinaryHelperTrace.excludes_refusal
    {spec : CompilationModel} {fields : List Field} {fuel : Nat} {runtime : SourceSemantics.RuntimeState} {stmts : List Stmt}
    (trace : OrdinaryHelperTrace spec fields fuel runtime stmts) (message : String) :
    SourceSemantics.execStmtListWithHelpers spec fields fuel runtime stmts ≠ .interpretationError message := by
  intro refused
  have ordinary := trace.outcome_is_ordinary
  rw [refused] at ordinary
  exact ordinary

theorem OrdinaryHelperTrace.excludes_exception
    {spec : CompilationModel} {fields : List Field} {fuel : Nat} {runtime : SourceSemantics.RuntimeState} {stmts : List Stmt}
    (trace : OrdinaryHelperTrace spec fields fuel runtime stmts) (terminal : SourceSemantics.RuntimeState) :
    SourceSemantics.execStmtListWithHelpers spec fields fuel runtime stmts ≠ .exceptional terminal := by
  intro exceptional
  have ordinary := trace.outcome_is_ordinary
  rw [exceptional] at ordinary
  exact ordinary


/-- The actual helper trace also discharges the internal-call IR certificate. -/
theorem OrdinaryHelperTrace.certify_with_internals
    {spec : CompilationModel} {fields : List Field} {fuel : Nat}
    {runtime : SourceSemantics.RuntimeState} {stmts : List Stmt}
    {ir : IRExecResultWithInternals} (trace : OrdinaryHelperTrace spec fields fuel runtime stmts)
    (matched : stmtOutcomeMatchesIRExecWithInternals fields
      (SourceSemantics.execStmtListWithHelpers spec fields fuel runtime stmts) ir) :
    stmtResultMatchesIRExecWithInternals fields
      (SourceSemantics.execStmtListWithHelpers spec fields fuel runtime stmts) ir :=
  (stmtOutcomeMatchesIRExecWithInternals_certified_iff _ _ _).mpr
    ⟨matched, trace.outcome_is_ordinary⟩

/-- Recover the actual step trace from an established ordinary execution.
This is useful for transporting a trace across a proved semantics equality. -/
theorem OrdinaryHelperTrace.of_ordinary_outcome
    {spec : CompilationModel} {fields : List Field} {fuel : Nat} {runtime : SourceSemantics.RuntimeState} {stmts : List Stmt}
    (ordinary : stmtOutcomeIsOrdinary (SourceSemantics.execStmtListWithHelpers spec fields fuel runtime stmts)) :
    OrdinaryHelperTrace spec fields fuel runtime stmts := by
  induction stmts generalizing runtime with
  | nil => exact .nil runtime
  | cons stmt rest ih =>
      cases head : SourceSemantics.execStmtWithHelpers spec fields fuel runtime stmt with
      | «continue» next =>
          apply OrdinaryHelperTrace.continued head
          apply ih
          simpa only [SourceSemantics.execStmtListWithHelpers, head] using ordinary
      | stop next => exact .stopped head
      | «return» value next => exact .returned head
      | revert => exact .reverted head
      | revertWithData data => exact .revertedWithData head
      | interpretationError message =>
          simp only [SourceSemantics.execStmtListWithHelpers, head, stmtOutcomeIsOrdinary] at ordinary
      | exceptional next =>
          simp only [SourceSemantics.execStmtListWithHelpers, head, stmtOutcomeIsOrdinary] at ordinary

end Compiler.Proofs.IRGeneration
