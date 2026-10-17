import Compiler.Proofs.IRGeneration.GenericInduction.ResultRelation

/-! Compositional ordinary-outcome admission for actual Source execution.
A trace must discharge each executed step; matching a refusal or an exception
is not a trace constructor and cannot be used as an ordinary EVM certificate. -/
namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel

/-- An ordinary admission records actual head executions and follows the
actual continuation state. Terminal steps do not require unreachable suffixes. -/
inductive OrdinarySourceTrace (fields : List Field) :
    SourceSemantics.RuntimeState → List Stmt → Prop where
  | nil (runtime : SourceSemantics.RuntimeState) : OrdinarySourceTrace fields runtime []
  | continued {runtime final : SourceSemantics.RuntimeState} {stmt : Stmt} {rest : List Stmt}
      (executed : SourceSemantics.execStmt fields runtime stmt = .continue final)
      (tail : OrdinarySourceTrace fields final rest) :
      OrdinarySourceTrace fields runtime (stmt :: rest)
  | stopped {runtime final : SourceSemantics.RuntimeState} {stmt : Stmt} {rest : List Stmt}
      (executed : SourceSemantics.execStmt fields runtime stmt = .stop final) :
      OrdinarySourceTrace fields runtime (stmt :: rest)
  | returned {runtime final : SourceSemantics.RuntimeState} {stmt : Stmt} {rest : List Stmt}
      {value : Nat}
      (executed : SourceSemantics.execStmt fields runtime stmt = .return value final) :
      OrdinarySourceTrace fields runtime (stmt :: rest)
  | reverted {runtime : SourceSemantics.RuntimeState} {stmt : Stmt} {rest : List Stmt}
      (executed : SourceSemantics.execStmt fields runtime stmt = .revert) :
      OrdinarySourceTrace fields runtime (stmt :: rest)
  | revertedWithData {runtime : SourceSemantics.RuntimeState} {stmt : Stmt} {rest : List Stmt}
      {data : List UInt8}
      (executed : SourceSemantics.execStmt fields runtime stmt = .revertWithData data) :
      OrdinarySourceTrace fields runtime (stmt :: rest)

/-- Admission is derived from the actual step equations, including the actual
states after every continued step. No ordinary outcome is postulated. -/
theorem OrdinarySourceTrace.outcome_is_ordinary
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {stmts : List Stmt}
    (trace : OrdinarySourceTrace fields runtime stmts) :
    stmtOutcomeIsOrdinary (SourceSemantics.execStmtList fields runtime stmts) := by
  induction trace with
  | nil => simp only [SourceSemantics.execStmtList, stmtOutcomeIsOrdinary]
  | continued executed _ ih => simp only [SourceSemantics.execStmtList, executed]; exact ih
  | stopped executed => simp only [SourceSemantics.execStmtList, executed, stmtOutcomeIsOrdinary]
  | returned executed => simp only [SourceSemantics.execStmtList, executed, stmtOutcomeIsOrdinary]
  | reverted executed => simp only [SourceSemantics.execStmtList, executed, stmtOutcomeIsOrdinary]
  | revertedWithData executed => simp only [SourceSemantics.execStmtList, executed, stmtOutcomeIsOrdinary]

/-- The unchanged ordinary certificate follows only after actual admission. -/
theorem OrdinarySourceTrace.certify
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {stmts : List Stmt}
    {ir : IRExecResult} (trace : OrdinarySourceTrace fields runtime stmts)
    (matched : stmtOutcomeMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime stmts) ir) :
    FunctionBody.stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime stmts) ir :=
  (stmtOutcomeMatchesIRExec_certified_iff _ _ _).mpr
    ⟨matched, trace.outcome_is_ordinary⟩

theorem OrdinarySourceTrace.excludes_refusal
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {stmts : List Stmt}
    (trace : OrdinarySourceTrace fields runtime stmts) (message : String) :
    SourceSemantics.execStmtList fields runtime stmts ≠ .interpretationError message := by
  intro refused
  have ordinary := trace.outcome_is_ordinary
  rw [refused] at ordinary
  exact ordinary

theorem OrdinarySourceTrace.excludes_exception
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {stmts : List Stmt}
    (trace : OrdinarySourceTrace fields runtime stmts) (terminal : SourceSemantics.RuntimeState) :
    SourceSemantics.execStmtList fields runtime stmts ≠ .exceptional terminal := by
  intro exceptional
  have ordinary := trace.outcome_is_ordinary
  rw [exceptional] at ordinary
  exact ordinary

/-- STOP is an ordinary terminal step; its unreachable suffix need not execute. -/
theorem ordinarySourceTrace_stop (fields : List Field)
    (runtime : SourceSemantics.RuntimeState) (rest : List Stmt) :
    OrdinarySourceTrace fields runtime (.stop :: rest) := .stopped rfl

/-- Bubbling retained bytes is an ordinary REVERT, regardless of payload. -/
theorem ordinarySourceTrace_revertReturndata (fields : List Field)
    (runtime : SourceSemantics.RuntimeState) (rest : List Stmt) :
    OrdinarySourceTrace fields runtime (.revertReturndata :: rest) := .revertedWithData rfl

/-- The retained byte extent discharges actual copy admission. The suffix is
checked at the actual post-copy world, never at the original world. -/
theorem ordinarySourceTrace_returndataCopy
    {fields : List Field} {runtime : SourceSemantics.RuntimeState}
    {destination source size : Expr} {dst src extent : Nat} {rest : List Stmt}
    (destinationValue : SourceSemantics.evalExpr fields runtime destination = some dst)
    (sourceValue : SourceSemantics.evalExpr fields runtime source = some src)
    (sizeValue : SourceSemantics.evalExpr fields runtime size = some extent)
    (inside : src % Verity.Core.Uint256.modulus + extent % Verity.Core.Uint256.modulus ≤
      32 * runtime.world.returndata.length)
    (tail : OrdinarySourceTrace fields
      { runtime with world := (runtime.world.copyPhysicalReturndata
        (dst % Verity.Core.Uint256.modulus) (src % Verity.Core.Uint256.modulus)
        (extent % Verity.Core.Uint256.modulus)) } rest) :
    OrdinarySourceTrace fields runtime (.returndataCopy destination source size :: rest) := by
  apply OrdinarySourceTrace.continued (final := { runtime with world := (runtime.world.copyPhysicalReturndata
      (dst % Verity.Core.Uint256.modulus) (src % Verity.Core.Uint256.modulus)
      (extent % Verity.Core.Uint256.modulus)) }) ?_ tail
  simp only [SourceSemantics.execStmt, destinationValue, sourceValue, sizeValue,
    SourceSemantics.execReturndataCopy,
    Verity.Core.Model.ReturndataCopy.run_in_bounds _ _ _ _ _ inside]

/-- A nearby out-of-bounds copy with missing context cannot be certified by
an ordinary trace, even if both interpreters produce the same refusal. -/
theorem no_ordinarySourceTrace_returndataCopy_missing_context
    {fields : List Field} {runtime : SourceSemantics.RuntimeState}
    {destination source size : Expr} {dst src extent : Nat} {rest : List Stmt}
    (destinationValue : SourceSemantics.evalExpr fields runtime destination = some dst)
    (sourceValue : SourceSemantics.evalExpr fields runtime source = some src)
    (sizeValue : SourceSemantics.evalExpr fields runtime size = some extent)
    (missing : runtime.executionContext = none)
    (outside : 32 * runtime.world.returndata.length <
      src % Verity.Core.Uint256.modulus + extent % Verity.Core.Uint256.modulus) :
    ¬ OrdinarySourceTrace fields runtime (.returndataCopy destination source size :: rest) := by
  intro trace
  apply trace.excludes_refusal "returndata copy exceptional exit requires actual opcode context"
  simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt,
    destinationValue, sourceValue, sizeValue, SourceSemantics.execReturndataCopy, missing,
    Verity.Core.Model.ReturndataCopy.run_missing_context _ _ _ _ outside,
    String.empty_append]

/-- Recover the actual step trace from an established ordinary execution.
This is useful for transporting a trace across a proved semantics equality. -/
theorem OrdinarySourceTrace.of_ordinary_outcome
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {stmts : List Stmt}
    (ordinary : stmtOutcomeIsOrdinary (SourceSemantics.execStmtList fields runtime stmts)) :
    OrdinarySourceTrace fields runtime stmts := by
  induction stmts generalizing runtime with
  | nil => exact .nil runtime
  | cons stmt rest ih =>
      cases head : SourceSemantics.execStmt fields runtime stmt with
      | «continue» next =>
          apply OrdinarySourceTrace.continued head
          apply ih
          simpa only [SourceSemantics.execStmtList, head] using ordinary
      | stop next => exact .stopped head
      | «return» value next => exact .returned head
      | revert => exact .reverted head
      | revertWithData data => exact .revertedWithData head
      | interpretationError message =>
          simp only [SourceSemantics.execStmtList, head, stmtOutcomeIsOrdinary] at ordinary
      | exceptional next =>
          simp only [SourceSemantics.execStmtList, head, stmtOutcomeIsOrdinary] at ordinary

end Compiler.Proofs.IRGeneration
