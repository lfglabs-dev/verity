import Compiler.Proofs.IRGeneration.CustomErrorMemoryFrame
import Compiler.Proofs.IRGeneration.NonReentrantGuardIR

namespace Compiler.Proofs.IRGeneration.CustomErrorContinuation
open Compiler.CompilationModel Compiler.Yul SourceSemantics IRMemoryCoherence

/-- Source helper fuel belongs to helper evaluation, not list traversal. -/
theorem source_append_continue (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (state next : RuntimeState) (pre suffix : List Stmt)
    (executed : execStmtListWithHelpers spec fields fuel state pre = .continue next) :
    execStmtListWithHelpers spec fields fuel state (pre ++ suffix) =
      execStmtListWithHelpers spec fields fuel next suffix := by
  induction pre generalizing state with
  | nil =>
      simp only [execStmtListWithHelpers] at executed
      cases executed
      rfl
  | cons stmt rest ih =>
      cases step : execStmtWithHelpers spec fields fuel state stmt <;>
        simp only [List.cons_append, execStmtListWithHelpers, step] at executed ⊢
      case «continue» middle => exact ih middle executed
      all_goals cases executed

/-- Derive declarations and coherence from both actual pre executions.
The pointer-frame premise must come from the pre's physical frame proof;
it replaces neither allocation checks nor a new-pointer extent proof. -/
theorem after_prefix (spec : CompilationModel) (fields : List Field)
    (helperFuel irFuel : Nat) (runtime next : RuntimeState) (state nextIR : IRState)
    (pre : List Stmt) (prefixIR : List YulStmt)
    (domain : CustomErrorDomain spec runtime state) (initial : Coherent state)
    (source : execStmtListWithHelpers spec fields helperFuel runtime pre = .continue next)
    (compiled : execIRStmts irFuel state prefixIR = .continue nextIR)
    (pointer : nextIR.memory freeMemoryPointer = state.memory freeMemoryPointer) :
    CustomErrorDomain spec next nextIR ∧ Coherent nextIR := by
  refine ⟨⟨SourceErrorDeclarations.helper_continuation_declarations spec fields helperFuel runtime next pre
    domain.declarations source, ?_⟩, ?_⟩
  · intro definition member
    rw [pointer]
    exact domain.extents definition member
  · have kept := (executors irFuel).2 state prefixIR initial
    simpa only [compiled, Preserves] using kept

private theorem source_singleton (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (state : RuntimeState) (stmt : Stmt) :
    execStmtListWithHelpers spec fields fuel state [stmt] =
      execStmtWithHelpers spec fields fuel state stmt := by
  simp only [execStmtListWithHelpers]
  cases execStmtWithHelpers spec fields fuel state stmt <;> rfl

/-- Compose a real continuing pre with a domain-admitted error step. The
remaining IR fuel is checked exactly after pre list traversal. -/
theorem prefix_then_error (spec : CompilationModel) (fields : List Field)
    (scope : List String) (stmt : Stmt) (out : List YulStmt) (minimum : Nat)
    (step : CompiledErrorStepWithin spec fields scope stmt out minimum)
    (helperFuel irFuel extraFuel : Nat) (runtime next : RuntimeState) (state nextIR : IRState)
    (pre : List Stmt) (prefixIR : List YulStmt)
    (domain : CustomErrorDomain spec runtime state) (initial : Coherent state)
    (source : execStmtListWithHelpers spec fields helperFuel runtime pre = .continue next)
    (compiled : execIRStmts irFuel state prefixIR = .continue nextIR)
    (pointer : nextIR.memory freeMemoryPointer = state.memory freeMemoryPointer)
    (enough : minimum ≤ extraFuel)
    (remaining : irFuel - prefixIR.length = out.length + extraFuel + 1) :
    ∃ sourceResult irExec,
      execStmtListWithHelpers spec fields helperFuel runtime (pre ++ [stmt]) = sourceResult ∧
      execIRStmts irFuel state (prefixIR ++ out) = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope stmt) sourceResult irExec := by
  have admitted := after_prefix spec fields helperFuel irFuel runtime next state nextIR
    pre prefixIR domain initial source compiled pointer
  obtain ⟨sourceResult, irExec, sourceStep, irStep, relation⟩ :=
    step.preserves next nextIR helperFuel extraFuel admitted.1 enough
  refine ⟨sourceResult, irExec, ?_, ?_, relation⟩
  · rw [source_append_continue spec fields helperFuel runtime next pre [stmt] source,
      source_singleton, sourceStep]
  · rw [execIRStmts_append_continue out prefixIR irFuel state nextIR compiled,
      remaining, irStep]

end Compiler.Proofs.IRGeneration.CustomErrorContinuation
