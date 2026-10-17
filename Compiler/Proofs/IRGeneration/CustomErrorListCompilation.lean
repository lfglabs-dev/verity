import Compiler.Proofs.IRGeneration.CustomErrorContinuation

namespace Compiler.Proofs.IRGeneration.CustomErrorListCompilation
open Compiler.CompilationModel Compiler.Yul SourceSemantics IRMemoryCoherence

/-- Actual compiler concatenation, including its accumulated binder scope. -/
theorem compiled_append (spec : CompilationModel) (fields : List Field)
    (scope : List String) (pre post : List Stmt) (preIR postIR : List YulStmt)
    (first : compileStmtList fields spec.events spec.errors .calldata [] false scope [] pre = .ok preIR)
    (second : compileStmtList fields spec.events spec.errors .calldata [] false
      (pre.foldl (fun names stmt => collectStmtBindNames stmt ++ names) scope) [] post = .ok postIR) :
    compileStmtList fields spec.events spec.errors .calldata [] false scope [] (pre ++ post) =
      .ok (preIR ++ postIR) := by
  simp only [compileStmtList] at first second ⊢
  induction pre generalizing scope preIR with
  | nil =>
      simp only [compileStmtListWithFork, pure, Except.pure] at first
      cases first
      exact second
  | cons stmt rest ih =>
      cases head : compileStmtWithFork fields spec.events spec.errors .calldata [] false scope []
          .cancun stmt [] with
      | error message =>
          simp [compileStmtListWithFork, head, Bind.bind, Except.bind] at first
      | ok headIR =>
          cases tail : compileStmtListWithFork fields spec.events spec.errors .calldata [] false
              (collectStmtBindNames stmt ++ scope) [] .cancun rest [] with
          | error message =>
              simp [compileStmtListWithFork, head, tail, Bind.bind, Except.bind] at first
          | ok tailIR =>
              have firstEq : headIR ++ tailIR = preIR := by
                simpa [compileStmtListWithFork, head, tail,
                  Bind.bind, Except.bind, pure, Except.pure] using first
              subst preIR
              have remaining := ih (collectStmtBindNames stmt ++ scope) tailIR tail second
              simpa [compileStmtListWithFork, head, remaining,
                Bind.bind, Except.bind, pure, Except.pure, List.append_assoc]

/-- The suffix compiler identity is supplied by the actual error-step witness. -/
theorem compiled_error_singleton (spec : CompilationModel) (fields : List Field)
    (scope : List String) (stmt : Stmt) (out : List YulStmt) (minimum : Nat)
    (step : CompiledErrorStepWithin spec fields scope stmt out minimum) :
    compileStmtList fields spec.events spec.errors .calldata [] false scope [] [stmt] = .ok out := by
  have compiled := step.compileOk
  simp only [compileStmt] at compiled
  simp [compileStmtList, compileStmtListWithFork, compiled,
    Bind.bind, Except.bind, pure, Except.pure]

/-- Compiler identity and exact execution for an error-ending list. The error
step is compiled in the scope actually accumulated by the Source prefix. -/
theorem compiled_prefix_then_error (spec : CompilationModel) (fields : List Field)
    (scope : List String) (pre : List Stmt) (preIR : List YulStmt)
    (stmt : Stmt) (out : List YulStmt) (minimum : Nat)
    (step : CompiledErrorStepWithin spec fields
      (pre.foldl (fun names stmt => collectStmtBindNames stmt ++ names) scope) stmt out minimum)
    (first : compileStmtList fields spec.events spec.errors .calldata [] false scope [] pre = .ok preIR)
    (helperFuel irFuel extraFuel : Nat) (runtime next : RuntimeState) (state nextIR : IRState)
    (domain : CustomErrorDomain spec runtime state) (initial : Coherent state)
    (source : execStmtListWithHelpers spec fields helperFuel runtime pre = .continue next)
    (executed : execIRStmts irFuel state preIR = .continue nextIR)
    (pointer : nextIR.memory freeMemoryPointer = state.memory freeMemoryPointer)
    (enough : minimum ≤ extraFuel)
    (remaining : irFuel - preIR.length = out.length + extraFuel + 1) :
    compileStmtList fields spec.events spec.errors .calldata [] false scope [] (pre ++ [stmt]) =
      .ok (preIR ++ out) ∧
    ∃ sourceResult irExec,
      execStmtListWithHelpers spec fields helperFuel runtime (pre ++ [stmt]) = sourceResult ∧
      execIRStmts irFuel state (preIR ++ out) = irExec ∧
      stmtStepMatchesIRExec fields
        (stmtNextScope (pre.foldl (fun names stmt => collectStmtBindNames stmt ++ names) scope) stmt)
        sourceResult irExec := by
  refine ⟨compiled_append spec fields scope pre [stmt] preIR out first
    (compiled_error_singleton spec fields _ stmt out minimum step), ?_⟩
  exact CustomErrorContinuation.prefix_then_error spec fields _ stmt out minimum step
    helperFuel irFuel extraFuel runtime next state nextIR pre preIR domain initial source executed
    pointer enough remaining

end Compiler.Proofs.IRGeneration.CustomErrorListCompilation
