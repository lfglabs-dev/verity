import Compiler.CompilationModel.Validation

/-!
Proof-layer CEI safety surface.

`stmtListCEIViolation` is the compiler checker used before code generation.
This module gives that checker a public proof-facing meaning: a function has
proof-backed CEI execution safety exactly when the checker accepts its body and
the recognized trust exits are absent at the function boundary.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler.CompilationModel

/-- Execution-level CEI claim for a function body: along the source statement
order recognized by the compiler, no persistent state write is reachable after
an external interaction barrier. -/
def CEIExecutionSafe (fn : FunctionSpec) : Prop :=
  stmtListCEIViolation fn.body false = none

/-- Explicit CEI trust-exit obligations. A proof-backed `cei_safe` function must
not rely on the untyped post-interaction-write opt-out, the generated
`nonreentrant` runtime guard, or local unsafe/refinement obligations. -/
structure CEITrustExitsClosed (fn : FunctionSpec) : Prop where
  noPostInteractionWriteOptOut : fn.allowPostInteractionWrites = false
  noNonReentrantRuntimeGuard : fn.nonReentrantLock = none
  noLocalUnsafeObligations : fn.localObligations = []

/-- The public proof-backed `cei_safe` contract: the annotation is present, the
compiler CEI checker accepted the body, and all trust exits are closed. -/
structure CEIProofBackedExecution (fn : FunctionSpec) : Prop where
  annotated : fn.ceiSafe = true
  executionSafe : CEIExecutionSafe fn
  trustExitsClosed : CEITrustExitsClosed fn

theorem CEIProofBackedExecution.execution_safe
    {fn : FunctionSpec}
    (h : CEIProofBackedExecution fn) :
    CEIExecutionSafe fn :=
  h.executionSafe

theorem CEIProofBackedExecution.no_post_interaction_write_opt_out
    {fn : FunctionSpec}
    (h : CEIProofBackedExecution fn) :
    fn.allowPostInteractionWrites = false :=
  h.trustExitsClosed.noPostInteractionWriteOptOut

theorem CEIProofBackedExecution.no_nonreentrant_runtime_guard
    {fn : FunctionSpec}
    (h : CEIProofBackedExecution fn) :
    fn.nonReentrantLock = none :=
  h.trustExitsClosed.noNonReentrantRuntimeGuard

theorem CEIProofBackedExecution.no_local_unsafe_obligations
    {fn : FunctionSpec}
    (h : CEIProofBackedExecution fn) :
    fn.localObligations = [] :=
  h.trustExitsClosed.noLocalUnsafeObligations

/-- Bridge the concrete facts emitted by the macro/checker into the public CEI
execution theorem. Escape hatches are hypotheses rather than hidden premises. -/
theorem ceiProofBackedExecution_of_checker
    {fn : FunctionSpec}
    (hAnnotated : fn.ceiSafe = true)
    (hChecked : stmtListCEIViolation fn.body false = none)
    (hAllow : fn.allowPostInteractionWrites = false)
    (hLock : fn.nonReentrantLock = none)
    (hLocal : fn.localObligations = []) :
    CEIProofBackedExecution fn :=
  { annotated := hAnnotated
    executionSafe := hChecked
    trustExitsClosed :=
      { noPostInteractionWriteOptOut := hAllow
        noNonReentrantRuntimeGuard := hLock
        noLocalUnsafeObligations := hLocal } }

/-- Smoke theorem for the public bridge: an explicit `cei_safe` function whose
body is accepted by the CEI checker discharges the execution theorem without
any escape hatch premise. -/
theorem ceiProofBackedExecution_checked_empty_body :
    CEIProofBackedExecution
      { name := "checkedEmptyBody"
        params := []
        returnType := none
        body := []
        ceiSafe := true } :=
  by
    refine ceiProofBackedExecution_of_checker rfl ?_ rfl rfl rfl
    change stmtListCEIViolation [] false = none
    simp [stmtListCEIViolation]

end Compiler.Proofs.IRGeneration
