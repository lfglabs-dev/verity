import Verity.Core.Model.SummaryBridge
import Verity.Core.Reentrancy

/-!
# Callback-bounded adversaries

Connects the external-call boundary (`AdversaryModel`) to the reentrancy
rely-guarantee framework (`ReentrancySpec`): instead of treating the callee as
an arbitrary world transformer, a *callback-bounded* adversary's committed
transitions are exactly finite reentry schedules drawn from the caller's
registered entrypoints — the callee may call back into the caller, choose any
entrypoints in any order, observe intermediate state, and reenter before the
first call's continuation runs, but it cannot perform caller-state magic that
no entrypoint could.

The payoff mirrors `ReentrancySpec.schedule_preserves`: one invariant proof
per entrypoint extends to every call site of every `CallProgram`, at every
externally opened window, and through the transaction commit/revert boundary.
-/
namespace Compiler.CompilationModel.DenoteExternalCalls

open Verity.Core.Invariant (Preserves runSeq)
open Verity.Core.Reentrancy (ReentrancySpec)

/-- Each mutable transition is some finite reentry schedule drawn from the
registry.  Static sites are unrestricted: `denoteCall` never commits their
transitions, and `Conforms` separately pins them externally. -/
def CallbackBounded
    (entrypoints : List (Verity.ContractState → Verity.ContractState))
    (adversary : AdversaryModel) : Prop :=
  ∀ site world, site.kind ≠ .staticcall →
    ∃ sched : List (Verity.ContractState → Verity.ContractState),
      (∀ f ∈ sched, f ∈ entrypoints) ∧
        adversary.stateTransition site world = runSeq sched world

/-- One external call under a callback-bounded adversary preserves the spec
invariant: rollback outcomes keep the pre-call world, and committed outcomes
are reentry schedules, covered by the per-entrypoint obligations. -/
theorem CallbackBounded.denoteCall_preserves (spec : ReentrancySpec)
    {adversary : AdversaryModel}
    (h : CallbackBounded spec.entrypoints adversary)
    (site : CallSite) (state : CallState)
    (hInv : spec.Inv state.world) :
    spec.Inv (denoteCall adversary site state).state.world := by
  cases hkind : site.kind with
  | staticcall =>
      rw [denoteCall_staticcall_world adversary site state hkind]
      exact hInv
  | call =>
      cases hres : adversary.result site state.world with
      | success data =>
          rw [denoteCall_call_success_world adversary site state data hkind hres]
          obtain ⟨sched, hmem, htrans⟩ := h site state.world (by simp [hkind])
          rw [htrans]
          exact spec.schedule_preserves sched hmem state.world hInv
      | failure data =>
          rw [denoteCall_failure_world adversary site state data (Or.inl hkind) hres]
          exact hInv
      | revert data =>
          rw [denoteCall_revert_world adversary site state data (Or.inl hkind) hres]
          exact hInv
  | delegatecall =>
      cases hres : adversary.result site state.world with
      | success data =>
          rw [denoteCall_delegatecall_success_world adversary site state data hkind hres]
          obtain ⟨sched, hmem, htrans⟩ := h site state.world (by simp [hkind])
          rw [htrans]
          exact spec.schedule_preserves sched hmem state.world hInv
      | failure data =>
          rw [denoteCall_failure_world adversary site state data (Or.inr hkind) hres]
          exact hInv
      | revert data =>
          rw [denoteCall_revert_world adversary site state data (Or.inr hkind) hres]
          exact hInv

/-- The invariant threads through every call of any program: no finite
sequence of externally opened windows — each free to reenter through any
registered schedule — can break it. -/
theorem CallbackBounded.denote_preserves (spec : ReentrancySpec)
    {adversary : AdversaryModel}
    (h : CallbackBounded spec.entrypoints adversary)
    (prog : CallProgram α) (state : CallState)
    (hInv : spec.Inv state.world) :
    spec.Inv (denote prog adversary state).2.world := by
  induction prog generalizing state with
  | pure value => exact hInv
  | bind site next ih =>
      exact ih (denoteCall adversary site state)
        (denoteCall adversary site state).state
        (h.denoteCall_preserves spec site state hInv)

/-- Through the transaction boundary: a committed transaction ends in an
invariant state by the program law, and a reverted one by rollback to the
initial state. -/
theorem CallbackBounded.transaction_preserves (spec : ReentrancySpec)
    {adversary : AdversaryModel}
    (h : CallbackBounded spec.entrypoints adversary)
    (prog : CallProgram (TransactionResult α)) (state : CallState)
    (hInv : spec.Inv state.world) :
    spec.Inv (denoteTransaction prog adversary state).state.world := by
  cases hres : (denote prog adversary state).1 with
  | commit value =>
      rw [denoteTransaction_commit_eq prog adversary state value hres]
      exact h.denote_preserves spec prog state hInv
  | revert data =>
      rw [denoteTransaction_revert_world prog adversary state data hres]
      exact hInv

end Compiler.CompilationModel.DenoteExternalCalls
