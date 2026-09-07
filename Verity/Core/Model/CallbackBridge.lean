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

/-- The macro-emitted registry is a predicate rather than a list of already
applied functions.  This keeps entrypoint arguments existential and, crucially,
indexes every executable transition by the same explicit adversary used at the
call boundary. -/
abbrev EntrypointRegistry :=
  AdversaryModel → (Verity.ContractState → Verity.ContractState) → Prop

namespace EntrypointRegistry

/-- Compatibility adapter for the original, argument-free worked examples. -/
def ofList (entrypoints : List (Verity.ContractState → Verity.ContractState)) :
    EntrypointRegistry :=
  fun _ entrypoint => entrypoint ∈ entrypoints

instance : Coe (List (Verity.ContractState → Verity.ContractState))
    EntrypointRegistry where
  coe := ofList

end EntrypointRegistry

/-- Each mutable transition is some finite reentry schedule drawn from the
registry.  Static sites are unrestricted: `denoteCall` never commits their
transitions, and `Conforms` separately pins them externally. -/
def CallbackBounded
    (entrypoints : EntrypointRegistry)
    (adversary : AdversaryModel) : Prop :=
  ∀ site world, site.kind ≠ .staticcall →
    ∃ sched : List (Verity.ContractState → Verity.ContractState),
      (∀ f ∈ sched, entrypoints adversary f) ∧
        adversary.stateTransition site world = runSeq sched world

/-- The sole proof obligation at the generated-registry boundary: every
transition admitted by the registry for this adversary preserves the caller's
invariant. -/
def RegistryPreserves (Inv : Verity.ContractState → Prop)
    (entrypoints : EntrypointRegistry) (adversary : AdversaryModel) : Prop :=
  ∀ f, entrypoints adversary f → Preserves Inv f

/-- A call through the restricted generated-registry boundary preserves any
invariant discharged for every registered, fully-applied entrypoint. -/
theorem CallbackBounded.denoteCall_preserves_registry
    (Inv : Verity.ContractState → Prop) (entrypoints : EntrypointRegistry)
    {adversary : AdversaryModel}
    (hbound : CallbackBounded entrypoints adversary)
    (hregistry : RegistryPreserves Inv entrypoints adversary)
    (site : CallSite) (state : CallState) (hInv : Inv state.world) :
    Inv (denoteCall adversary site state).state.world := by
  cases hkind : site.kind with
  | staticcall =>
      rw [denoteCall_staticcall_world adversary site state hkind]
      exact hInv
  | call =>
      cases hres : adversary.result site state.world with
      | success data =>
          rw [denoteCall_call_success_world adversary site state data hkind hres]
          obtain ⟨sched, hmem, htrans⟩ := hbound site state.world (by simp [hkind])
          rw [htrans]
          exact Verity.Core.Invariant.runSeq_preserves sched
            (fun f hf => hregistry f (hmem f hf)) state.world hInv
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
          obtain ⟨sched, hmem, htrans⟩ := hbound site state.world (by simp [hkind])
          rw [htrans]
          exact Verity.Core.Invariant.runSeq_preserves sched
            (fun f hf => hregistry f (hmem f hf)) state.world hInv
      | failure data =>
          rw [denoteCall_failure_world adversary site state data (Or.inr hkind) hres]
          exact hInv
      | revert data =>
          rw [denoteCall_revert_world adversary site state data (Or.inr hkind) hres]
          exact hInv

/-- One external call under a callback-bounded adversary preserves the spec
invariant: rollback outcomes keep the pre-call world, and committed outcomes
are reentry schedules, covered by the per-entrypoint obligations. -/
theorem CallbackBounded.denoteCall_preserves (spec : ReentrancySpec)
    {adversary : AdversaryModel}
    (h : CallbackBounded (EntrypointRegistry.ofList spec.entrypoints) adversary)
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
    (h : CallbackBounded (EntrypointRegistry.ofList spec.entrypoints) adversary)
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
    (h : CallbackBounded (EntrypointRegistry.ofList spec.entrypoints) adversary)
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
