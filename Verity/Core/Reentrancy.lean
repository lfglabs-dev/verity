/-
  Reentrancy rely-guarantee framework for Verity (single-contract v1, with a
  forward-compatible multi-contract layer).

  This module grounds the state-polymorphic library in `Verity/Core/Invariant.lean`
  against the real `ContractState`/`Contract` monad:

    * `reentrantCall` — the adversarial-reentry effect in the Contract monad.
    * `ReentrancySpec` — bundle a global invariant with the contract's entrypoint
      registry; discharge one obligation per entrypoint and obtain safety against
      the entire adversarial interleaving space (`schedule_preserves`).
    * `System`/`lift`/`Isys` — the additive multi-contract (vN) layer. The v1
      `ReentrancySpec` is the single-slot instance; no v1 proof is redone.

  The design intent is the Midnight `take` callback-reentrancy bug: with a
  lock-as-disjunct invariant `I s := healthy s ∨ locked s`, a transiently
  unhealthy but *locked* position still satisfies `I`, so no reentrant
  `liquidate` can fire during the trade window. See
  `Contracts/ReentrancyRelyGuarantee/Contract.lean` for the worked example.
-/

import Verity.Core
import Verity.Core.Semantics
import Verity.Core.Invariant

namespace Verity.Core.Reentrancy

open Verity
open Verity.Core.Invariant

/-! ## Adversarial reentry in the Contract monad (S1) -/

/-- One external call that may reenter, modeled as an arbitrary state
    transformer over this contract's persistent channels. Exposed as a
    `Contract Unit` so it threads through `bind`/do-notation like any effect.
    The rely condition (below) constrains `adv` to preserve the contract
    invariant; with `adv := id` this degenerates to the no-reentry case. -/
def reentrantCall (adv : ContractState → ContractState) : Contract Unit :=
  fun s => ContractResult.success () (adv s)

@[simp] theorem reentrantCall_run (adv : ContractState → ContractState) (s : ContractState) :
    (reentrantCall adv).run s = ContractResult.success () (adv s) := rfl

@[simp] theorem reentrantCall_runState (adv : ContractState → ContractState) (s : ContractState) :
    (reentrantCall adv).runState s = adv s := rfl

/-- A `Contract` preserves a state invariant when every *successful* run from an
    `Inv`-state lands in an `Inv`-state. Reverts are excluded on purpose: EVM
    atomicity rolls a reverted call back to its pre-state (see `Contract.run`),
    so a revert preserves every invariant for free. -/
def ContractPreserves {α : Type} (Inv : ContractState → Prop) (c : Contract α) : Prop :=
  ∀ s, Inv s → ∀ a s', c.run s = ContractResult.success a s' → Inv s'

/-- Bridge from the pure rely-guarantee library to the monad: if the adversary
    transformer preserves `Inv`, then the `reentrantCall` effect does. -/
theorem reentrantCall_preserves {Inv : ContractState → Prop}
    {adv : ContractState → ContractState} (hadv : Preserves Inv adv) :
    ContractPreserves Inv (reentrantCall adv) := by
  intro s hs a s' hrun
  rw [reentrantCall_run] at hrun
  injection hrun with _hval hstate
  rw [← hstate]
  exact hadv s hs

/-! ## ReentrancySpec: register entrypoints once, get whole-interleaving safety (S3) -/

/-- A reentrancy specification for one contract: a global invariant `Inv` plus
    the finite registry of public entrypoints (each modeled as a state
    transformer) and the proof obligation that each preserves `Inv`. The
    macro-emitted entrypoint registry supplies `entrypoints`; the author
    supplies `Inv` and `entrypoints_preserve` — one obligation per entrypoint. -/
structure ReentrancySpec where
  Inv : ContractState → Prop
  entrypoints : List (ContractState → ContractState)
  entrypoints_preserve : ∀ f, f ∈ entrypoints → Preserves Inv f

namespace ReentrancySpec

/-- The payoff. ANY finite reentry schedule drawn from the registered
    entrypoints preserves the invariant. One proof per entrypoint discharges the
    entire adversarial interleaving space — no interleaving enumeration. -/
theorem schedule_preserves (spec : ReentrancySpec)
    (sched : List (ContractState → ContractState))
    (hsched : ∀ f, f ∈ sched → f ∈ spec.entrypoints) :
    Preserves spec.Inv (runSeq sched) := by
  apply runSeq_preserves
  intro f hf
  exact spec.entrypoints_preserve f (hsched f hf)

/-- Corollary at the monad level: replaying any registered schedule as a single
    `reentrantCall` preserves the invariant. -/
theorem reentrantCall_schedule_preserves (spec : ReentrancySpec)
    (sched : List (ContractState → ContractState))
    (hsched : ∀ f, f ∈ sched → f ∈ spec.entrypoints) :
    ContractPreserves spec.Inv (reentrantCall (runSeq sched)) :=
  reentrantCall_preserves (spec.schedule_preserves sched hsched)

end ReentrancySpec

/-! ## Forward-compatibility: multi-contract `System` (vN)

  Everything below is additive and reuses the SAME `Preserves`/`runSeq` library.
  It shows the v1 single-contract `ReentrancySpec` is the degenerate (single-slot)
  instance of a multi-contract development. No v1 proof is re-done; the only new
  primitive is the storage lens `lift`. Deliberately out of scope here (vN proof
  obligations, not v1 blockers): unbounded mutual A↔B recursion and oracle-return
  precision for read-only reentrancy. -/

/-- A multi-contract world: a map from address to per-contract state. The v1
    `ContractState` is exactly one addressable slot. -/
structure System where
  slot : Address → ContractState

/-- Run a single contract's entrypoint on its own slot, framing every other slot
    unchanged — the one genuinely new vN primitive (a state lens). -/
def lift (a : Address) (c : ContractState → ContractState) (sys : System) : System :=
  { slot := fun x => if x = a then c (sys.slot a) else sys.slot x }

/-- Joint invariant across the in-scope contracts, built from the SAME
    per-contract invariant. Out-of-scope addresses are trusted and unconstrained. -/
def Isys (Inv : ContractState → Prop) (inScope : List Address) (sys : System) : Prop :=
  ∀ a, a ∈ inScope → Inv (sys.slot a)

/-- Lens lemma: a per-contract entrypoint preserving `Inv` on its slot preserves
    the JOINT invariant. This is the only bridging proof the multi-contract layer
    adds. -/
theorem lift_preserves {Inv : ContractState → Prop} {a : Address} {inScope : List Address}
    {c : ContractState → ContractState} (hc : Preserves Inv c) :
    Preserves (Isys Inv inScope) (lift a c) := by
  intro sys hsys b hb
  show Inv (if b = a then c (sys.slot a) else sys.slot b)
  by_cases hba : b = a
  · rw [if_pos hba]
    exact hc (sys.slot a) (hsys a (hba ▸ hb))
  · rw [if_neg hba]
    exact hsys b hb

/-- A v1 `ReentrancySpec` lifts to the multi-contract setting at any slot with no
    new per-contract proof: every registered entrypoint, lifted, preserves the
    joint invariant. -/
theorem spec_lifts (spec : ReentrancySpec) (a : Address) (inScope : List Address)
    (f : ContractState → ContractState) (hf : f ∈ spec.entrypoints) :
    Preserves (Isys spec.Inv inScope) (lift a f) :=
  lift_preserves (spec.entrypoints_preserve f hf)

/-- Headline forward-compat theorem: ANY finite cross-contract reentry schedule —
    each step reentering some contract's registered entrypoint — preserves the
    JOINT invariant. Proven only from the per-contract obligations via the SAME
    polymorphic library, now instantiated at `σ := System`. -/
theorem cross_contract_schedule_preserves (spec : ReentrancySpec) (inScope : List Address)
    (steps : List (Address × (ContractState → ContractState)))
    (hsteps : ∀ p, p ∈ steps → p.2 ∈ spec.entrypoints) :
    Preserves (Isys spec.Inv inScope) (runSeq (steps.map (fun p => lift p.1 p.2))) := by
  apply runSeq_preserves
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨p, hp, rfl⟩ := hf
  exact lift_preserves (spec.entrypoints_preserve p.2 (hsteps p hp))

end Verity.Core.Reentrancy
