/-
  Rely-guarantee core for Verity reentrancy reasoning.

  This module is deliberately *state-polymorphic*: nothing here mentions
  `ContractState`. The v1 single-contract development instantiates every
  definition at `σ := ContractState` (see `Verity/Core/Reentrancy.lean`); a
  future multi-contract development instantiates the SAME definitions at
  `σ := System`. Because the library never commits to a state type, the v1
  proofs transfer to the multi-contract setting by instantiation rather than
  re-proof — that is the forward-compatibility guarantee.

  The single load-bearing result is `runSeq_preserves`: if every entrypoint
  preserves the invariant, then *any* finite schedule of them does. This is
  what collapses the adversarial interleaving space into one proof obligation
  per entrypoint, with no enumeration of interleavings.
-/

namespace Verity.Core.Invariant

/-- A state transformer `c` *preserves* the invariant `Inv`. -/
def Preserves {σ : Type} (Inv : σ → Prop) (c : σ → σ) : Prop :=
  ∀ s, Inv s → Inv (c s)

namespace Preserves

/-- The identity transformer preserves every invariant (the "no reentry" case). -/
theorem id {σ : Type} (Inv : σ → Prop) : Preserves Inv (fun s => s) :=
  fun _ h => h

/-- Preservation is closed under composition: this is what lets a *sequence* of
    adversarial reentries be discharged from the per-step obligations. -/
theorem comp {σ : Type} {Inv : σ → Prop} {f g : σ → σ}
    (hf : Preserves Inv f) (hg : Preserves Inv g) :
    Preserves Inv (fun s => f (g s)) :=
  fun s h => hf (g s) (hg s h)

end Preserves

/-- A reentrant adversary as a finite *schedule* of picked entrypoints, applied
    left to right. A bounded call depth is exactly a finite list; unbounded
    mutual recursion is out of scope (it is not expressible as a `List`). -/
def runSeq {σ : Type} (picks : List (σ → σ)) (s : σ) : σ :=
  picks.foldl (fun acc f => f acc) s

@[simp] theorem runSeq_nil {σ : Type} (s : σ) : runSeq [] s = s := rfl

@[simp] theorem runSeq_cons {σ : Type} (f : σ → σ) (fs : List (σ → σ)) (s : σ) :
    runSeq (f :: fs) s = runSeq fs (f s) := rfl

/-- Rely-guarantee meta-theorem. If every entrypoint preserves `Inv`, then any
    finite schedule of them preserves `Inv`. The entire interleaving space
    collapses to one obligation per entrypoint — no interleaving enumeration. -/
theorem runSeq_preserves {σ : Type} {Inv : σ → Prop} :
    ∀ (picks : List (σ → σ)),
      (∀ f, f ∈ picks → Preserves Inv f) → Preserves Inv (runSeq picks) := by
  intro picks
  induction picks with
  | nil => intro _ s hs; exact hs
  | cons f fs ih =>
      intro h s hs
      have hf : Preserves Inv f := h f (List.mem_cons.mpr (Or.inl rfl))
      have hfs : ∀ g, g ∈ fs → Preserves Inv g :=
        fun g hg => h g (List.mem_cons.mpr (Or.inr hg))
      exact ih hfs (f s) (hf s hs)

end Verity.Core.Invariant
