import Verity.Core.Model.CallProgramRollback

/-!
# Gas-faithful adversaries and non-observable failure causes

Short-term gas semantics for the external-call boundary (#1963 §1.4): tie the
modeled cost of serving a request to the call's gas allowance and its result,
without committing to opcode-level accounting (a dedicated roadmap lane).

- A `GasFaithful` adversary can only succeed within the site's allowance, and
  must fail — never commit — when the modeled cost exceeds it (the callee runs
  out of gas).
- `FailureCause`/`CauseModel` give failures an internal taxonomy (out-of-gas
  vs. opaque exceptional halt).  The cause is a modeling artifact only: it is
  not a field of `AdversaryModel`, and `denoteCall_congr` makes precise that
  observations are determined by the three adversary fields alone, so no
  theorem can leak a cause to the caller — matching the EVM, where the caller
  sees only the zero success bit and returndata.
- The caller-side assumption that the enclosing function has enough gas to
  run its own handler is explicit (`CallerCoversAllowance`), not implicit.
-/
namespace Compiler.CompilationModel.DenoteExternalCalls

/-- Modeled cost discipline.  `requires site world` is the gas the callee
needs to serve the request from `world`. -/
structure GasFaithful (requires : CallSite → Verity.ContractState → Nat)
    (adversary : AdversaryModel) : Prop where
  /-- Success is only possible within the requested allowance. -/
  success_within_allowance : ∀ site world data,
    adversary.result site world = .success data → requires site world ≤ site.gas
  /-- An over-budget request fails: the callee runs out of gas.  It cannot
  succeed, revert with chosen data, or commit. -/
  overBudget_fails : ∀ site world,
    site.gas < requires site world → ∃ data, adversary.result site world = .failure data
  /-- The callee cannot claim more gas than the allowance it was given. -/
  gasUsed_le_allowance : ∀ site world, adversary.gasUsed site world ≤ site.gas

/-- Contrapositive of `success_within_allowance`: an over-budget call has no
successful response. -/
theorem GasFaithful.overBudget_no_success
    {requires : CallSite → Verity.ContractState → Nat}
    {adversary : AdversaryModel} (h : GasFaithful requires adversary)
    (site : CallSite) (world : Verity.ContractState)
    (hover : site.gas < requires site world) (data : List Nat) :
    adversary.result site world ≠ .success data := by
  intro hres
  exact absurd (h.success_within_allowance site world data hres)
    (Nat.not_le.mpr hover)

/-- The out-of-gas callee never commits: an over-budget call preserves the
caller world for every call kind. -/
theorem GasFaithful.overBudget_preserves_world
    {requires : CallSite → Verity.ContractState → Nat}
    {adversary : AdversaryModel} (h : GasFaithful requires adversary)
    (site : CallSite) (state : CallState)
    (hover : site.gas < requires site state.world) :
    (denoteCall adversary site state).state.world = state.world := by
  obtain ⟨data, hfail⟩ := h.overBudget_fails site state.world hover
  cases hkind : site.kind with
  | staticcall => exact denoteCall_staticcall_world adversary site state hkind
  | call =>
      exact denoteCall_failure_world adversary site state data (Or.inl hkind) hfail
  | delegatecall =>
      exact denoteCall_failure_world adversary site state data (Or.inr hkind) hfail

/-- Explicit caller-side assumption: the caller's remaining gas covers the
allowance it forwards, so the call cannot silently starve the caller's own
continuation in the model. -/
def CallerCoversAllowance (state : CallState) (site : CallSite) : Prop :=
  site.gas ≤ state.gasRemaining

/-- Under the caller-cover assumption and gas-faithfulness, the charged gas is
exactly what the callee claims: neither the availability cap nor the
allowance cap bites. -/
theorem chargedGas_eq_claimed_of_faithful
    {requires : CallSite → Verity.ContractState → Nat}
    {adversary : AdversaryModel} (h : GasFaithful requires adversary)
    (site : CallSite) (state : CallState)
    (hcover : CallerCoversAllowance state site) :
    chargedGas state.gasRemaining site.gas (adversary.gasUsed site state.world) =
      adversary.gasUsed site state.world := by
  have hclaim := h.gasUsed_le_allowance site state.world
  have h1 : Nat.min site.gas (adversary.gasUsed site state.world) =
      adversary.gasUsed site state.world := Nat.min_eq_right hclaim
  have h2 : Nat.min state.gasRemaining (adversary.gasUsed site state.world) =
      adversary.gasUsed site state.world :=
    Nat.min_eq_right (Nat.le_trans hclaim hcover)
  unfold chargedGas
  rw [h1, h2]

/-! ## Non-observable failure causes -/

/-- Internal cause of a zero-success-bit call. -/
inductive FailureCause where
  | outOfGas
  | exceptional
  deriving DecidableEq, Repr

/-- A cause assignment for an adversary's failures.  Deliberately *not* part
of `AdversaryModel`: causes exist for the modeler, not for the caller. -/
structure CauseModel where
  causeOf : CallSite → Verity.ContractState → FailureCause

/-- Observations are determined by the adversary's three fields alone: two
adversaries with equal responses, transitions, and gas claims are
observationally identical, whatever cause narrative accompanies them.  This is
the formal sense in which `FailureCause` cannot leak to the caller. -/
theorem denoteCall_congr (a b : AdversaryModel)
    (hres : a.result = b.result)
    (htrans : a.stateTransition = b.stateTransition)
    (hgas : a.gasUsed = b.gasUsed) :
    denoteCall a = denoteCall b := by
  cases a; cases b
  cases hres; cases htrans; cases hgas
  rfl

/-- The same cause-erasure at the program level. -/
theorem denote_congr (a b : AdversaryModel)
    (hres : a.result = b.result)
    (htrans : a.stateTransition = b.stateTransition)
    (hgas : a.gasUsed = b.gasUsed)
    (prog : CallProgram α) (state : CallState) :
    denote prog a state = denote prog b state := by
  have hcall := denoteCall_congr a b hres htrans hgas
  induction prog generalizing state with
  | pure value => rfl
  | bind site next ih =>
      show denote (next (denoteCall a site state)) a (denoteCall a site state).state =
        denote (next (denoteCall b site state)) b (denoteCall b site state).state
      rw [hcall]
      exact ih (denoteCall b site state) (denoteCall b site state).state

end Compiler.CompilationModel.DenoteExternalCalls
