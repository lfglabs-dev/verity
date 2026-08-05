import Verity.Core.Model.DenoteExternalCalls

/-!
# Whole-program rollback and commit laws for external calls

`CallProgram` continuations may inspect the preceding observation, so the calls
made by a program are determined only when an adversary and initial state are
supplied.  `ObservedCall` records exactly the pre-call world needed to state
response hypotheses without ambiguity (including when the same site occurs
more than once).
-/
namespace Compiler.CompilationModel.DenoteExternalCalls

/-- One entry in the dynamically observed call trace. -/
structure ObservedCall where
  site : CallSite
  preWorld : Verity.ContractState

/-- The calls performed by `prog`, in execution order. -/
def ObservedCalls : CallProgram α → AdversaryModel → CallState → List ObservedCall
  | .pure _, _, _ => []
  | .bind site next, adversary, state =>
      let observation := denoteCall adversary site state
      { site := site, preWorld := state.world } ::
        ObservedCalls (next observation) adversary observation.state

/-- The call sites performed by `prog`, in execution order.  The adversary and
state parameters are necessary because a continuation can branch on the
preceding observation. -/
def CallsIn (prog : CallProgram α) (adversary : AdversaryModel)
    (state : CallState) : List CallSite :=
  (ObservedCalls prog adversary state).map (·.site)

/-- A trace entry rolls back when it is static, fails, or reverts. -/
def RollsBack (adversary : AdversaryModel) (entry : ObservedCall) : Prop :=
  entry.site.kind = .staticcall ∨
    (∃ data, adversary.result entry.site entry.preWorld = .failure data) ∨
    ∃ data, adversary.result entry.site entry.preWorld = .revert data

/-- A trace entry succeeds when the adversary returns `success`. -/
def Succeeds (adversary : AdversaryModel) (entry : ObservedCall) : Prop :=
  ∃ data, adversary.result entry.site entry.preWorld = .success data

/-- The world update committed by one successful site.  Static calls are
read-only even when their response is successful. -/
def commitWorld (adversary : AdversaryModel) (world : Verity.ContractState)
    (site : CallSite) : Verity.ContractState :=
  if site.kind = .staticcall then world else adversary.stateTransition site world

/-- Iterate successful call commits in execution order. -/
def commitWorlds (adversary : AdversaryModel) (world : Verity.ContractState)
    (sites : List CallSite) : Verity.ContractState :=
  sites.foldl (commitWorld adversary) world

theorem denote_pure_world (value : α) (adversary : AdversaryModel)
    (state : CallState) :
    (denote (.pure value) adversary state).2.world = state.world := rfl

private theorem rollsBack_denoteCall_world (adversary : AdversaryModel)
    (site : CallSite) (state : CallState)
    (h : RollsBack adversary { site := site, preWorld := state.world }) :
    (denoteCall adversary site state).state.world = state.world := by
  rcases h with hstatic | hfailure | hrevert
  · exact denoteCall_staticcall_world adversary site state hstatic
  · rcases hfailure with ⟨data, hresult⟩
    cases hkind : site.kind with
    | call =>
        exact denoteCall_failure_world adversary site state data
          (Or.inl hkind) hresult
    | staticcall =>
        exact denoteCall_staticcall_world adversary site state hkind
    | delegatecall =>
        exact denoteCall_failure_world adversary site state data
          (Or.inr hkind) hresult
  · rcases hrevert with ⟨data, hresult⟩
    cases hkind : site.kind with
    | call =>
        exact denoteCall_revert_world adversary site state data
          (Or.inl hkind) hresult
    | staticcall =>
        exact denoteCall_staticcall_world adversary site state hkind
    | delegatecall =>
        exact denoteCall_revert_world adversary site state data
          (Or.inr hkind) hresult

theorem denote_single_bind_world (site : CallSite) (value : α)
    (adversary : AdversaryModel) (state : CallState) :
    (denote (.bind site fun _ => .pure value) adversary state).2.world =
      match site.kind, adversary.result site state.world with
      | .staticcall, _ => state.world
      | .call, .success _ | .delegatecall, .success _ =>
          adversary.stateTransition site state.world
      | .call, .failure _ | .call, .revert _
      | .delegatecall, .failure _ | .delegatecall, .revert _ => state.world := by
  rfl

theorem denote_sequential_world (first second : CallSite)
    (adversary : AdversaryModel) (state : CallState) :
    (denote (sequential first second) adversary state).2.world =
      (denoteCall adversary second (denoteCall adversary first state).state).state.world := by
  rfl

/-- If every dynamically observed call fails, reverts, or is static, the whole
program preserves its initial world. -/
theorem denoteCallProgram_all_revert_preserves_world
    (prog : CallProgram α) (adversary : AdversaryModel) (state : CallState)
    (h : ∀ entry ∈ ObservedCalls prog adversary state, RollsBack adversary entry) :
    (denote prog adversary state).2.world = state.world := by
  induction prog generalizing state with
  | pure value => exact denote_pure_world value adversary state
  | bind site next ih =>
      let observation := denoteCall adversary site state
      have hhead : RollsBack adversary { site := site, preWorld := state.world } := by
        apply h _ (by simp [ObservedCalls])
      have htail : ∀ entry ∈ ObservedCalls (next observation) adversary observation.state,
          RollsBack adversary entry := by
        intro entry hentry
        apply h entry
        simp [ObservedCalls, observation, hentry]
      have hrest := ih observation observation.state htail
      have hcall := rollsBack_denoteCall_world adversary site state hhead
      exact hrest.trans hcall

private theorem succeeds_denoteCall_world (adversary : AdversaryModel)
    (site : CallSite) (state : CallState)
    (h : Succeeds adversary { site := site, preWorld := state.world }) :
    (denoteCall adversary site state).state.world =
      commitWorld adversary state.world site := by
  rcases h with ⟨data, hresult⟩
  cases hkind : site.kind with
  | call =>
      simpa [commitWorld, hkind] using
        denoteCall_call_success_world adversary site state data hkind hresult
  | staticcall =>
      simpa [commitWorld, hkind] using
        denoteCall_staticcall_world adversary site state hkind
  | delegatecall =>
      simpa [commitWorld, hkind] using
        denoteCall_delegatecall_success_world adversary site state data hkind hresult

/-- If every dynamically observed call succeeds, the final world is the fold
of the successful mutable-call transitions over the sites in execution order.
Static calls occur in `CallsIn` but contribute the identity update. -/
theorem denoteCallProgram_all_succeed_commits_world
    (prog : CallProgram α) (adversary : AdversaryModel) (state : CallState)
    (h : ∀ entry ∈ ObservedCalls prog adversary state, Succeeds adversary entry) :
    (denote prog adversary state).2.world =
      commitWorlds adversary state.world (CallsIn prog adversary state) := by
  induction prog generalizing state with
  | pure value => rfl
  | bind site next ih =>
      let observation := denoteCall adversary site state
      have hhead : Succeeds adversary { site := site, preWorld := state.world } := by
        apply h _ (by simp [ObservedCalls])
      have htail : ∀ entry ∈ ObservedCalls (next observation) adversary observation.state,
          Succeeds adversary entry := by
        intro entry hentry
        apply h entry
        simp [ObservedCalls, observation, hentry]
      have hcall := succeeds_denoteCall_world adversary site state hhead
      have hrest := ih observation observation.state htail
      change (denote (next observation) adversary observation.state).2.world = _
      rw [hrest]
      change commitWorlds adversary observation.state.world
          (CallsIn (next observation) adversary observation.state) =
        commitWorlds adversary (commitWorld adversary state.world site)
          (CallsIn (next observation) adversary observation.state)
      rw [hcall]

end Compiler.CompilationModel.DenoteExternalCalls
