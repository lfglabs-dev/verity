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

/-! ## Top-level transaction rollback -/

/-- The control result of the enclosing transaction.  Unlike an individual
external-call result, `revert` rolls back every mutable call already performed
by the program. -/
inductive TransactionResult (α : Type) where
  | commit (value : α)
  | revert (returndata : List Nat)
  deriving DecidableEq, Repr

/-- The observable result and final caller state of a transaction. -/
structure TransactionObservation (α : Type) where
  result : TransactionResult α
  state : CallState

/-- Run a call program against a snapshot of the caller world.  A committed
result keeps the threaded state.  A top-level revert restores the initial
world after all inner calls have run, while retaining charged gas and exposing
the transaction's revert data. -/
def denoteTransaction (prog : CallProgram (TransactionResult α))
    (adversary : AdversaryModel) (state : CallState) : TransactionObservation α :=
  let (result, postState) := denote prog adversary state
  match result with
  | .commit value => { result := .commit value, state := postState }
  | .revert data =>
      { result := .revert data
        state := { postState with world := state.world, returndata := data } }

theorem denoteTransaction_commit_eq (prog : CallProgram (TransactionResult α))
    (adversary : AdversaryModel) (state : CallState) (value : α)
    (h : (denote prog adversary state).1 = .commit value) :
    denoteTransaction prog adversary state =
      { result := .commit value, state := (denote prog adversary state).2 } := by
  simp [denoteTransaction, h]

theorem denoteTransaction_revert_world (prog : CallProgram (TransactionResult α))
    (adversary : AdversaryModel) (state : CallState) (data : List Nat)
    (h : (denote prog adversary state).1 = .revert data) :
    (denoteTransaction prog adversary state).state.world = state.world := by
  simp [denoteTransaction, h]

theorem denoteTransaction_revert_result (prog : CallProgram (TransactionResult α))
    (adversary : AdversaryModel) (state : CallState) (data : List Nat)
    (h : (denote prog adversary state).1 = .revert data) :
    (denoteTransaction prog adversary state).result = .revert data := by
  simp [denoteTransaction, h]

theorem denoteTransaction_revert_returndata (prog : CallProgram (TransactionResult α))
    (adversary : AdversaryModel) (state : CallState) (data : List Nat)
    (h : (denote prog adversary state).1 = .revert data) :
    (denoteTransaction prog adversary state).state.returndata = data := by
  simp [denoteTransaction, h]

theorem denoteTransaction_revert_gasRemaining (prog : CallProgram (TransactionResult α))
    (adversary : AdversaryModel) (state : CallState) (data : List Nat)
    (h : (denote prog adversary state).1 = .revert data) :
    (denoteTransaction prog adversary state).state.gasRemaining =
      (denote prog adversary state).2.gasRemaining := by
  simp [denoteTransaction, h]

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

/-! ## Result-aware iteration

A loop whose continuation decides, after observing each call, whether to keep
iterating, stop with a committed value, or abort the enclosing transaction.
The laws below relate the *observed trace* — not just the wrapper — to the
rollback: an aborted run has really committed the fold of its observed sites
into the threaded state before the transaction discards it. -/

/-- Decision taken by the loop policy after observing one iteration. -/
inductive LoopStep (α : Type) where
  | next
  | stop (value : α)
  | abort (returndata : List Nat)

/-- Iterate `sites` in order.  After each call the `step` policy inspects the
observation and chooses to continue, stop with a committed value, or abort the
enclosing transaction.  Exhausting the sites commits `exhausted`.  A failed or
reverted inner call does not by itself abort the transaction: the policy sees
the observation and chooses, which models callers that tolerate individual
call failures. -/
def forEachCall (step : CallObservation → LoopStep α) (exhausted : α) :
    List CallSite → CallProgram (TransactionResult α)
  | [] => .pure (.commit exhausted)
  | site :: rest =>
      .bind site fun obs =>
        match step obs with
        | .next => forEachCall step exhausted rest
        | .stop value => .pure (.commit value)
        | .abort data => .pure (.revert data)

/-- The loop executes a prefix of its planned sites: iteration order follows
the site list and stops at the first `stop`/`abort` decision. -/
theorem forEachCall_callsIn_take (step : CallObservation → LoopStep α)
    (exhausted : α) (sites : List CallSite) (adversary : AdversaryModel)
    (state : CallState) :
    ∃ n, CallsIn (forEachCall step exhausted sites) adversary state =
      sites.take n := by
  induction sites generalizing state with
  | nil => exact ⟨0, rfl⟩
  | cons site rest ih =>
      cases hstep : step (denoteCall adversary site state) with
      | next =>
          obtain ⟨n, hn⟩ := ih (denoteCall adversary site state).state
          exact ⟨n + 1, by
            simp [CallsIn, ObservedCalls, forEachCall, hstep] at hn ⊢
            exact hn⟩
      | stop value =>
          exact ⟨1, by simp [CallsIn, ObservedCalls, forEachCall, hstep]⟩
      | abort data =>
          exact ⟨1, by simp [CallsIn, ObservedCalls, forEachCall, hstep]⟩

/-- A transaction-level revert of the loop can only originate from the loop
policy: some actually produced observation was mapped to `abort` with exactly
the revert data the transaction reports. -/
theorem forEachCall_revert_step_abort (step : CallObservation → LoopStep α)
    (exhausted : α) (sites : List CallSite) (adversary : AdversaryModel)
    (state : CallState) (data : List Nat)
    (habort : (denote (forEachCall step exhausted sites) adversary state).1 =
      .revert data) :
    ∃ obs : CallObservation, step obs = .abort data := by
  induction sites generalizing state with
  | nil => simp [forEachCall, denote] at habort
  | cons site rest ih =>
      have hden : (denote (forEachCall step exhausted (site :: rest)) adversary state).1 =
          (denote
            (match step (denoteCall adversary site state) with
              | .next => forEachCall step exhausted rest
              | .stop value => CallProgram.pure (TransactionResult.commit value)
              | .abort data => CallProgram.pure (TransactionResult.revert data))
            adversary (denoteCall adversary site state).state).1 := rfl
      rw [hden] at habort
      cases hstep : step (denoteCall adversary site state) with
      | next =>
          rw [hstep] at habort
          exact ih (denoteCall adversary site state).state habort
      | stop value =>
          rw [hstep] at habort
          exact absurd habort (by simp [denote])
      | abort d =>
          rw [hstep] at habort
          have hdd : d = data := by simpa [denote] using habort
          exact ⟨denoteCall adversary site state, by rw [hstep, hdd]⟩

/-- The Lido-shaped rollback law.  A run of the loop whose observed iterations
all succeed — and therefore committed their world transitions into the
threaded state, per the third conjunct — but which ends in a policy abort,
reverts the whole transaction: the observable result carries the abort data,
the final world is the initial world, and the discarded intermediate world is
exactly the fold of the observed sites' commits.  The conclusion is tied to
`ObservedCalls`/`CallsIn`, so it cannot be satisfied by a wrapper that merely
overwrites the final state: the same hypotheses pin the intermediate state to
the committed prefix. -/
theorem forEachCall_abort_discards_committed_prefix
    (step : CallObservation → LoopStep α) (exhausted : α)
    (sites : List CallSite) (adversary : AdversaryModel) (state : CallState)
    (data : List Nat)
    (habort : (denote (forEachCall step exhausted sites) adversary state).1 =
      .revert data)
    (hsucc : ∀ entry ∈ ObservedCalls (forEachCall step exhausted sites) adversary state,
      Succeeds adversary entry) :
    (denoteTransaction (forEachCall step exhausted sites) adversary state).result =
        .revert data ∧
    (denoteTransaction (forEachCall step exhausted sites) adversary state).state.world =
        state.world ∧
    (denote (forEachCall step exhausted sites) adversary state).2.world =
      commitWorlds adversary state.world
        (CallsIn (forEachCall step exhausted sites) adversary state) :=
  ⟨denoteTransaction_revert_result _ adversary state data habort,
   denoteTransaction_revert_world _ adversary state data habort,
   denoteCallProgram_all_succeed_commits_world _ adversary state hsucc⟩

end Compiler.CompilationModel.DenoteExternalCalls
