import Verity.Core.Model.CallProgramRollback

/-! A two-call always-revert example using the whole-program wrapper. -/
namespace Contracts.Examples.CallProgramRollback

open Compiler.CompilationModel.DenoteExternalCalls

def first : CallSite :=
  { siteId := 1, kind := .call, target := 10, gas := 30 }

def second : CallSite :=
  { siteId := 2, kind := .delegatecall, target := 20, gas := 30 }

def commitsThenReverts : CallProgram (TransactionResult Nat) :=
  .bind first fun _ =>
    .bind second fun _ =>
      .pure (.revert [0xde, 0xad])

def commits : CallProgram (TransactionResult Nat) :=
  .bind first fun _ =>
    .pure (.commit 7)

example (adversary : AdversaryModel) (state : CallState)
    (h : ∀ entry ∈ ObservedCalls (sequential first second) adversary state,
      RollsBack adversary entry) :
    (denote (sequential first second) adversary state).2.world = state.world := by
  exact denoteCallProgram_all_revert_preserves_world
    (sequential first second) adversary state h

example (adversary : AdversaryModel) (state : CallState)
    (h : ∀ entry ∈ ObservedCalls (sequential first second) adversary state,
      Succeeds adversary entry) :
    (denote (sequential first second) adversary state).2.world =
      commitWorlds adversary state.world
        (CallsIn (sequential first second) adversary state) := by
  exact denoteCallProgram_all_succeed_commits_world
    (sequential first second) adversary state h

example (adversary : AdversaryModel) (state : CallState) :
    (denoteTransaction commitsThenReverts adversary state).state.world = state.world := by
  exact denoteTransaction_revert_world commitsThenReverts adversary state [0xde, 0xad] rfl

example (adversary : AdversaryModel) (state : CallState) :
    (denoteTransaction commitsThenReverts adversary state).state.returndata = [0xde, 0xad] := by
  exact denoteTransaction_revert_returndata commitsThenReverts adversary state [0xde, 0xad] rfl

example (adversary : AdversaryModel) (state : CallState) :
    (denoteTransaction commitsThenReverts adversary state).result = .revert [0xde, 0xad] := by
  exact denoteTransaction_revert_result commitsThenReverts adversary state [0xde, 0xad] rfl

example (adversary : AdversaryModel) (state : CallState) :
    (denoteTransaction commitsThenReverts adversary state).state.gasRemaining =
      (denote commitsThenReverts adversary state).2.gasRemaining := by
  exact denoteTransaction_revert_gasRemaining
    commitsThenReverts adversary state [0xde, 0xad] rfl

example (adversary : AdversaryModel) (state : CallState) :
    denoteTransaction commits adversary state =
      let (_, postState) := denote commits adversary state
      { result := .commit 7, state := postState } := by
  exact denoteTransaction_commit_eq commits adversary state 7 rfl

/-! ### Non-vacuous instantiation

A concrete adversary whose successful calls really mutate the world: site `k`
writes `42` into storage slot `k`.  The examples below show the mutation is
observable after each inner call commits, and that the transaction-level
revert restores the untouched initial world — so the rollback laws are
exercised on an execution whose intermediate state provably differs from both
the initial and the final state. -/

def mutatingAdversary : AdversaryModel where
  stateTransition := fun site w =>
    w.writeSlot site.siteId 42
  result := fun _ _ => .success []
  gasUsed := fun _ _ => 5

def demoState : CallState :=
  { world := Verity.defaultState, gasRemaining := 100 }

/-- The first call commits: slot 1 now holds 42 (it held 0 initially). -/
example : (denoteCall mutatingAdversary first demoState).state.world.storage 1 = 42 := by
  decide

/-- Both inner calls committed before the transaction-level revert: the
threaded post-state has both slots mutated. -/
example :
    (denote commitsThenReverts mutatingAdversary demoState).2.world.storage 1 = 42 ∧
    (denote commitsThenReverts mutatingAdversary demoState).2.world.storage 2 = 42 := by
  constructor <;> decide

/-- The enclosing revert rolls those committed mutations back to the initial
values — which differ from the intermediate ones, so the rollback is not
vacuous. -/
example :
    (denoteTransaction commitsThenReverts mutatingAdversary demoState).state.world.storage 1 = 0 ∧
    (denoteTransaction commitsThenReverts mutatingAdversary demoState).state.world.storage 2 = 0 := by
  constructor <;> decide

/-- On commit the same adversary's mutation is kept, ruling out a wrapper that
unconditionally restores the initial world. -/
example :
    (denoteTransaction commits mutatingAdversary demoState).state.world.storage 1 = 42 := by
  decide

/-- Gas charged by the reverted inner calls stays charged after rollback. -/
example :
    (denoteTransaction commitsThenReverts mutatingAdversary demoState).state.gasRemaining = 90 := by
  decide

/-! ### Result-aware loop, Lido shape

Three deposit-like calls iterate under a policy that aborts once the gas
budget drops to 85.  Every call succeeds and commits (slot k := 42), the
first two observations continue, the third aborts — so the enclosing
transaction reverts and discards three genuinely committed mutations. -/

def third : CallSite :=
  { siteId := 3, kind := .call, target := 30, gas := 30 }

def depositLoop : CallProgram (TransactionResult Nat) :=
  forEachCall
    (fun obs => if obs.state.gasRemaining ≤ 85 then .abort [0xbe, 0xef] else .next)
    0
    [first, second, third]

/-- All three planned sites are actually observed before the abort. -/
example :
    (CallsIn depositLoop mutatingAdversary demoState).map (·.siteId) = [1, 2, 3] := by
  decide

/-- Each iteration really committed: the threaded pre-revert world has all
three slots mutated. -/
example :
    (denote depositLoop mutatingAdversary demoState).2.world.storage 1 = 42 ∧
    (denote depositLoop mutatingAdversary demoState).2.world.storage 2 = 42 ∧
    (denote depositLoop mutatingAdversary demoState).2.world.storage 3 = 42 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The loop aborts through its policy and the transaction reverts with the
policy's data, rolling every committed iteration back to the initial world
while keeping the charged gas. -/
example :
    (denoteTransaction depositLoop mutatingAdversary demoState).result =
        .revert [0xbe, 0xef] ∧
    (denoteTransaction depositLoop mutatingAdversary demoState).state.world.storage 1 = 0 ∧
    (denoteTransaction depositLoop mutatingAdversary demoState).state.world.storage 3 = 0 ∧
    (denoteTransaction depositLoop mutatingAdversary demoState).state.gasRemaining = 85 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The generic trace-based law instantiated on the concrete loop: revert
result, rollback to the initial world, and intermediate world pinned to the
fold of the observed commits. -/
example :
    (denoteTransaction depositLoop mutatingAdversary demoState).state.world =
        demoState.world ∧
    (denote depositLoop mutatingAdversary demoState).2.world =
      commitWorlds mutatingAdversary demoState.world
        (CallsIn depositLoop mutatingAdversary demoState) := by
  have h := forEachCall_abort_discards_committed_prefix
    (fun obs => if obs.state.gasRemaining ≤ 85 then .abort [0xbe, 0xef] else .next)
    0 [first, second, third] mutatingAdversary demoState [0xbe, 0xef]
    (by decide)
    (by intro entry hentry
        refine ⟨[], ?_⟩
        rfl)
  exact ⟨h.2.1, h.2.2⟩

end Contracts.Examples.CallProgramRollback
