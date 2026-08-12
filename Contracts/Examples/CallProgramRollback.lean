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
    { w with storage := fun slot => if slot == site.siteId then 42 else w.storage slot }
  result := fun _ _ => .success []
  gasUsed := fun _ _ => 5

def demoState : CallState :=
  { world := Verity.defaultState, gasRemaining := 100 }

/-- The first call commits: slot 1 now holds 42 (it held 0 initially). -/
example : (denoteCall mutatingAdversary first demoState).state.world.storage 1 = 42 := by
  native_decide

/-- Both inner calls committed before the transaction-level revert: the
threaded post-state has both slots mutated. -/
example :
    (denote commitsThenReverts mutatingAdversary demoState).2.world.storage 1 = 42 ∧
    (denote commitsThenReverts mutatingAdversary demoState).2.world.storage 2 = 42 := by
  constructor <;> native_decide

/-- The enclosing revert rolls those committed mutations back to the initial
values — which differ from the intermediate ones, so the rollback is not
vacuous. -/
example :
    (denoteTransaction commitsThenReverts mutatingAdversary demoState).state.world.storage 1 = 0 ∧
    (denoteTransaction commitsThenReverts mutatingAdversary demoState).state.world.storage 2 = 0 := by
  constructor <;> native_decide

/-- On commit the same adversary's mutation is kept, ruling out a wrapper that
unconditionally restores the initial world. -/
example :
    (denoteTransaction commits mutatingAdversary demoState).state.world.storage 1 = 42 := by
  native_decide

/-- Gas charged by the reverted inner calls stays charged after rollback. -/
example :
    (denoteTransaction commitsThenReverts mutatingAdversary demoState).state.gasRemaining = 90 := by
  native_decide

end Contracts.Examples.CallProgramRollback
