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

end Contracts.Examples.CallProgramRollback
