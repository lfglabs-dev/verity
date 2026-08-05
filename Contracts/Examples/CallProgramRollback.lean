import Verity.Core.Model.CallProgramRollback

/-! A two-call always-revert example using the whole-program wrapper. -/
namespace Contracts.Examples.CallProgramRollback

open Compiler.CompilationModel.DenoteExternalCalls

def first : CallSite :=
  { siteId := 1, kind := .call, target := 10, gas := 30 }

def second : CallSite :=
  { siteId := 2, kind := .delegatecall, target := 20, gas := 30 }

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

end Contracts.Examples.CallProgramRollback
