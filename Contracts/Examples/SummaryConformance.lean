import Verity.Core.Model.SummaryBridge
import Contracts.Examples.CallProgramRollback

/-! A concrete summary environment and a conforming adversary: the callee
always returns `[1]`, commits nothing externally visible, and never reverts.
The conformance proof is constructive — no axioms, no vacuous branches — and
the final example threads it through a reverted transaction. -/
namespace Contracts.Examples.SummaryConformance

open Compiler.CompilationModel.DenoteExternalCalls
open Compiler.ECM.StatefulExternal
open Contracts.Examples.CallProgramRollback (first second demoState commitsThenReverts)

/-- Every site gets a "ping" summary: success returns `[1]` and leaves the
external world unchanged; reverting is never allowed. -/
def pingEnv : SummaryEnv where
  summaryFor site :=
    { name := "ping"
      mutability := if site.kind = .staticcall then .staticcall else .call
      post := fun req world data => data = [1] ∧ world = req.world
      revert := fun _ _ => False }

/-- Succeeds with `[1]` everywhere and only mutates the caller's own storage —
its external projection is untouched, as `pingEnv` demands. -/
def pingAdversary : AdversaryModel where
  stateTransition := fun site w =>
    { w with storage := fun slot => if slot == site.siteId then 7 else w.storage slot }
  result := fun _ _ => .success [1]
  gasUsed := fun _ _ => 3

theorem pingAdversary_conforms : Conforms pingEnv pingAdversary := by
  intro site world
  constructor
  · unfold KindMatches pingEnv
    cases h : site.kind <;> simp [h]
  · unfold SummaryConsistent
    refine ⟨trivial, ⟨rfl, rfl⟩, fun _ => rfl⟩

/-- The summary's post relation holds at every observed call of a real run. -/
example :
    ∀ entry ∈ ObservedCalls commitsThenReverts pingAdversary demoState,
      SummaryConsistent pingEnv pingAdversary entry.site entry.preWorld :=
  pingAdversary_conforms.observed commitsThenReverts demoState

/-- Combined transaction law on a run that really executes and then reverts:
initial world restored and every observed call summary-consistent. -/
example :
    (denoteTransaction commitsThenReverts pingAdversary demoState).state.world =
        demoState.world ∧
      ∀ entry ∈ ObservedCalls commitsThenReverts pingAdversary demoState,
        SummaryConsistent pingEnv pingAdversary entry.site entry.preWorld :=
  conforming_transaction_revert pingAdversary_conforms
    commitsThenReverts demoState [0xde, 0xad] (by decide)

/-- The run is not vacuous: the caller-local mutation of the first site is
visible in the threaded state before the transaction-level rollback. -/
example :
    (denote commitsThenReverts pingAdversary demoState).2.world.storage 1 = 7 := by
  decide

/-- Derived staticcall law instantiated: on a static site the conforming
adversary's transition is externally unobservable. -/
example (world : Verity.ContractState) :
    externalWorldOf (pingAdversary.stateTransition
        { siteId := 9, kind := .staticcall, target := 40, gas := 10 } world) =
      externalWorldOf world :=
  pingAdversary_conforms.staticcall_preserves_externalWorld _ world [1] rfl rfl

end Contracts.Examples.SummaryConformance
