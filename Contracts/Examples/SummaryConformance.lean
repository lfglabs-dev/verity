import Verity.Core.Model.SummaryBridge
import Contracts.Examples.CallProgramRollback

/-! A concrete summary environment and a conforming adversary: the callee
always returns `[1]`, writes one caller slot on non-static calls, and never reverts.
The conformance proof is constructive — no axioms, no vacuous branches — and
the final example threads it through a reverted transaction. -/
namespace Contracts.Examples.SummaryConformance

open Compiler.CompilationModel.DenoteExternalCalls
open Compiler.ECM.StatefulExternal
open Contracts.Examples.CallProgramRollback (first second demoState commitsThenReverts)

/-- The precise storage update promised by a non-static ping. Account zero
is the caller's unqualified storage namespace, not an excluded account. -/
def pingWorld (site : CallSite) (world : ExternalWorld) : ExternalWorld :=
  if site.kind = .staticcall then world else
    { accountState := fun account slot =>
        if account = 0 ∧ slot = site.siteId then 7 else world.accountState account slot }

/-- Success returns `[1]` and commits exactly `pingWorld`; reverting is
never allowed. Static calls preserve every observed account, including zero. -/
def pingEnv : SummaryEnv where
  summaryFor site :=
    { name := "ping"
      mutability := if site.kind = .staticcall then .staticcall else .call
      post := fun req world data => data = [1] ∧ world = pingWorld site req.world
      revert := fun _ _ => False }

/-- Succeeds with `[1]` everywhere; only non-static calls write caller storage. -/
def pingAdversary : AdversaryModel where
  stateTransition := fun site w =>
    if site.kind = .staticcall then w else w.writeSlot site.siteId 7
  result := fun _ _ => .success [1]
  gasUsed := fun _ _ => 3

theorem pingAdversary_conforms : Conforms pingEnv pingAdversary := by
  intro site world
  constructor
  · unfold KindMatches pingEnv
    cases h : site.kind <;> simp [h]
  · have hworld : externalWorldOf (pingAdversary.stateTransition site world) =
        pingWorld site (externalWorldOf world) := by
      by_cases hs : site.kind = .staticcall
      · simp [pingAdversary, pingWorld, hs]
      · simp only [pingAdversary, pingWorld, hs, ↓reduceIte]
        unfold externalWorldOf
        congr 1
        funext account slot
        by_cases ha : account = 0 <;> by_cases hk : slot = site.siteId <;>
          simp [Verity.ContractState.contractStorage,
            Verity.ContractState.storage, Verity.ContractState.writeSlot, ha, hk] <;> rfl
    refine ⟨trivial, ⟨rfl, hworld⟩, ?_⟩
    by_cases hs : site.kind = .staticcall
    · simp [pingEnv, pingAdversary, requestOf, hs]
    · simp [pingEnv, hs]

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

/-- Regression: account zero remains observable to summaries. Filtering it
out would make this inequality false while hiding caller writes. -/
example : externalWorldOf (Verity.defaultState.writeSlot 1 7) ≠
    externalWorldOf Verity.defaultState := by
  intro h
  have hslot := congrArg (fun w => w.accountState 0 1) h
  exact (by decide : (7 : Nat) ≠ 0) hslot

/-- The summary pins the complete post-world, including unrelated accounts. -/
example (world : Verity.ContractState) (account slot : Nat) (h : account ≠ 0) :
    (externalWorldOf (pingAdversary.stateTransition first world)).accountState account slot =
      (externalWorldOf world).accountState account slot := by
  simp [externalWorldOf, pingAdversary, first, Verity.ContractState.contractStorage,
    Verity.ContractState.writeSlot, h]

end Contracts.Examples.SummaryConformance
