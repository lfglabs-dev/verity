import Verity.Core.Model.CallProgramRollback
import Verity.Core.Model.ECM

/-!
# Summary-conforming adversaries

`AdversaryModel` (the executable call boundary) and
`StatefulExternal.Summary` (the typed ECM interface contract) previously lived
in separate worlds.  This module states what it means for an adversary to
*conform* to a summary environment, so caller proofs can quantify over
summary-respecting adversaries instead of arbitrary ones, and typed ECMs and
source-level calls are interpreted against the same external-world boundary.

Conformance obligations:
- every site's opcode-level mutability agrees with its summary's declared one;
- a `success` response satisfies the summary's pre/post on the externally
  visible projection of the committed caller world;
- a `revert` response satisfies the summary's revert relation;
- a `failure` response carries no summary obligation: it models an opaque
  exceptional failure, and `denoteCall` never commits it.

The staticcall law is derived, not declared: a conforming adversary's
transition on a staticcall site cannot change the external world, because the
summary's `interprets` forces the committed world to equal the request world.
-/
namespace Compiler.CompilationModel.DenoteExternalCalls

open Compiler.ECM.StatefulExternal

/-- Externally visible projection of the caller-threaded world: the modeled
storage of explicitly identified foreign contracts. -/
def externalWorldOf (w : Verity.ContractState) : ExternalWorld :=
  { accountState := fun account slot => (w.contractStorage account slot).val }

/-- The request a call site issues from a given caller world. -/
def requestOf (site : CallSite) (w : Verity.ContractState) : Request :=
  { caller := w.thisAddress.val
    target := site.target
    selector := none
    calldata := site.calldata
    value := site.value
    world := externalWorldOf w }

/-- Assignment of an interface summary to every call site. -/
structure SummaryEnv where
  summaryFor : CallSite → Summary

/-- The site's opcode-level mutability agrees with the summary's declared
mutability. -/
def KindMatches (site : CallSite) (summary : Summary) : Prop :=
  site.kind = .staticcall ↔ summary.mutability = .staticcall

/-- What one observed response must satisfy under a summary environment. -/
def SummaryConsistent (env : SummaryEnv) (adversary : AdversaryModel)
    (site : CallSite) (world : Verity.ContractState) : Prop :=
  match adversary.result site world with
  | .success data =>
      (env.summaryFor site).interprets (requestOf site world)
        (.success (externalWorldOf (adversary.stateTransition site world)) data)
  | .revert data =>
      (env.summaryFor site).interprets (requestOf site world) (.revert data)
  | .failure _ => True

/-- An adversary conforms to a summary environment when every response at
every site and world is summary-consistent and mutability-faithful. -/
def Conforms (env : SummaryEnv) (adversary : AdversaryModel) : Prop :=
  ∀ site world,
    KindMatches site (env.summaryFor site) ∧ SummaryConsistent env adversary site world

/-- A successful response of a conforming adversary satisfies the summary's
precondition and its post relation on the committed external world. -/
theorem Conforms.success_post {env : SummaryEnv} {adversary : AdversaryModel}
    (h : Conforms env adversary) (site : CallSite) (world : Verity.ContractState)
    (data : List Nat) (hres : adversary.result site world = .success data) :
    (env.summaryFor site).pre (requestOf site world) ∧
      (env.summaryFor site).post (requestOf site world)
        (externalWorldOf (adversary.stateTransition site world)) data := by
  have hcons := (h site world).2
  unfold SummaryConsistent at hcons
  rw [hres] at hcons
  exact ⟨hcons.1, hcons.2.1⟩

/-- A reverting response of a conforming adversary satisfies the summary's
precondition and revert relation. -/
theorem Conforms.revert_allowed {env : SummaryEnv} {adversary : AdversaryModel}
    (h : Conforms env adversary) (site : CallSite) (world : Verity.ContractState)
    (data : List Nat) (hres : adversary.result site world = .revert data) :
    (env.summaryFor site).pre (requestOf site world) ∧
      (env.summaryFor site).revert (requestOf site world) data := by
  have hcons := (h site world).2
  unfold SummaryConsistent at hcons
  rw [hres] at hcons
  exact ⟨hcons.1, hcons.2⟩

/-- Derived staticcall law: on a staticcall site, even the adversary's own
transition is externally unobservable — the summary's interpretation pins the
committed external world to the request world.  Combined with
`denoteCall_staticcall_world` (the caller world is never threaded on static
sites) this closes the staticcall non-mutation story on both sides of the
boundary. -/
theorem Conforms.staticcall_preserves_externalWorld {env : SummaryEnv}
    {adversary : AdversaryModel} (h : Conforms env adversary) (site : CallSite)
    (world : Verity.ContractState) (data : List Nat)
    (hkind : site.kind = .staticcall)
    (hres : adversary.result site world = .success data) :
    externalWorldOf (adversary.stateTransition site world) = externalWorldOf world := by
  have hkm := (h site world).1
  have hcons := (h site world).2
  unfold SummaryConsistent at hcons
  rw [hres] at hcons
  have hstatic : (env.summaryFor site).mutability = .staticcall := hkm.mp hkind
  simpa [requestOf] using
    Summary.static_success_preserves_world hstatic hcons

/-- Lift conformance to whole programs: every dynamically observed call of any
`CallProgram` under a conforming adversary is summary-consistent at its actual
pre-call world. -/
theorem Conforms.observed {env : SummaryEnv} {adversary : AdversaryModel}
    (h : Conforms env adversary) (prog : CallProgram α) (state : CallState) :
    ∀ entry ∈ ObservedCalls prog adversary state,
      SummaryConsistent env adversary entry.site entry.preWorld := by
  intro entry _
  exact (h entry.site entry.preWorld).2

/-- Transaction-level packaging: under a conforming adversary, a reverted
transaction restores the initial caller world and every observed call of the
run was summary-consistent — the rollback claim and the boundary-contract
claim hold together on the same execution. -/
theorem conforming_transaction_revert {env : SummaryEnv}
    {adversary : AdversaryModel} (h : Conforms env adversary)
    (prog : CallProgram (TransactionResult α)) (state : CallState)
    (data : List Nat)
    (habort : (denote prog adversary state).1 = .revert data) :
    (denoteTransaction prog adversary state).state.world = state.world ∧
      ∀ entry ∈ ObservedCalls prog adversary state,
        SummaryConsistent env adversary entry.site entry.preWorld :=
  ⟨denoteTransaction_revert_world prog adversary state data habort,
   h.observed prog state⟩

/-- A program whose observed calls are all static preserves the caller world,
for any adversary. -/
theorem denoteCallProgram_all_static_preserves_world
    (prog : CallProgram α) (adversary : AdversaryModel) (state : CallState)
    (h : ∀ entry ∈ ObservedCalls prog adversary state,
      entry.site.kind = .staticcall) :
    (denote prog adversary state).2.world = state.world :=
  denoteCallProgram_all_revert_preserves_world prog adversary state
    (fun entry hentry => Or.inl (h entry hentry))

end Compiler.CompilationModel.DenoteExternalCalls
