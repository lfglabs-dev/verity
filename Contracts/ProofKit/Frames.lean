import Contracts.ProofKit.Stepping

/-!
# Storage frames and external calls for the executable EDSL

A theorem about a contract body often only needs "this step left storage alone": `mstore`,
`copyBytes`, a static call, or an external call whose callee cannot write this contract's storage.
These lemmas say it once.

- `KeepsStorage s t`: `t` has `s`'s storage, chain id and contract address. It is reflexive and
  transitive, so a sequence of steps is framed by composing the frames of its steps. It is the
  opposite of `Compiler.Proofs.StateLenses.StorageWordsFrame`, which says only storage changed.
- `keepsStorage_of_mstore`, `keepsStorage_of_copyBytes`: memory writes keep storage.
- `ecmSite mod args`: the call site an ECM crossing (`ecmCallTypedWords`) presents to the
  adversary.
- `ecmCallTypedWords_success`: a successful ECM crossing returns the adversary's answer at that
  site, decoded, from a state that keeps storage. Afterwards storage is the pre-call state's for a
  static call, or the adversary's transition's for a mutable one.
- `NonInterfering adv`: the adversary's transitions keep storage. On the EVM only a contract's own
  code writes its storage, so this holds of every callee that does not reenter.
- `ecmCallTypedWords_keepsStorage`: under `NonInterfering`, every successful ECM crossing keeps
  storage; `ecmCallTypedWords_keepsStorage_of_staticcall`: a static one does for every adversary.
-/

namespace Contracts.ProofKit

open Verity

/-- `t` has `s`'s storage, chain id and contract address (memory, balance, returndata and the call
journal may differ). -/
structure KeepsStorage (s t : ContractState) : Prop where
  storageWords : t.storageWords = s.storageWords
  chainId : t.chainId = s.chainId
  thisAddress : t.thisAddress = s.thisAddress

namespace KeepsStorage

theorem refl (s : ContractState) : KeepsStorage s s := ⟨rfl, rfl, rfl⟩

theorem trans {a b c : ContractState} (h₁ : KeepsStorage a b) (h₂ : KeepsStorage b c) :
    KeepsStorage a c :=
  ⟨h₂.storageWords.trans h₁.storageWords, h₂.chainId.trans h₁.chainId,
    h₂.thisAddress.trans h₁.thisAddress⟩

end KeepsStorage

theorem keepsStorage_of_mstore {o v : Uint256} {s t : ContractState} {u : Unit}
    (h : Contracts.mstore o v s = .success u t) : KeepsStorage s t := by
  rw [mstore_ok h]; exact ⟨rfl, rfl, rfl⟩

theorem keepsStorage_of_copyBytes {data : ByteArray} {o : Uint256} {s t : ContractState} {u : Unit}
    (h : Contracts.copyBytes data o s = .success u t) : KeepsStorage s t := by
  rw [copyBytes_ok h]; exact ⟨rfl, rfl, rfl⟩

/-- The adversary's state transitions keep this contract's storage, chain id and address. -/
def NonInterfering (adv : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel) : Prop :=
  ∀ site w, KeepsStorage w (adv.stateTransition site w)

/-- The call kind of an ECM crossing: `staticcall` for a static module, `call` otherwise. -/
def ecmKind (mod : Compiler.ECM.ExternalCallModule) :
    Compiler.CompilationModel.DenoteExternalCalls.CallKind :=
  if mod.summaryMutability == Compiler.ECM.StatefulExternal.Mutability.staticcall then .staticcall
  else .call

/-- The call site `ecmCallTypedWords mod adv args siteId` presents to the adversary. -/
def ecmSite (mod : Compiler.ECM.ExternalCallModule) (args : List Uint256) (siteId : Nat := 0) :
    Compiler.CompilationModel.DenoteExternalCalls.CallSite :=
  linkedCallSite mod.summaryName args mod.resultVars.length (ecmKind mod)
    (ecmTargetWord mod args) (ecmValueWord mod args) [] siteId

/-- Paying for an ECM crossing (debiting this contract's balance) keeps storage. -/
theorem keepsStorage_of_debitEcmSelfBalance {s paid : ContractState} {target value : Nat}
    (h : Compiler.CompilationModel.DenoteFunctionCalls.debitEcmSelfBalance s target value =
      some paid) : KeepsStorage s paid := by
  unfold Compiler.CompilationModel.DenoteFunctionCalls.debitEcmSelfBalance at h
  split_ifs at h <;> (injection h with h; subst h; exact ⟨rfl, rfl, rfl⟩)

/-- The state after the adversary answers `site` successfully from `paid`: its storage is
`paid`'s for a static call and the adversary transition's otherwise. -/
theorem keepsStorage_after_call (adv : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel)
    (mod : Compiler.ECM.ExternalCallModule) (args : List Uint256) (siteId : Nat)
    (paid : ContractState) (ws : List Nat)
    (hres : adv.result (ecmSite mod args siteId) paid = .success ws) (rd : List Nat) :
    KeepsStorage
      (if ecmKind mod = .staticcall then paid
        else adv.stateTransition (ecmSite mod args siteId) paid)
      { (Compiler.CompilationModel.DenoteExternalCalls.denoteCallJournaled adv
          (ecmSite mod args siteId) { world := paid, gasRemaining := 0 }).state.world with
        returndata := rd } := by
  have hkind : (ecmSite mod args siteId).kind = ecmKind mod := rfl
  simp only [Compiler.CompilationModel.DenoteExternalCalls.denoteCallJournaled,
    Compiler.CompilationModel.DenoteExternalCalls.denoteCall, hres, hkind]
  rcases hk : ecmKind mod with _ | _ | _ <;> simp only [reduceCtorEq, if_true, if_false] <;>
    exact ⟨rfl, rfl, rfl⟩

/-- A successful ECM crossing returns the adversary's answer at `ecmSite`, decoded, from a state
`paid` that keeps storage; afterwards storage is `paid`'s for a static call and the adversary
transition's otherwise. -/
theorem ecmCallTypedWords_success {α : Type} [ExternalResult α]
    {mod : Compiler.ECM.ExternalCallModule}
    {adv : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel}
    {args : List Uint256} {siteId : Nat} {s s' : ContractState} {x : α}
    (h : Contracts.ecmCallTypedWords mod adv args siteId s = .success x s') :
    ∃ paid ws, KeepsStorage s paid ∧ adv.result (ecmSite mod args siteId) paid = .success ws ∧
      ws.length = mod.resultVars.length ∧
      x = ExternalResult.fromWords (ws.map Verity.Core.Uint256.ofNat) ∧
      KeepsStorage (if ecmKind mod = .staticcall then paid
        else adv.stateTransition (ecmSite mod args siteId) paid) s' := by
  unfold Contracts.ecmCallTypedWords at h
  dsimp only at h
  rw [show (if mod.summaryMutability == Compiler.ECM.StatefulExternal.Mutability.staticcall then
      Compiler.CompilationModel.DenoteExternalCalls.CallKind.staticcall else .call) = ecmKind mod
      from rfl] at h
  split at h
  · simp at h
  · rename_i paid hpaid
    split at h
    · rename_i ws post hcall
      split at h
      · rename_i hlen
        injection h with hx hs'
        unfold Contracts.commonExternalCall at hcall
        change (Compiler.CompilationModel.DenoteExternalCalls.externalCall adv _).run paid = _
          at hcall
        rw [Compiler.CompilationModel.DenoteExternalCalls.externalCall_run] at hcall
        injection hcall with hres hpost
        refine ⟨paid, ws, keepsStorage_of_debitEcmSelfBalance hpaid, hres, hlen, hx.symm, ?_⟩
        subst hs' hpost
        exact keepsStorage_after_call adv mod args siteId paid ws hres _
      · simp at h
    · simp at h
    · simp at h
    · simp at h

/-- Under `NonInterfering`, a successful ECM crossing keeps storage. -/
theorem ecmCallTypedWords_keepsStorage {α : Type} [ExternalResult α]
    {mod : Compiler.ECM.ExternalCallModule}
    {adv : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel}
    {args : List Uint256} {siteId : Nat} {s s' : ContractState} {x : α}
    (hadv : NonInterfering adv)
    (h : Contracts.ecmCallTypedWords mod adv args siteId s = .success x s') :
    KeepsStorage s s' := by
  obtain ⟨paid, _, hpaid, _, _, _, hpost⟩ := ecmCallTypedWords_success h
  refine hpaid.trans ?_
  split at hpost
  · exact hpost
  · exact (hadv _ paid).trans hpost

/-- A successful static ECM crossing keeps storage, whatever the adversary. -/
theorem ecmCallTypedWords_keepsStorage_of_staticcall {α : Type} [ExternalResult α]
    {mod : Compiler.ECM.ExternalCallModule}
    {adv : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel}
    {args : List Uint256} {siteId : Nat} {s s' : ContractState} {x : α}
    (hk : ecmKind mod = .staticcall)
    (h : Contracts.ecmCallTypedWords mod adv args siteId s = .success x s') :
    KeepsStorage s s' := by
  obtain ⟨paid, _, hpaid, _, _, _, hpost⟩ := ecmCallTypedWords_success h
  rw [if_pos hk] at hpost
  exact hpaid.trans hpost

end Contracts.ProofKit
