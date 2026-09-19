import Verity.Core.Model.DenoteExternalCalls

/-!
# Source-level external calls in the `Contract` monad

`Contract.run` alone cannot observe a call boundary: nothing in
`ContractState` records that a call happened, what it carried, or what came
back.  This module lifts the journaled call denotation
(`DenoteExternalCalls.denoteCallJournaled`) into the `Contract` monad so
source-level contracts observe `kind`/`value`/`control`/`returndata` directly
and every crossing lands in the append-only `ContractState.calls` journal.

Design points:

* **Never a monadic revert.**  A failed or reverted callee is reported
  in-band through `ExternalCallResult.control`; the caller inspects it and
  decides.  Raising `ContractResult.revert` instead would erase the journal
  through `Contract.run`'s snapshot rollback, making the failed call
  unobservable.  Callers wanting bubbling semantics compose with
  `requireSuccess` below.
* **No gas channel.**  The `Contract` monad carries no gas, so the call's
  allowance is the site's own `gas` field; `chargedGas` caps the adversary's
  claim by it.  Opcode-level gas accounting stays in the dedicated
  `GasCoupling` lane.
* **FFI-backed externals** (e.g. an SSZ Merkle verifier over the SHA-256
  precompile) need no dedicated feature: model them as an ordinary
  `staticcall` site whose `AdversaryModel.result` is constrained by the
  relevant trust assumption.
-/

namespace Compiler.CompilationModel.DenoteExternalCalls

open Verity

/-- Perform one external call from inside the `Contract` monad: the callee's
behaviour is the explicit `adversary` parameter, the observed result is
returned in-band, and the call is appended to the caller's journal. -/
def externalCall (adversary : AdversaryModel) (site : CallSite) :
    Contract ExternalCallResult :=
  fun s =>
    let observation := denoteCallJournaled adversary site
      { world := s, gasRemaining := site.gas }
    ContractResult.success observation.result
      { observation.state.world with
        returndata := observation.result.returndata.map Denote.wordNormalize }

/-- Unfolding law: `externalCall` succeeds monadically with the adversary's
response and the journaled post-world. -/
theorem externalCall_run (adversary : AdversaryModel) (site : CallSite)
    (s : ContractState) :
    (externalCall adversary site).run s =
      ContractResult.success (adversary.result site s)
        { (denoteCallJournaled adversary site
            { world := s, gasRemaining := site.gas }).state.world with
          returndata := (adversary.result site s).returndata.map Denote.wordNormalize } := rfl

/-- The returned result is exactly the adversary's response on the pre-call
world. -/
@[simp] theorem externalCall_result (adversary : AdversaryModel)
    (site : CallSite) (s : ContractState) :
    ((externalCall adversary site).run s).fst = adversary.result site s := rfl

/-- One call appends exactly one journal entry. -/
@[simp] theorem externalCall_calls (adversary : AdversaryModel)
    (site : CallSite) (s : ContractState) :
    ((externalCall adversary site).run s).snd.calls =
      s.calls ++ [journalEntry site (adversary.result site s)] := rfl

/-- Caller-side rollback: when a mutable call fails or reverts, the post
world is the pre world except the journal entry. -/
theorem externalCall_rollback (adversary : AdversaryModel) (site : CallSite)
    (s : ContractState) (data : List Nat)
    (hkind : site.kind = .call ∨ site.kind = .delegatecall)
    (hresult : adversary.result site s = .failure data ∨
      adversary.result site s = .revert data) :
    ((externalCall adversary site).run s).snd =
      { s with
        calls := s.calls ++ [journalEntry site (adversary.result site s)]
        returndata := (adversary.result site s).returndata.map Denote.wordNormalize } := by
  rw [externalCall_run]
  rw [denoteCallJournaled_rollback_world adversary site
    { world := s, gasRemaining := site.gas } data hkind hresult]
  simp [denoteCall]

/-- A static call preserves the caller world except the journal entry. -/
theorem externalCall_staticcall (adversary : AdversaryModel) (site : CallSite)
    (s : ContractState) (hkind : site.kind = .staticcall) :
    ((externalCall adversary site).run s).snd =
      { s with
        calls := s.calls ++ [journalEntry site (adversary.result site s)]
        returndata := (adversary.result site s).returndata.map Denote.wordNormalize } := by
  rw [externalCall_run]
  rw [denoteCallJournaled_staticcall_world adversary site
    { world := s, gasRemaining := site.gas } hkind]
  simp [denoteCall]

/-- Bubbling wrapper: revert the caller when the callee did not succeed.
This intentionally re-enters `Contract.run`'s snapshot rollback — including
the journal — matching EVM top-level semantics where a fully reverted
execution leaves nothing observable. -/
def externalCallRequireSuccess (adversary : AdversaryModel) (site : CallSite)
    (msg : String := "external call failed") : Contract (List Nat) :=
  Verity.bind (externalCall adversary site) fun result =>
    fun s =>
      match result with
      | .success data => ContractResult.success data s
      | .failure _ | .revert _ => ContractResult.revert msg s

end Compiler.CompilationModel.DenoteExternalCalls
