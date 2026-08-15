import Contracts.Common

/-!
# Observability of the executable linked-call family

Discriminating checks that the EDSL executable plane's external-call
primitives (`externalCallBind`, `callResultWords`, `tryExternalCallWords`,
and the `safeTransfer` family) thread an observable effect through
`ContractState.calls`. Each theorem *runs* a program and separates it from a
mutant at the journal:

* a duplicated call is observably different from a single call;
* an omitted call is observably different from the original program;
* reordered calls are observably different from the original order;
* a renamed callee or an altered/zeroed argument journals a different entry;
* a monadic revert after a call rolls the entry back through `Contract.run`,
  matching EVM top-level revert observability.

The mutant separations are stated over an arbitrary pre-state, not just
`defaultState`, so they hold in every reachable world.
-/

namespace Contracts.Smoke.ExternalCallObservability

open Contracts
open Verity hiding pure bind

private def notify (arg : Uint256) : Contract Unit :=
  Contracts.externalCallBind ([] : List String) "notify" [arg]

private def notifyEntry (arg : Uint256) : ExternalCall :=
  Contracts.linkedCallEntry "notify" [arg]

/-- One call appends exactly one journal entry. -/
theorem single_call_journals_one_entry (s : ContractState) :
    ((notify 1).run s).snd.calls = s.calls ++ [notifyEntry 1] := rfl

/-- (a) Duplication is observable: calling twice journals two entries, so the
double-call mutant is separated from the original program by `calls` — in
every pre-state. This is the executable-plane rejection of the double-send
mutant class. -/
theorem duplicated_call_observable (s : ContractState) :
    (((do notify 1; notify 1) : Contract Unit).run s).snd.calls ≠
      ((notify 1).run s).snd.calls := by
  show s.calls ++ [notifyEntry 1] ++ [notifyEntry 1] ≠ s.calls ++ [notifyEntry 1]
  intro h
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  omega

/-- (b) Omission is observable: dropping the second call of a two-call
program changes the journal in every pre-state. -/
theorem omitted_call_observable (s : ContractState) :
    (((do notify 1; notify 2) : Contract Unit).run s).snd.calls ≠
      ((notify 1).run s).snd.calls := by
  show s.calls ++ [notifyEntry 1] ++ [notifyEntry 2] ≠ s.calls ++ [notifyEntry 1]
  intro h
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  omega

/-- (b) Reordering is observable: `alpha; beta` and `beta; alpha` journal
different traces in every pre-state. -/
theorem reordered_calls_observable (s : ContractState) :
    (((do Contracts.externalCallBind ([] : List String) "alpha" ([1] : List Uint256)
          Contracts.externalCallBind ([] : List String) "beta" ([1] : List Uint256)) :
        Contract Unit).run s).snd.calls ≠
      (((do Contracts.externalCallBind ([] : List String) "beta" ([1] : List Uint256)
            Contracts.externalCallBind ([] : List String) "alpha" ([1] : List Uint256)) :
        Contract Unit).run s).snd.calls := by
  show s.calls ++ [Contracts.linkedCallEntry "alpha" [1]] ++
        [Contracts.linkedCallEntry "beta" [1]] ≠
      s.calls ++ [Contracts.linkedCallEntry "beta" [1]] ++
        [Contracts.linkedCallEntry "alpha" [1]]
  rw [List.append_assoc, List.append_assoc]
  intro h
  have hpair := List.append_cancel_left h
  have hhead : Contracts.linkedCallEntry "alpha" [1] =
      Contracts.linkedCallEntry "beta" [1] := by
    simpa using congrArg (List.headD · (Contracts.linkedCallEntry "alpha" [1])) hpair
  exact absurd hhead (by decide)

/-- (b) A renamed callee is observable: the journal entry carries the linked
name, so calling `transferFrom` instead of `transfer` is separated in every
pre-state. -/
theorem renamed_call_observable (s : ContractState) :
    ((Contracts.externalCallBind ([] : List String) "transfer"
        ([2] : List Uint256)).run s).snd.calls ≠
      ((Contracts.externalCallBind ([] : List String) "transferFrom"
        ([2] : List Uint256)).run s).snd.calls := by
  show s.calls ++ [Contracts.linkedCallEntry "transfer" [2]] ≠
      s.calls ++ [Contracts.linkedCallEntry "transferFrom" [2]]
  intro h
  have hpair := List.append_cancel_left h
  have hhead : Contracts.linkedCallEntry "transfer" [2] =
      Contracts.linkedCallEntry "transferFrom" [2] := by
    simpa using congrArg (List.headD · (Contracts.linkedCallEntry "transfer" [2])) hpair
  exact absurd hhead (by decide)

/-- (b) A zeroed argument is observable: `calldata` records the exact
argument words, so `notify 0` is separated from `notify 7`. -/
theorem zeroed_arg_observable (s : ContractState) :
    ((notify 7).run s).snd.calls ≠ ((notify 0).run s).snd.calls := by
  show s.calls ++ [notifyEntry 7] ≠ s.calls ++ [notifyEntry 0]
  intro h
  have hpair := List.append_cancel_left h
  have hhead : notifyEntry 7 = notifyEntry 0 := by
    simpa using congrArg (List.headD · (notifyEntry 7)) hpair
  exact absurd hhead (by decide)

/-- The double-send separation in `safeTransfer` form: sending twice is
observably different from sending once, in every pre-state. A deposit-style
theorem quantified over `calls` therefore rejects the double-send mutant by
running the program, not by auxiliary record arithmetic. -/
theorem double_send_observable (token toAddr : Address) (amount : Uint256)
    (s : ContractState) :
    (((do Contracts.safeTransfer token toAddr amount
          Contracts.safeTransfer token toAddr amount) : Contract Unit).run s).snd.calls ≠
      ((Contracts.safeTransfer token toAddr amount).run s).snd.calls := by
  intro h
  have hlen := congrArg List.length h
  have : (s.calls ++ [Contracts.linkedCallEntry "safeTransfer"
      [Verity.addressToWord token, Verity.addressToWord toAddr, amount]] ++
      [Contracts.linkedCallEntry "safeTransfer"
        [Verity.addressToWord token, Verity.addressToWord toAddr, amount]]).length =
      (s.calls ++ [Contracts.linkedCallEntry "safeTransfer"
        [Verity.addressToWord token, Verity.addressToWord toAddr, amount]]).length := hlen
  simp only [List.length_append, List.length_cons, List.length_nil] at this
  omega

/-- `callResult` and `tryExternalCall` journal their crossing too: the
success path records the callee name, argument words, control, and the
in-band stub word. -/
example :
    ((Contracts.callResultWords "quote" [3, 4] :
        Contract (Contracts.Call.Result Uint256)).run defaultState).snd.calls =
      [Contracts.linkedCallEntry "quote" [3, 4] .success
        [(Contracts.externalCallStubWord "quote" [3, 4] : Nat)]] := rfl

example :
    ((Contracts.tryExternalCallWords "quote" [3, 4] :
        Contract (Bool × Uint256)).run defaultState).snd.calls =
      [Contracts.linkedCallEntry "quote" [3, 4] .success
        [(Contracts.externalCallStubWord "quote" [3, 4] : Nat)]] := rfl

/-- The reserved `"fail"` callee journals a failure-control entry with no
returndata, and reports `success := false` in-band. -/
example :
    ((Contracts.callResultWords "fail" [9] :
        Contract (Contracts.Call.Result Uint256)).run defaultState).snd.calls =
      [Contracts.linkedCallEntry "fail" [9] .failure []] := rfl

example :
    ((Contracts.callResultWords "fail" [9] :
        Contract (Contracts.Call.Result Uint256)).run defaultState) =
      ContractResult.success
        { success := false, returndata := (Inhabited.default : Uint256) }
        { defaultState with
            calls := [Contracts.linkedCallEntry "fail" [9] .failure []] } := rfl

/-- A monadic revert after a call rolls the journal entry back through
`Contract.run`'s snapshot semantics: a fully reverted execution leaves
nothing observable, matching EVM top-level behaviour (and the documented
contrast with the model plane's revert-surviving journal). -/
theorem revert_rolls_back_journal (token toAddr : Address) (amount : Uint256)
    (s : ContractState) :
    (((do Contracts.safeTransfer token toAddr amount
          require false "boom") : Contract Unit).run s) =
      ContractResult.revert "boom" s := rfl

end Contracts.Smoke.ExternalCallObservability
