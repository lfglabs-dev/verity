import Verity.Core.Model.MultiContract

/-!
# Checked Vault-to-Lido call consumer

This is a concrete consumer of the `CallFrame` boundary.  The vault makes a
payable `call` to a Lido-style `submit` endpoint.  A successful submit credits
the callee, updates its shares slot, and exposes a receipt through returndata.
A revert is intentionally given a mutated callee post-state; the frame model
must discard it and restore both accounts while retaining the observable
revert entry on the caller.
-/

namespace Verity.Proofs.CheckedExternalCallConsumer

open Compiler.CompilationModel.DenoteExternalCalls
open Verity.MultiContract

def vault : Address := (30 : Address)
def lido : Address := (31 : Address)

def lidoSharesSlot : Nat := 0
def submitReceipt : Nat := 0x51
def submitRevertData : List Nat := [0xde, 0xad]

def vaultBefore : ContractState :=
  { defaultState with thisAddress := vault, selfBalance := 10 }

def lidoBefore : ContractState :=
  { defaultState with thisAddress := lido, selfBalance := 7 }

def lidoWorld : MultiWorld :=
  { accounts := [{ address := vault, state := vaultBefore },
                 { address := lido, state := lidoBefore }] }

def lidoSubmit : CallSite :=
  { siteId := 2084
    kind := .call
    target := lido.toNat
    value := 3
    calldata := [0x73, 0x75, 0x62, 0x6d, 0x69, 0x74]
    gas := 50_000 }

def submitSuccess (frame : CallFrame) : CalleeExecution :=
  { result := .success [submitReceipt]
    post := (frame.calleeEntry).writeSlot lidoSharesSlot
      (frame.calleeEntry.storage lidoSharesSlot + frame.site.value) }

/-- This post-state is deliberately different from the entry state.  The
rollback theorems below establish that a callee cannot commit it by reverting. -/
def submitRevert (frame : CallFrame) : CalleeExecution :=
  { result := .revert submitRevertData
    post := (frame.calleeEntry).writeSlot lidoSharesSlot 999 }

theorem lido_submit_entry_installs_caller_context :
    callEntry lidoWorld vault lido lidoSubmit = some
      { caller := vault
        callee := lido
        site := lidoSubmit
        callerBefore := vaultBefore
        calleeBefore := lidoBefore
        calleeEntry := withCallContext lidoBefore vault lido 3 } := by
  rfl

/-- Success commits the caller debit, payable callee credit, and Lido share
storage transition in one framed external call. -/
theorem lido_submit_success_world :
    (call lidoWorld vault lido lidoSubmit submitSuccess).map (fun observation =>
      observation.world) =
      some
        (upsert
          (upsert lidoWorld vault
            { vaultBefore with
              selfBalance := vaultBefore.selfBalance - 3
              calls := vaultBefore.calls ++
                [framedJournalEntry
                  { caller := vault
                    callee := lido
                    site := lidoSubmit
                    callerBefore := vaultBefore
                    calleeBefore := lidoBefore
                    calleeEntry := withCallContext lidoBefore vault lido 3 }
                  (.success [submitReceipt])] })
          lido
          ((withCallContext lidoBefore vault lido 3).writeSlot lidoSharesSlot 3)) := by
  rfl

theorem lido_submit_success_returndata :
    (call lidoWorld vault lido lidoSubmit submitSuccess).map (fun observation =>
      observation.result.returndata) = some [submitReceipt] := by
  rfl

theorem lido_submit_success_caller_balance :
    (call lidoWorld vault lido lidoSubmit submitSuccess).map (fun observation =>
      (lookup observation.world vault).selfBalance) = some 7 := by
  rfl

theorem lido_submit_success_callee_transition :
    (call lidoWorld vault lido lidoSubmit submitSuccess).map (fun observation =>
      ((lookup observation.world lido).selfBalance,
       (lookup observation.world lido).storage lidoSharesSlot,
       (lookup observation.world lido).sender,
       (lookup observation.world lido).thisAddress,
       (lookup observation.world lido).msgValue)) =
      some (10, 3, vault, lido, 3) := by
  rfl

/-- A reverting callee exposes its revert payload but cannot commit either its
payable credit or its attempted shares write; the caller debit is rolled back
as well. -/
theorem lido_submit_revert_rolls_back :
    (call lidoWorld vault lido lidoSubmit submitRevert).map (fun observation =>
      ((lookup observation.world vault).selfBalance,
       (lookup observation.world lido).selfBalance,
       (lookup observation.world lido).storage lidoSharesSlot,
       observation.result.returndata,
       (lookup observation.world vault).calls)) =
      some
        (10, 7, 0, submitRevertData,
         [framedJournalEntry
           { caller := vault
             callee := lido
             site := lidoSubmit
             callerBefore := vaultBefore
             calleeBefore := lidoBefore
             calleeEntry := withCallContext lidoBefore vault lido 3 }
           (.revert submitRevertData)]) := by
  rfl

end Verity.Proofs.CheckedExternalCallConsumer
