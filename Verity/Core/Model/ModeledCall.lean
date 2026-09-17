import Verity.Core.Model.MultiContract

/-!
# Modeled-callee hops

Feature 2 model-plane denotation: a bound interface call is a CALL-shaped hop
in `Verity.MultiContract.MultiWorld`. Compilation-model lowering stays an ABI
call; this module does not claim bytecode identity.

`callEntry` still rejects `caller = callee` (ordinary inter-contract CALL).
Same-address `this.f()` uses `selfCallEntry` / `executeSelfCall` — a new frame
with `sender` replaced, not the DELEGATECALL path `selfDelegateEntry`.
-/

namespace Verity.MultiContract

open Compiler.CompilationModel.DenoteExternalCalls
open Verity

/-- Non-payable CALL site used by modeled hops (`msg.value = 0`). -/
def modeledSite (callee : Address) (name : String := "modeled") : CallSite where
  siteId := callee.toNat
  kind := .call
  target := callee.toNat
  value := 0
  calldata := []
  name := name
  gas := 0

/-- CALL-shaped same-address hop. `sender` becomes the contract itself. -/
def selfCallEntry (w : MultiWorld) (addr : Address) (site : CallSite) :
    Option CallFrame :=
  let st := lookup w addr
  if site.kind != .call then none
  else if site.target != addr.toNat then none
  else if site.value != 0 then none
  else
    some
      { caller := addr
        callee := addr
        site := site
        callerBefore := st
        calleeBefore := st
        calleeEntry := withCallContext st addr addr 0 }

/-- Same-address commit: success keeps the body post-state; revert restores
    the pre-call snapshot. Both outcomes journal and install returndata. -/
def executeSelfCall (w : MultiWorld) (frame : CallFrame)
    (runCallee : CallFrame → CalleeExecution) : FramedCallObservation :=
  let execution := runCallee frame
  let entry := framedJournalEntry frame execution.result
  let base : ContractState :=
    match execution.result with
    | .success _ => execution.post
    | .failure _ | .revert _ => frame.callerBefore
  let journaled : ContractState :=
    { base with
      returndata := execution.result.returndata.map
        Compiler.CompilationModel.Denote.wordNormalize
      calls := frame.callerBefore.calls ++ [entry] }
  { frame := frame, result := execution.result,
    world := upsert w frame.caller journaled }

/-- Frame construction for a modeled hop, including `this.f()` self-calls. -/
def hopEntry (w : MultiWorld) (caller callee : Address) (site : CallSite) :
    Option CallFrame :=
  if caller = callee then selfCallEntry w caller site
  else callEntry w caller callee site

/-- Execute a modeled hop. Self-calls use `executeSelfCall`; distinct
    addresses reuse `executeCall`. -/
def executeHop (w : MultiWorld) (frame : CallFrame)
    (runCallee : CallFrame → CalleeExecution) : FramedCallObservation :=
  if frame.caller = frame.callee then executeSelfCall w frame runCallee
  else executeCall w frame runCallee

/-- View hop: run the callee body, then discard its storage writes.
    Journal and returndata still record the attempt. -/
def executeViewHop (w : MultiWorld) (frame : CallFrame)
    (runCallee : CallFrame → CalleeExecution) : FramedCallObservation :=
  let execution := runCallee frame
  let entry := framedJournalEntry frame execution.result
  if frame.caller = frame.callee then
    let journaled : ContractState :=
      { frame.callerBefore with
        returndata := execution.result.returndata.map
          Compiler.CompilationModel.Denote.wordNormalize
        calls := frame.callerBefore.calls ++ [entry] }
    { frame := frame, result := execution.result,
      world := upsert w frame.caller journaled }
  else
    let callerJournaled : ContractState :=
      { frame.callerBefore with
        returndata := execution.result.returndata.map
          Compiler.CompilationModel.Denote.wordNormalize
        calls := frame.callerBefore.calls ++ [entry] }
    { frame := frame, result := execution.result,
      world := upsert (upsert w frame.caller callerJournaled)
        frame.callee frame.calleeBefore }

/-- Run a `Contract` body as the callee of a CALL-shaped hop. -/
def runContract {α : Type} (body : Contract α) (frame : CallFrame) :
    CalleeExecution :=
  match body frame.calleeEntry with
  | .success _ post => { result := .success [], post }
  | .revert _ _ => { result := .revert [], post := frame.calleeBefore }

def hop (w : MultiWorld) (caller callee : Address) (site : CallSite)
    (runCallee : CallFrame → CalleeExecution) :
    Option FramedCallObservation := do
  let frame ← hopEntry w caller callee site
  some (executeHop w frame runCallee)

def hopView (w : MultiWorld) (caller callee : Address) (site : CallSite)
    (runCallee : CallFrame → CalleeExecution) :
    Option FramedCallObservation := do
  let frame ← hopEntry w caller callee site
  some (executeViewHop w frame runCallee)

def hopContract {α : Type} (w : MultiWorld) (caller callee : Address)
    (body : Contract α) : Option FramedCallObservation :=
  hop w caller callee (modeledSite callee) (runContract body)

def hopContractView {α : Type} (w : MultiWorld) (caller callee : Address)
    (body : Contract α) : Option FramedCallObservation :=
  hopView w caller callee (modeledSite callee) (runContract body)

/-! ## Required Feature 2 theorems

Stated against the explicit `upsert` world from `executeCall_*_world` so they
do not depend on a separate `lookup` theory. Caller context fields are
definitionally those of `callerBefore`. -/

theorem hop_eq_executeCall (w : MultiWorld) (frame : CallFrame)
    (runCallee : CallFrame → CalleeExecution)
    (hneq : frame.caller ≠ frame.callee) :
    executeHop w frame runCallee = executeCall w frame runCallee := by
  simp [executeHop, hneq]

/-- Callee of a hop sees the caller as `msg.sender`. -/
theorem enter_sender (callee : ContractState) (caller this : Address)
    (value : Core.Uint256) :
    (withCallContext callee caller this value).sender = caller :=
  withCallContext_sender callee caller this value

/-- Success commits callee storage; caller `sender`/`this`/`msgValue` stay. -/
theorem external_success (w : MultiWorld) (frame : CallFrame)
    (runCallee : CallFrame → CalleeExecution) (data : List Nat)
    (hneq : frame.caller ≠ frame.callee)
    (h : (runCallee frame).result = .success data) :
    (executeHop w frame runCallee).result = .success data ∧
    (executeHop w frame runCallee).world =
      upsert
        (upsert w frame.caller
          { frame.callerBefore with
            selfBalance := frame.callerBefore.selfBalance -
              (frame.site.value : Core.Uint256)
            returndata := data.map
              Compiler.CompilationModel.Denote.wordNormalize
            calls := frame.callerBefore.calls ++
              [framedJournalEntry frame (.success data)] })
        frame.callee (runCallee frame).post ∧
    frame.callerBefore.sender = frame.callerBefore.sender ∧
    frame.callerBefore.thisAddress = frame.callerBefore.thisAddress ∧
    frame.callerBefore.msgValue = frame.callerBefore.msgValue := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · simp [executeHop, hneq, executeCall_result, h]
  · simpa [executeHop, hneq] using
      executeCall_success_world w frame runCallee data h

/-- Revert restores the pre-call callee snapshot. Caller storage words are
    those of `callerBefore` (only journal/returndata change). -/
theorem external_failure (w : MultiWorld) (frame : CallFrame)
    (runCallee : CallFrame → CalleeExecution) (data : List Nat)
    (hneq : frame.caller ≠ frame.callee)
    (h : (runCallee frame).result = .revert data) :
    (executeHop w frame runCallee).result = .revert data ∧
    (executeHop w frame runCallee).world =
      upsert
        (upsert w frame.caller
          { frame.callerBefore with
            returndata := data.map
              Compiler.CompilationModel.Denote.wordNormalize
            calls := frame.callerBefore.calls ++
              [framedJournalEntry frame (.revert data)] })
        frame.callee frame.calleeBefore ∧
    ({ frame.callerBefore with
        returndata := data.map Compiler.CompilationModel.Denote.wordNormalize
        calls := frame.callerBefore.calls ++
          [framedJournalEntry frame (.revert data)] }).storageWords =
      frame.callerBefore.storageWords := by
  refine ⟨?_, ?_, rfl⟩
  · simp [executeHop, hneq, executeCall_result, h]
  · simpa [executeHop, hneq] using
      executeCall_revert_world w frame runCallee data h

/-- A distinct-address call does not write caller storage words. -/
theorem hop_caller_storage_frame (frame : CallFrame) (data : List Nat) :
    ({ frame.callerBefore with
        selfBalance := frame.callerBefore.selfBalance -
          (frame.site.value : Core.Uint256)
        returndata := data.map Compiler.CompilationModel.Denote.wordNormalize
        calls := frame.callerBefore.calls ++
          [framedJournalEntry frame (.success data)] }).storageWords =
      frame.callerBefore.storageWords :=
  rfl

theorem hopEntry_self (w : MultiWorld) (addr : Address) (site : CallSite)
    (hkind : site.kind = .call) (htarget : site.target = addr.toNat)
    (hvalue : site.value = 0) :
    hopEntry w addr addr site =
      some
        { caller := addr
          callee := addr
          site := site
          callerBefore := lookup w addr
          calleeBefore := lookup w addr
          calleeEntry := withCallContext (lookup w addr) addr addr 0 } := by
  simp [hopEntry, selfCallEntry, hkind, htarget, hvalue]

theorem selfCall_success {α : Type} (body : Contract α) (s : ContractState)
    (v : α) (s' : ContractState)
    (h : body { s with sender := s.thisAddress, msgValue := 0, returndata := [] } =
      ContractResult.success v s') :
    (Contract.selfCall body s).getValue? = some v ∧
      (Contract.selfCall body s).getState.sender = s.sender ∧
      (Contract.selfCall body s).getState.thisAddress = s.thisAddress ∧
      (Contract.selfCall body s).getState.msgValue = s.msgValue := by
  unfold Contract.selfCall
  simp [h, ContractResult.getValue?, ContractResult.getState]

theorem selfCall_failure {α : Type} (body : Contract α) (s : ContractState)
    (msg : String) (s' : ContractState)
    (h : body { s with sender := s.thisAddress, msgValue := 0, returndata := [] } =
      ContractResult.revert msg s') :
    Contract.selfCall body s = ContractResult.revert msg s := by
  unfold Contract.selfCall
  simp [h]

theorem executeViewHop_discards_callee (w : MultiWorld) (frame : CallFrame)
    (runCallee : CallFrame → CalleeExecution)
    (hneq : frame.caller ≠ frame.callee) :
    executeViewHop w frame runCallee =
      let execution := runCallee frame
      let entry := framedJournalEntry frame execution.result
      let callerJournaled : ContractState :=
        { frame.callerBefore with
          returndata := execution.result.returndata.map
            Compiler.CompilationModel.Denote.wordNormalize
          calls := frame.callerBefore.calls ++ [entry] }
      { frame := frame, result := execution.result,
        world := upsert (upsert w frame.caller callerJournaled)
          frame.callee frame.calleeBefore } := by
  simp [executeViewHop, hneq]

end Verity.MultiContract
