import Verity.Core.Model.DenoteExternalCalls

/-!
# Multi-contract world with ETH-valued calls

A finite map `Address → ContractState`. A hop debits the caller,
credits the callee (so `selfBalance` is the post-call balance),
installs the call context (`sender` / `thisAddress` / `msgValue`),
applies an explicit callee step, and journals `target` and `value`
on the caller.

The P-ETH-1 ensemble is `Bus → Gateway → Vault → (Lido | request)`.
This is a model-plane composition, not a claim that those contracts
are compiled or L2-proved. No keccak injectivity, no new axiom.
-/

namespace Verity.MultiContract

open Compiler.CompilationModel.DenoteExternalCalls

/-- One named account in the ensemble. -/
structure Account where
  address : Address
  state : ContractState
  deriving Repr

/-- Finite multi-contract world. Missing addresses read as `defaultState`. -/
structure MultiWorld where
  accounts : List Account
  deriving Repr

def lookup (w : MultiWorld) (addr : Address) : ContractState :=
  match w.accounts.find? (fun a => a.address == addr) with
  | some a => a.state
  | none => defaultState

def upsert (w : MultiWorld) (addr : Address) (s : ContractState) : MultiWorld :=
  if w.accounts.any (fun a => a.address == addr) then
    { accounts := w.accounts.map (fun a =>
        if a.address == addr then { a with state := s } else a) }
  else
    { accounts := w.accounts ++ [{ address := addr, state := s }] }

/-- Call-frame context installed on the callee: sender, this, msg.value,
    and `selfBalance` after receiving `value`. -/
def withCallContext (callee : ContractState) (caller this : Address)
    (value : Core.Uint256) : ContractState :=
  { callee with
    sender := caller
    thisAddress := this
    msgValue := value
    selfBalance := callee.selfBalance + value }

def totalSelfBalance (w : MultiWorld) : Nat :=
  w.accounts.foldl (fun acc a => acc + a.state.selfBalance.val) 0

/-- One ETH-valued hop. Fails when the caller cannot pay. The callee
    step sees the credited, re-contextualized world. -/
def callValue (w : MultiWorld) (caller callee : Address) (value : Core.Uint256)
    (name : String := "") (calldata : List Nat := [])
    (calleeStep : ContractState → ContractState := id) : Option MultiWorld :=
  let fromS := lookup w caller
  let toS := lookup w callee
  if value ≤ fromS.selfBalance then
    let fromPaid : ContractState :=
      { fromS with selfBalance := fromS.selfBalance - value }
    let toAfter := calleeStep (withCallContext toS caller callee value)
    let fromJournaled : ContractState :=
      { fromPaid with
        calls := fromPaid.calls ++
          [{ siteId := callee.toNat
             kind := .call
             target := callee.toNat
             value := value.val
             calldata := calldata
             control := .success
             returndata := []
             name := name }] }
    some (upsert (upsert w caller fromJournaled) callee toAfter)
  else
    none

/-! ## Execution-backed call frames

`callValue` above is the compatibility success-only helper.  The semantics
below is the generic boundary: the callee runs in an explicit frame and its
actual control result determines commit or rollback. -/

/-- Immutable caller/callee snapshot and the context installed for execution. -/
structure CallFrame where
  caller : Address
  callee : Address
  site : CallSite
  callerBefore : ContractState
  calleeBefore : ContractState
  calleeEntry : ContractState

/-- Result produced by executing the callee body in `calleeEntry`. -/
structure CalleeExecution where
  result : ExternalCallResult
  post : ContractState

/-- Observable result of one framed call.  Keeping the frame in the result
prevents a continuation from silently replacing the caller/callee snapshot. -/
structure FramedCallObservation where
  frame : CallFrame
  result : ExternalCallResult
  world : MultiWorld

def callEntry (w : MultiWorld) (caller callee : Address) (site : CallSite) :
    Option CallFrame :=
  let callerBefore := lookup w caller
  let calleeBefore := lookup w callee
  if caller = callee then none
  else if site.kind != .call then none
  else if site.target != callee.toNat then none
  else if site.value ≤ callerBefore.selfBalance.val then
    some
      { caller := caller
        callee := callee
        site := site
        callerBefore := callerBefore
        calleeBefore := calleeBefore
        calleeEntry :=
          withCallContext calleeBefore caller callee (site.value : Core.Uint256) }
  else
    none

def framedJournalEntry (frame : CallFrame) (result : ExternalCallResult) :
    ExternalCall :=
  journalEntry frame.site result

/-- Execute one source-shaped external call.  Success commits the debit and
callee post-state.  Failure/revert restore both account snapshots.  Every
outcome appends the control and returndata produced by the execution itself
to the caller journal. -/
def executeCall (w : MultiWorld) (frame : CallFrame)
    (runCallee : CallFrame → CalleeExecution) : FramedCallObservation :=
  let execution := runCallee frame
  let entry := framedJournalEntry frame execution.result
  let callerJournaled : ContractState :=
    { frame.callerBefore with calls := frame.callerBefore.calls ++ [entry] }
  let nextWorld :=
    match execution.result with
    | .success _ =>
        let callerCommitted : ContractState :=
          { callerJournaled with
            selfBalance :=
              frame.callerBefore.selfBalance - (frame.site.value : Core.Uint256) }
        upsert (upsert w frame.caller callerCommitted) frame.callee execution.post
    | .failure _ | .revert _ =>
        upsert (upsert w frame.caller callerJournaled)
          frame.callee frame.calleeBefore
  { frame := frame, result := execution.result, world := nextWorld }

/-- Construct and execute a frame in one checked operation. -/
def call (w : MultiWorld) (caller callee : Address) (site : CallSite)
    (runCallee : CallFrame → CalleeExecution) : Option FramedCallObservation := do
  let frame ← callEntry w caller callee site
  some (executeCall w frame runCallee)

/-! ## First-class self-delegatecall sequence

Ordinary `callEntry` rejects `caller = callee` and `kind ≠ .call` (the
#2362 ordinary-call frame). Self-delegate multicall is a different
path: same address, `delegatecall`, no ETH transfer. Success commits
the body post-state on that one account; failure/revert restores the
sequence-entry world and bubbles returndata. This is not the ECM
`selfDelegateMulticallBytes` assumption and not #2365's compiled
`FunctionSpec` transaction. -/

def selfDelegateEntry (w : MultiWorld) (addr : Address) (site : CallSite) :
    Option CallFrame :=
  let st := lookup w addr
  if site.kind != .delegatecall then none
  else if site.target != addr.toNat then none
  else if site.value != 0 then none
  else
    some
      { caller := addr
        callee := addr
        site := site
        callerBefore := st
        calleeBefore := st
        -- DELEGATECALL runs the callee code in the caller's frame: `msg.sender`
        -- and `msg.value` are inherited from the executing frame, not reset.
        -- `site.value = 0` above only records that DELEGATECALL carries no
        -- value argument; it does not zero the inherited `msg.value`.
        calleeEntry := { st with thisAddress := addr } }

/-- Same-account commit: success replaces `addr` with `post` (plus journal);
    failure/revert restore the pre-call snapshot and still journal. -/
def executeSelfDelegate (w : MultiWorld) (addr : Address) (frame : CallFrame)
    (runBody : CallFrame → CalleeExecution) : FramedCallObservation :=
  let execution := runBody frame
  let entry := framedJournalEntry frame execution.result
  let journaled : ContractState :=
    { (match execution.result with
        | .success _ => execution.post
        | .failure _ | .revert _ => frame.callerBefore) with
      calls := frame.callerBefore.calls ++ [entry] }
  { frame := frame, result := execution.result, world := upsert w addr journaled }

def selfDelegate (w : MultiWorld) (addr : Address) (site : CallSite)
    (runBody : CallFrame → CalleeExecution) : Option FramedCallObservation := do
  let frame ← selfDelegateEntry w addr site
  some (executeSelfDelegate w addr frame runBody)

inductive SelfDelegateControl where
  | success
  | invalidCall (index : Nat)
  | callFailed (index : Nat) (result : ExternalCallResult)
  deriving Repr, DecidableEq

structure SelfDelegateExecution where
  control : SelfDelegateControl
  world : MultiWorld
  calls : List FramedCallObservation

/-- Run a list of self-delegate sites against one address. Successful
    steps thread `observation.world`. Invalid frame, failure, or revert
    restores `before` and records the failed result (returndata bubble). -/
def denoteSelfDelegateCallsFrom (before current : MultiWorld) (addr : Address)
    (runBody : CallFrame → CalleeExecution) :
    Nat → List CallSite → List FramedCallObservation → SelfDelegateExecution
  | _, [], observations =>
      { control := .success, world := current, calls := observations.reverse }
  | index, site :: rest, observations =>
      match selfDelegate current addr site runBody with
      | none =>
          { control := .invalidCall index, world := before,
            calls := observations.reverse }
      | some observation =>
          if observation.result.succeeded then
            denoteSelfDelegateCallsFrom before observation.world addr runBody
              (index + 1) rest (observation :: observations)
          else
            { control := .callFailed index observation.result, world := before,
              calls := (observation :: observations).reverse }

def denoteSelfDelegateCalls (before : MultiWorld) (addr : Address)
    (program : List CallSite) (runBody : CallFrame → CalleeExecution) :
    SelfDelegateExecution :=
  denoteSelfDelegateCallsFrom before before addr runBody 0 program []

theorem denoteSelfDelegateCalls_nil (before : MultiWorld) (addr : Address)
    (runBody : CallFrame → CalleeExecution) :
    (denoteSelfDelegateCalls before addr [] runBody).world = before :=
  rfl

theorem selfDelegateEntry_rejects_ordinary_call
    (w : MultiWorld) (addr : Address) (site : CallSite)
    (h : site.kind = .call) :
    selfDelegateEntry w addr site = none := by
  simp [selfDelegateEntry, h]

theorem denoteSelfDelegateCalls_invalid_first_rolls_back
    (before : MultiWorld) (addr : Address) (site : CallSite)
    (runBody : CallFrame → CalleeExecution)
    (h : selfDelegate before addr site runBody = none) :
    (denoteSelfDelegateCalls before addr [site] runBody).world = before := by
  simp [denoteSelfDelegateCalls, denoteSelfDelegateCallsFrom, h]

theorem denoteSelfDelegateCalls_failed_first_rolls_back
    (before : MultiWorld) (addr : Address) (site : CallSite)
    (runBody : CallFrame → CalleeExecution)
    (obs : FramedCallObservation)
    (h : selfDelegate before addr site runBody = some obs)
    (hfail : obs.result.succeeded = false) :
    (denoteSelfDelegateCalls before addr [site] runBody).world = before := by
  simp [denoteSelfDelegateCalls, denoteSelfDelegateCallsFrom, h, hfail]

theorem denoteSelfDelegateCalls_failed_bubbles_result
    (before : MultiWorld) (addr : Address) (site : CallSite)
    (runBody : CallFrame → CalleeExecution)
    (obs : FramedCallObservation)
    (h : selfDelegate before addr site runBody = some obs)
    (hfail : obs.result.succeeded = false) :
    (denoteSelfDelegateCalls before addr [site] runBody).control =
      .callFailed 0 obs.result := by
  simp [denoteSelfDelegateCalls, denoteSelfDelegateCallsFrom, h, hfail]

/-! ## P-ETH-1 ensemble: Bus → Gateway → Vault → (Lido | request) -/

def busAddr : Address := (1 : Address)
def gatewayAddr : Address := (2 : Address)
def vaultAddr : Address := (3 : Address)
def lidoAddr : Address := (4 : Address)
def requestAddr : Address := (5 : Address)

inductive VaultRoute where
  | lido
  | request
  deriving DecidableEq, Repr

def accountAt (addr : Address) (bal : Nat) : Account :=
  { address := addr
    state := { defaultState with thisAddress := addr, selfBalance := bal } }

def fundedBus (busWei : Nat) : MultiWorld :=
  { accounts :=
      [accountAt busAddr busWei,
       accountAt gatewayAddr 0,
       accountAt vaultAddr 0,
       accountAt lidoAddr 0,
       accountAt requestAddr 0] }

/-- Forward `value` along Bus → Gateway → Vault → route. -/
def routeEth (w : MultiWorld) (value : Core.Uint256) (route : VaultRoute) :
    Option MultiWorld :=
  match callValue w busAddr gatewayAddr value (name := "busToGateway") with
  | none => none
  | some w1 =>
      match callValue w1 gatewayAddr vaultAddr value (name := "gatewayToVault") with
      | none => none
      | some w2 =>
          match route with
          | .lido =>
              callValue w2 vaultAddr lidoAddr value (name := "vaultToLido")
          | .request =>
              callValue w2 vaultAddr requestAddr value (name := "vaultToRequest")

/-! ## Laws -/

theorem withCallContext_selfBalance (callee : ContractState)
    (caller this : Address) (value : Core.Uint256) :
    (withCallContext callee caller this value).selfBalance =
      callee.selfBalance + value :=
  rfl

theorem withCallContext_msgValue (callee : ContractState)
    (caller this : Address) (value : Core.Uint256) :
    (withCallContext callee caller this value).msgValue = value :=
  rfl

theorem withCallContext_this (callee : ContractState)
    (caller this : Address) (value : Core.Uint256) :
    (withCallContext callee caller this value).thisAddress = this :=
  rfl

theorem withCallContext_sender (callee : ContractState)
    (caller this : Address) (value : Core.Uint256) :
    (withCallContext callee caller this value).sender = caller :=
  rfl

theorem callValue_none_of_cannot_pay (w : MultiWorld)
    (caller callee : Address) (value : Core.Uint256)
    (h : (lookup w caller).selfBalance < value) :
    callValue w caller callee value = none := by
  simpa [callValue] using h

@[simp] theorem executeCall_frame (w : MultiWorld) (frame : CallFrame)
    (runCallee : CallFrame → CalleeExecution) :
    (executeCall w frame runCallee).frame = frame :=
  rfl

@[simp] theorem executeCall_result (w : MultiWorld) (frame : CallFrame)
    (runCallee : CallFrame → CalleeExecution) :
    (executeCall w frame runCallee).result = (runCallee frame).result :=
  rfl

/-- Checked rollback is definitionally driven by execution control, not by a
separately injected post-state or observation. -/
theorem executeCall_revert_world (w : MultiWorld) (frame : CallFrame)
    (runCallee : CallFrame → CalleeExecution) (data : List Nat)
    (h : (runCallee frame).result = .revert data) :
    (executeCall w frame runCallee).world =
      upsert
        (upsert w frame.caller
          { frame.callerBefore with
            calls := frame.callerBefore.calls ++
              [framedJournalEntry frame (.revert data)] })
        frame.callee frame.calleeBefore := by
  simp [executeCall, h]

theorem executeCall_failure_world (w : MultiWorld) (frame : CallFrame)
    (runCallee : CallFrame → CalleeExecution) (data : List Nat)
    (h : (runCallee frame).result = .failure data) :
    (executeCall w frame runCallee).world =
      upsert
        (upsert w frame.caller
          { frame.callerBefore with
            calls := frame.callerBefore.calls ++
              [framedJournalEntry frame (.failure data)] })
        frame.callee frame.calleeBefore := by
  simp [executeCall, h]

theorem executeCall_success_world (w : MultiWorld) (frame : CallFrame)
    (runCallee : CallFrame → CalleeExecution) (data : List Nat)
    (h : (runCallee frame).result = .success data) :
    (executeCall w frame runCallee).world =
      upsert
        (upsert w frame.caller
          { frame.callerBefore with
            selfBalance := frame.callerBefore.selfBalance -
              (frame.site.value : Core.Uint256)
            calls := frame.callerBefore.calls ++
              [framedJournalEntry frame (.success data)] })
        frame.callee (runCallee frame).post := by
  simp [executeCall, h]

theorem callEntry_calleeEntry (w : MultiWorld) (caller callee : Address)
    (site : CallSite) (frame : CallFrame)
    (h : callEntry w caller callee site = some frame) :
    frame.calleeEntry =
      withCallContext frame.calleeBefore frame.caller frame.callee
        (frame.site.value : Core.Uint256) := by
  simp only [callEntry] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  next _ => cases h; rfl

theorem fundedBus_bus_balance (n : Nat) :
    (lookup (fundedBus n) busAddr).selfBalance =
      (n : Core.Uint256) := by
  unfold lookup fundedBus accountAt
  simp [busAddr]

end Verity.MultiContract
