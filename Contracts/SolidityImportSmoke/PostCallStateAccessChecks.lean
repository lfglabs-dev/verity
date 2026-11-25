import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.AdversarialEntryPointInvariants
import Compiler.CompilationModel.TrustSurface
import Verity.Core.Model.ByteCallStorageFrames

/-!
Storage reads, storage writes and logs after a closed value-free `CALL`
(`PostCallStateAccess.sol`). The trust flags record the open post-call window
(`reentrancyAdversarial`, NOT `reentrancyTrusted`, plus `solidity_post_call_state_access`),
and Denote runs each post-call statement against the world the callee committed: an inert
callee, a failing callee, an account without code, and a callee that calls back into the
contract once. The callback's writes are visible to the outer frame's post-call reads, so a
re-entrant double spend is modelled exactly as on the EVM, and a re-entrant spend of the same
credit makes the outer checked subtraction panic. Source EVM and compiled-model parity runs in
`check_post_call_state_access.py` (recording responders) and `check_reentrant_callback.py`
(re-entrant callbacks through `ReentrantCallbackHook` / `ReentrantCallResponderMocks`).
-/
namespace SolidityImportSmoke.PostCallStateAccessChecks
open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport
open Compiler.CompilationModel.ByteExternalCall

solidity_import postCallWriteIr from "Contracts/SolidityImportSmoke" entry "PostCallStateAccess.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticPostCallWrite
  function pingThenCount(address,uint256)
  function pingThenRead(address)
  function twoPingsThenCount(address,address,uint256)
  function pingThenRequire(address,uint256)
  function pingLoop(address,uint256)
  function pingThenBalance(address)
  function pingThenView(address,address)
  function read()

solidity_import postCallWriteLegacy from "Contracts/SolidityImportSmoke"
  entry "PostCallStateAccess.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticPostCallWrite
  function pingThenCount(address,uint256)
  function pingThenRead(address)
  function read()

solidity_import callbackTransferIr from "Contracts/SolidityImportSmoke"
  entry "PostCallStateAccess.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticCallbackTransfer
  function deposit(address,uint256)
  function transferOut(address,address,uint256)
  function read(address)

solidity_import postCallEventIr from "Contracts/SolidityImportSmoke" entry "PostCallStateAccess.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticPostCallEvent
  function notify(address,uint256)
  function tryNotify(address,uint256)
  function tryNotifyRead(address,uint256)
  function read()

private def postCallWrite : CompilationModel := postCallWriteIr.model
private def legacyWrite : CompilationModel := postCallWriteLegacy.model
private def callbackTransfer : CompilationModel := callbackTransferIr.model
private def postCallEvent : CompilationModel := postCallEventIr.model

private def flags (model : CompilationModel) (name : String) :
    Option (Bool × Bool × Bool × List String) :=
  (model.functions.find? (·.name == name)).map fun f =>
    (f.allowPostInteractionWrites, f.reentrancyTrusted, f.reentrancyAdversarial,
      f.localObligations.map (·.name))

private def postCall (abi : String) : Option (Bool × Bool × Bool × List String) :=
  some (true, false, true, [abi, "solidity_post_call_state_access"])

-- A write after the call: the CEI opt-out, the adversarial reentrancy disposition (never
-- `reentrancyTrusted`), and its obligation.
#guard flags postCallWrite "pingThenCount" == postCall "solidity_scalar_abi_entry"
#guard flags legacyWrite "pingThenCount" == postCall "solidity_scalar_abi_entry"
#guard flags postCallWrite "twoPingsThenCount" == postCall "solidity_scalar_abi_entry"
#guard flags postCallWrite "pingThenRequire" == postCall "solidity_scalar_abi_entry"
#guard flags postCallWrite "pingLoop" == postCall "solidity_scalar_abi_entry"
#guard flags callbackTransfer "transferOut" == postCall "solidity_scalar_abi_entry"
#guard flags postCallEvent "notify" == postCall "solidity_scalar_abi_entry"
#guard flags postCallEvent "tryNotify" == postCall "solidity_scalar_abi_entry"
-- A read after the call. The CEI opt-out comes from the call following the closed code-size
-- check, as for every typed void call (`InterfaceVoidCallTrustChecks`).
#guard flags postCallWrite "pingThenRead" == some (true, false, true,
  ["solidity_scalar_abi_entry", "solidity_closed_transport_cei", "solidity_post_call_state_access"])
#guard flags postCallWrite "pingThenBalance" == some (true, false, true,
  ["solidity_scalar_abi_entry", "solidity_closed_transport_cei", "solidity_post_call_state_access"])
#guard flags postCallWrite "pingThenView" == some (true, false, true,
  ["solidity_scalar_abi_entry", "solidity_closed_transport_cei", "solidity_post_call_state_access"])
#guard flags postCallEvent "tryNotifyRead" == some (true, false, true,
  ["solidity_scalar_abi_entry", "solidity_closed_transport_cei", "solidity_post_call_state_access"])
-- Trust report labels open post-call windows `reentrancy_adversarial`, never `reentrancy_trusted`.
#guard (collectStaticOptOuts postCallWrite).any (·.optOut == "reentrancy_adversarial")
#guard (collectStaticOptOuts postCallWrite).all (·.optOut != "reentrancy_trusted")
-- No call: no flag.
#guard flags postCallWrite "read" == some (false, false, false, [])
#guard flags callbackTransfer "deposit" == some (false, false, false, ["solidity_scalar_abi_entry"])

private def self : Nat := 0xc0ffee
private def user : Nat := 0x1111
private def callee : Nat := 0x7a11
private def noCode : Nat := 0x99
private def gas : Nat := 30000000

private def world0 : Verity.ContractState :=
  { Verity.defaultState with
    accountWorld := Verity.Core.AccountWorld.write Verity.Core.AccountWorld.empty
      (Verity.Core.Address.ofNat callee) { code := [0] } }

private def frame (model : CompilationModel) (name : String) (args : List Nat)
    (world : Verity.ContractState) (sender : Nat) (byteCalls : Denote.ByteCallEnvironment) :
    Except String Transactions.FrameResult := do
  let some fn := model.functions.find? (·.name == name) | throw s!"missing function {name}"
  let tx : Denote.DenoteTransaction :=
    { sender, txOrigin := sender, thisAddress := self, functionSelector := 0, args }
  let initial := Transactions.beginTransaction (Denote.withTransactionContext world tx)
  let some bindings := Denote.bindExternalParams 0 fn.bindingParams args | throw "abi"
  Transactions.executeBody Differential.oracle (Denote.effectiveFields model) initial bindings
    fn.body model.errors byteCalls

/-- A callee that answers only `CALL` with `answer`; any other request succeeds inertly. -/
private def callOnly
    (answer : Request → Verity.ContractState → Response Verity.ContractState Verity.StorageKey) :
    Adversary Verity.ContractState Verity.StorageKey where
  respond request world :=
    if request.kind = .call then answer request world else .success world [] []
  valid request world := by
    by_cases h : request.kind = .call
    · simp only [h, if_true]
      cases answer request world <;> simp [Response.valid, h]
    · simp [h, Response.valid]

private def env (adversary : Adversary Verity.ContractState Verity.StorageKey) :
    Denote.ByteCallEnvironment :=
  { adversary := some adversary, gas := some gas }

private def inert : Denote.ByteCallEnvironment := env Denote.inertCallee

private def failing : Denote.ByteCallEnvironment :=
  env (callOnly fun _ _ => .revert [0xde, 0xad] [])

/-- The callee calls back into `name` of `model` once, as account `request.target`, in a
reentrant frame (transient storage kept); calls made by the callback answer inertly. The
callback's persistent effects are committed into the caller's world. -/
private def reenter (model : CompilationModel) (name : String) (args : List Nat) :
    Denote.ByteCallEnvironment :=
  env <| callOnly fun request world =>
    let nested := { Transactions.beginReentrantFrame world with
      events := world.events, sender := Verity.Core.Address.ofNat request.target }
    let callback : Except String Transactions.FrameResult := do
      let some fn := model.functions.find? (fun f : FunctionSpec => f.name == name)
        | throw "missing callback"
      let some bindings := Denote.bindExternalParams 0 fn.bindingParams args | throw "abi"
      Transactions.finishFrame nested (Denote.execStmtList Differential.oracle
        (Denote.effectiveFields model)
        { world := nested, bindings, errors := model.errors,
          byteCallAdversary := some Denote.inertCallee, byteCallGas := some gas } fn.body)
    match callback with
    | .ok result =>
        if result.success then
          .success (DenoteByteExternalCalls.commitCalleeWorld world result.world) [] []
        else .revert result.data []
    | .error _ => .exceptional []

private def summary : Except String Transactions.FrameResult →
    Option (Bool × List UInt8 × List Nat × List (List Nat))
  | .ok r => some (r.success, r.data, [r.world.readSlot 0 |>.val, r.world.readSlot 1 |>.val],
      r.world.events.map Denote.encodeEvent)
  | .error _ => none

/-- `Panic(0x11)`: checked arithmetic overflow or underflow. -/
private def panicOverflow : List UInt8 := [0x4e, 0x48, 0x7b, 0x71] ++ Denote.wordBytes 0x11

private def ok (words : List Nat) (slots : List Nat) (events : List (List Nat) := []) :
    Option (Bool × List UInt8 × List Nat × List (List Nat)) :=
  some (true, words.flatMap Denote.wordBytes, slots, events)

private def reverted (data : List UInt8) :
    Option (Bool × List UInt8 × List Nat × List (List Nat)) :=
  some (false, data, [0, 0], [])

private def callbackAgain : Denote.ByteCallEnvironment :=
  reenter postCallWrite "pingThenCount" [callee, 7]

-- Post-call reads and writes run against the committed world: an inert callee leaves the
-- pre-call words; a callback's `pingThenCount(callee, 7)` is visible to the outer frame's
-- reads (counter 1 + 1, total 7 + 5), not overwritten by values read before the call.
#guard summary (frame postCallWrite "pingThenCount" [callee, 5] world0 user inert) == ok [] [1, 5]
#guard summary (frame postCallWrite "pingThenCount" [callee, 5] world0 user callbackAgain) ==
  ok [] [2, 12]
#guard summary (frame legacyWrite "pingThenCount" [callee, 5] world0 user
  (reenter legacyWrite "pingThenCount" [callee, 7])) == ok [] [2, 12]
#guard summary (frame postCallWrite "pingThenRead" [callee] world0 user callbackAgain) ==
  ok [1] [1, 7]
-- A failed call forwards its return data and rolls back; no code reverts with no data.
#guard summary (frame postCallWrite "pingThenCount" [callee, 5] world0 user failing) ==
  reverted [0xde, 0xad]
#guard summary (frame postCallWrite "pingThenCount" [noCode, 5] world0 user inert) == reverted []

private def deposited (amount : Nat) : Verity.ContractState :=
  match frame callbackTransfer "deposit" [user, amount] world0 user inert with
  | .ok r => r.world
  | .error _ => world0

/-- `read(user)` after `transferOut`: the remaining credit and the transfer count. -/
private def creditAfter (deposit : Nat) (byteCalls : Denote.ByteCallEnvironment) :
    Option (List UInt8) :=
  match frame callbackTransfer "transferOut" [callee, user, 10] (deposited deposit) user
      byteCalls with
  | .ok r => if r.success then
      match frame callbackTransfer "read" [user] r.world user inert with
      | .ok read => some read.data
      | .error _ => none
    else none
  | .error _ => none

private def spendAgain : Denote.ByteCallEnvironment :=
  reenter callbackTransfer "transferOut" [callee, user, 10]

#guard summary (frame callbackTransfer "transferOut" [callee, user, 10] (deposited 10) user
  inert) == ok [] [0, 1]
#guard creditAfter 10 inert == some ([0, 1].flatMap Denote.wordBytes)
-- Re-entrant spend of the same credit: the callback passes the pre-call check, so the outer
-- post-call checked subtraction underflows and the whole transaction rolls back.
#guard summary (frame callbackTransfer "transferOut" [callee, user, 10] (deposited 10) user
  spendAgain) == reverted panicOverflow
-- With credit for both, the re-entrant double spend succeeds, exactly as on the EVM.
#guard summary (frame callbackTransfer "transferOut" [callee, user, 10] (deposited 20) user
  spendAgain) == ok [] [0, 2]
#guard creditAfter 20 spendAgain == some ([0, 2].flatMap Denote.wordBytes)

-- A log after the call carries the post-call count; a callback's log precedes the caller's.
#guard summary (frame postCallEvent "notify" [callee, 3] world0 user inert) ==
  ok [] [1, 0] [[callee, 3, 1]]
#guard summary (frame postCallEvent "notify" [callee, 3] world0 user
  (reenter postCallEvent "notify" [callee, 4])) == ok [] [2, 0] [[callee, 4, 1], [callee, 3, 2]]
-- `try` clauses write storage; an account without code reverts uncaught with no data.
#guard summary (frame postCallEvent "tryNotify" [callee, 3] world0 user inert) == ok [1] [1, 0]
#guard summary (frame postCallEvent "tryNotify" [callee, 3] world0 user failing) == ok [0] [0, 1]
#guard summary (frame postCallEvent "tryNotify" [noCode, 3] world0 user inert) == reverted []

/-- The re-entrant callee does not keep the caller's storage, so imported models must not
(and do not) assume `Denote.CallKeepsCallerStorage`; the inert callee does
(`Denote.callKeepsCallerStorage_inertCallee`), framing both `storageWords` and `storageArray`. -/
example : Denote.CallKeepsCallerStorage Denote.inertCallee :=
  Denote.callKeepsCallerStorage_inertCallee

example {request : Request} {before : Verity.ContractState}
    {observed : Observation Verity.ContractState Verity.StorageKey}
    (h : executeChecked Denote.inertCallee request before = .ok observed) :
    observed.world.storageArray = before.storageArray :=
  Denote.executeChecked_storageArray_of_callKeepsCallerStorage
    Denote.callKeepsCallerStorage_inertCallee h

/-! Admission classifier on hand-built bodies. Only the exact closed `CALL` transport (and
the other closed transports) is erased: an internal call, a non-closed external call or a
call module that differs from the closed one after the `CALL` keeps the body out. -/

private def closedCall : Stmt :=
  .ecm (Compiler.ECM.SolidityLowLevelCall.optionalBoolModule "ok" 0xa9059cbb 2)
    [.param "token", .param "to", .param "amount"]

private def openCall : Stmt :=
  .ecm { Compiler.ECM.SolidityLowLevelCall.optionalBoolModule "ok" 0xa9059cbb 2 with
    byteTransport := none } [.param "token", .param "to", .param "amount"]

private def write : Stmt := .setStorage "counter" (.add (.storage "counter") (.literal 1))

#guard onlyClosedCallStateWindows [closedCall, write]
#guard onlyClosedCallStateWindows [write, closedCall, write, .emit "Notified" [.literal 1]]
#guard onlyClosedCallStateWindows [.forEach "i" (.literal 2) [closedCall, write]]
#guard onlyClosedCallStateWindows [.ite (.param "flag") [closedCall] [], write]
#guard !onlyClosedCallStateWindows [write]
#guard !onlyClosedCallStateWindows [closedCall, .internalCall "helper" [], write]
#guard !onlyClosedCallStateWindows [closedCall, .externalCallBind ["r"] "f" [], write]
#guard !onlyClosedCallStateWindows [closedCall, openCall, write]
#guard !onlyClosedCallStateWindows [openCall, write]
-- The unerased bodies violate CEI: the importer records the opt-out it relies on.
#guard (Compiler.CompilationModel.stmtListCEIViolation [closedCall, write] false).isSome
#guard !onlyTrailingCallReentrancyWindows [closedCall, write]
#guard onlyTrailingCallReentrancyWindows [write, closedCall]

end SolidityImportSmoke.PostCallStateAccessChecks
