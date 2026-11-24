import Compiler.SolidityImport.CallResponderMocks
import Compiler.SolidityImport.AdversarialEntryPointInvariants
import Compiler.CompilationModel.AbiHelpers
import Compiler.Keccak.Sponge

/-! Explicit configurable re-entrant call responder for differential validation of contracts
whose callee calls them back. It mirrors `ReentrantCallbackHook` in
`Contracts/SolidityImportSmoke/ReentrantCallbackHook.sol`: slot 0 holds the callback selector,
slot 1 the argument count (0 or 1), slot 2 the argument word, slot 3 the flags, and slot 4
counts answered calls. A value-free `CALL` to a configured account increments the counter, then
calls the caller back with the payload (the four selector bytes, then the argument word if
there is one), as the EVM's `CALL` frame: `msg.sender` is the account, the calldata and
selector are the payload's, no value; memories, return data and journals start empty and
transient storage is the transaction's (`beginReentrantFrame`). The payload selector picks the
model's own public entry point, which runs through the production frame runner
`executeReentrantBody`. A successful callback is committed with the caller's frame restored
(`commitCallback`): the callback's logs and call journal follow the caller's, as the EVM appends
a successful frame's logs to the transaction's; with flag bit 0 the account then reverts with no
data. A failed callback
is bubbled with its exact revert bytes. A selector that names no entry point, or arguments that
do not decode, revert with no data, as solc's dispatcher and decoder do. An execution error
(an unsupported construct, or a nested external call, which the callback frame is not given)
is an instrumentation failure: such a request is outside `accepts`, so the model run fails
instead of producing a Solidity outcome that a `try` could catch. Answers, writes and accesses are computed from the current world and
request, never copied from an EVM trace.

This is a test-only instrument. It admits nothing in the importer, adds no trust assumption, and
establishes nothing about a deployed callee: its agreement with the Solidity hook is
differential evidence (`check_reentrant_callback.py`). The responder reports only its own
account's accesses; the callback's accesses to the caller's storage are observed through the
source and compiled routes, whose traces include them.
-/
namespace Compiler.CompilationModel.SolidityImport.ReentrantCallResponderMocks

open Denote DenoteByteExternalCalls ByteExternalCall StaticOracleMocks CallResponderMocks
open Transactions

/-- The responder's storage word at `slot`. -/
def slotValue (world : Verity.ContractState) (account slot : Nat) : Nat :=
  (world.storageWords (.contractSlot account slot)).val

/-- The callback calldata: the four selector bytes, then the argument word if there is one. -/
def payload (world : Verity.ContractState) (account : Nat) : Bytes :=
  let selector := (List.range 4).map fun index =>
    UInt8.ofNat (slotValue world account 0 / 2 ^ (8 * (3 - index)) % 256)
  if slotValue world account 1 == 0 then selector
  else selector ++ (List.range 32).map fun index =>
    UInt8.ofNat (slotValue world account 2 / 2 ^ (8 * (31 - index)) % 256)

/-- The calldata words after the selector, zero padded, as the frame's `calldata`. -/
def payloadWords (calldata : Bytes) : List Nat :=
  (List.range ((calldata.length - 4 + 31) / 32)).map fun index => calldataWord calldata (4 + 32 * index)

/-- The selector of `calldata`: its first four bytes. -/
def payloadSelector (calldata : Bytes) : Nat := calldataWord calldata 0 / 2 ^ 224

/-- The world of `callee`'s `CALL` back into the contract with `calldata`: `msg.sender` is the
callee, the calldata, selector and size are the payload's, no value. Everything persistent,
transient storage and `tx.origin` included, is the caller's; memories, return data and
journals start empty. -/
def callbackWorld (world : Verity.ContractState) (callee : Nat) (calldata : Bytes) :
    Verity.ContractState :=
  { beginReentrantFrame world with
    sender := Verity.wordToAddress callee
    msgValue := 0
    calldataSize := Verity.Core.Uint256.ofNat calldata.length
    calldata := payloadWords calldata
    selector := payloadSelector calldata }

section CallbackWorld

variable (world : Verity.ContractState) (callee : Nat) (calldata : Bytes)

@[simp] theorem callbackWorld_sender :
    (callbackWorld world callee calldata).sender = Verity.wordToAddress callee := rfl

@[simp] theorem callbackWorld_selector :
    (callbackWorld world callee calldata).selector = payloadSelector calldata := rfl

@[simp] theorem callbackWorld_calldata :
    (callbackWorld world callee calldata).calldata = payloadWords calldata := rfl

@[simp] theorem callbackWorld_msgValue : (callbackWorld world callee calldata).msgValue = 0 := rfl

@[simp] theorem callbackWorld_storageWords :
    (callbackWorld world callee calldata).storageWords = world.storageWords := rfl

@[simp] theorem callbackWorld_storageArray :
    (callbackWorld world callee calldata).storageArray = world.storageArray := rfl

@[simp] theorem callbackWorld_transientStorage :
    (callbackWorld world callee calldata).transientStorage = world.transientStorage := rfl

@[simp] theorem callbackWorld_txOrigin :
    (callbackWorld world callee calldata).txOrigin = world.txOrigin := rfl

@[simp] theorem callbackWorld_thisAddress :
    (callbackWorld world callee calldata).thisAddress = world.thisAddress := rfl

end CallbackWorld

/-- Revert bytes of an instrumentation failure. Unreachable for accepted requests, which
exclude callbacks that do not execute (`environment`); kept so `respond` is total. -/
def instrumentationBytes : Bytes := [0xde, 0xad, 0xbe, 0xef]

/-- Run the model's public entry point named by the payload selector in the callback frame.
`none` is an instrumentation failure. -/
def runCallback (model : CompilationModel) (oracle : DenoteOracle) (world : Verity.ContractState)
    (callee : Nat) (calldata : Bytes) : Option FrameResult :=
  let frame := callbackWorld world callee calldata
  let selector := payloadSelector calldata
  match model.functions.filter fun fn =>
      !fn.isInternal && (KeccakEngine.keccak256_selector (functionSignature fn)).toNat == selector with
  | [fn] =>
      match bindExternalParams selector fn.bindingParams frame.calldata with
      | none => some ⟨false, [], beginReentrantFrame frame⟩
      | some bindings =>
          match executeReentrantBody oracle (effectiveFields model) frame bindings fn.body
              model.errors with
          | .ok result => some result
          | .error _ => none
  | [] => some ⟨false, [], beginReentrantFrame frame⟩
  | _ => none

/-- Commit a successful callback into the caller: `commitCalleeWorld`, with the callback's logs
and call journal appended to the caller's (the callback frame starts both empty). -/
def commitCallback (caller callback : Verity.ContractState) : Verity.ContractState :=
  { commitCalleeWorld caller callback with
    events := caller.events ++ callback.events
    calls := caller.calls ++ callback.calls }

@[simp] theorem commitCallback_storageWords (caller callback : Verity.ContractState) :
    (commitCallback caller callback).storageWords = callback.storageWords := rfl

@[simp] theorem commitCallback_events (caller callback : Verity.ContractState) :
    (commitCallback caller callback).events = caller.events ++ callback.events := rfl

@[simp] theorem commitCallback_sender (caller callback : Verity.ContractState) :
    (commitCallback caller callback).sender = caller.sender := rfl

/-- The responder's storage after counting one answered call to `account`. -/
def countCall (world : Verity.ContractState) (account : Nat) : Verity.ContractState :=
  world.withStorageWords fun key =>
    if key == .contractSlot account 4 then
      Verity.Core.Uint256.ofNat ((slotValue world account 4 + 1) % 2 ^ 256)
    else world.storageWords key

/-- Slots a call reads or writes: the configuration and the counter. -/
def touchedSlots (account : Nat) : List Verity.StorageKey :=
  (List.range 5).map (.contractSlot account)

/-- Response of the configured accounts; empty accounts answer every call with empty success
and touch nothing. -/
def respond (model : CompilationModel) (oracle : DenoteOracle) (accounts : List Nat)
    (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if request.value != 0 then .revert [] []
  else if accounts.contains request.target then
    let account := request.target
    let touched := touchedSlots account
    -- The fallback writes the counter, which a `staticcall` forbids: an exceptional halt.
    if request.kind != .call then .exceptional touched else
    let counted := countCall world account
    match runCallback model oracle counted account (payload world account) with
    | none => .revert instrumentationBytes touched
    | some result =>
        if !result.success then .revert result.data touched
        else if slotValue world account 3 % 2 == 1 then .revert [] touched
        else .success (commitCallback counted result.world) [] touched
  else .success world [] []

/-- A `staticcall` commits only the world it started from. -/
theorem respond_staticcall_valid (model : CompilationModel) (oracle : DenoteOracle)
    (accounts : List Nat) (request : Request) (world : Verity.ContractState)
    (hstatic : request.kind = .staticcall) :
    Response.valid request world (respond model oracle accounts request world) := by
  unfold respond
  by_cases hvalue : (request.value != 0) = true
  · simp [hvalue, Response.valid]
  · by_cases haccount : request.target ∈ accounts
    · simp [hvalue, haccount, hstatic, Response.valid,
        show (Kind.staticcall != Kind.call) = true from rfl]
    · simp [hvalue, haccount, Response.valid]

/-- Every configured account holds a well-formed configuration and an unsaturated counter. -/
def wellFormed (world : Verity.ContractState) (account : Nat) : Bool :=
  slotValue world account 0 < 2 ^ 32 && slotValue world account 1 ≤ 1 &&
    slotValue world account 4 + 1 < 2 ^ 256

def environment (model : CompilationModel) (oracle : DenoteOracle) (accounts : List Nat)
    (gas : Nat) (emptyAccounts : List Nat := []) : ByteCallEnvironment :=
  { gas := some gas
    adversary := some
      { respond := respond model oracle accounts
        accepts := fun request world =>
          (request.kind == .call || request.kind == .staticcall) && request.value == 0 &&
          request.target != world.thisAddress.val && !reservedPrecompile request.target &&
          (emptyAccounts.contains request.target ||
            (accounts.contains request.target && wellFormed world request.target &&
              -- A callback that does not execute fails the run; no `try` can hide it.
              (request.kind != .call ||
                (runCallback model oracle (countCall world request.target) request.target
                  (payload world request.target)).isSome)))
        valid := by
          intro request world
          by_cases hstatic : request.kind = .staticcall
          · exact respond_staticcall_valid model oracle accounts request world hstatic
          · cases respond model oracle accounts request world <;>
              simp [Response.valid, hstatic] } }

private def decimal (value : Lean.Json) : Except String Nat := do
  let text ← value.getStr?
  let some n := text.toNat? | throw "reentrant callback mock expects decimal words"
  unless n < 2^256 do throw "reentrant callback mock word exceeds uint256"
  return n

/-- Parse `reentrant-callback-v1` for `model`; every other program is configured by
`CallResponderMocks.configure`. The account lists are a code deployment model, not inferred
from requested slots. -/
def configure (model : CompilationModel) (oracle : DenoteOracle) (input : Lean.Json) :
    Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  let program ← config.getObjValAs? String "program"
  unless program == "reentrant-callback-v1" do return ← CallResponderMocks.configure input
  let caller ← decimal (← input.getObjVal? "account")
  let accounts ← (← (← config.getObjVal? "accounts").getArr?).toList.mapM fun entry => do
    let address ← decimal entry
    unless address < 2^160 && !reservedPrecompile address && address != caller do
      throw "invalid reentrant callback account"
    return address
  unless accounts.eraseDups.length == accounts.length do
    throw "duplicate reentrant callback account"
  let emptyAccounts ← (← (← config.getObjVal? "emptyAccounts").getArr?).toList.mapM fun entry => do
    let address ← decimal entry
    unless address < 2^160 && !reservedPrecompile address && address != caller &&
        !accounts.contains address do
      throw "invalid empty reentrant callback account"
    return address
  unless emptyAccounts.eraseDups.length == emptyAccounts.length do
    throw "duplicate empty reentrant callback account"
  return environment model oracle accounts (← decimal (← config.getObjVal? "gas")) emptyAccounts

end Compiler.CompilationModel.SolidityImport.ReentrantCallResponderMocks
