import Compiler.SolidityImport.CallResponderMocks
import Compiler.SolidityImport.AdversarialEntryPointInvariants
import Compiler.CompilationModel.AbiHelpers
import Compiler.Keccak.Sponge

/-! Explicit configurable re-entrant call responder for differential validation of contracts
whose callee calls them back. It mirrors `ReentrantCallbackHook` in
`Contracts/SolidityImportSmoke/ReentrantCallbackHook.sol`: slot 0 holds the callback selector,
slot 1 the argument count (0..3), slots 2..4 the argument words, slot 5 the flags, and slot 6
counts answered calls.

Flags:
* bit 0 (`1`): revert with no data after a successful callback (or inert call).
* bit 1 (`2`): inert callee (increment the counter without calling back, then return or revert).
* bit 2 (`4`): read-only view responder (write no storage, return `arg0` as 32 bytes; answers
  both `CALL` and `STATICCALL`).

A value-free `CALL` to a configured account (without bit 2) increments the counter, then (unless
bit 1 is set) calls the caller back with the payload (the four selector bytes, followed by
`argumentCount` 32-byte argument words), as the EVM's `CALL` frame: `msg.sender` is the account,
the calldata and selector are the payload's, no value; memories, return data and journals start
empty and transient storage is the transaction's (`beginReentrantFrame`). The payload selector
picks the model's own public entry point, which runs through the production frame runner
`executeReentrantBody` with a depth-bounded nested byte-call environment (`depth`), so a
re-entrant callback may itself invoke inert (`bit 1`) or view (`bit 2`) callees without
unbounded recursion. A successful callback is committed with the caller's frame restored
(`commitCallback`): the callback's logs and call journal follow the caller's, as the EVM appends
a successful frame's logs to the transaction's. With flag bit 0 the account then reverts with no
data. A failed callback is bubbled with its exact revert bytes. Arguments that do not decode
revert with no data, as solc's decoder does.

Limits. A selector that names no entry point reverts with no data, which matches solc's
dispatcher only for a contract without `fallback` or `receive`. The callback frame runs with
every immutable read as 0 and with `depth - 1` nested callback depth, so a fixture whose
callbacks read immutables, or re-enter beyond the configured depth, is outside this instrument.
An execution error (an unsupported construct, or exceeding callback depth) is an instrumentation
failure: the request is outside `accepts`, so the model run fails instead of producing a
Solidity outcome that a `try` could catch. Value-bearing calls and transient-storage branches
are modelled but not exercised by `check_reentrant_callback.py`. Answers, writes and accesses
are computed from the current world and request, never copied from an EVM trace.

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

/-- Flag bit 0: revert with no data after a successful callback or inert call. -/
def isRevertAfter (world : Verity.ContractState) (account : Nat) : Bool :=
  slotValue world account 5 % 2 == 1

/-- Flag bit 1: inert callee that counts the call without calling back. -/
def isNoCallback (world : Verity.ContractState) (account : Nat) : Bool :=
  (slotValue world account 5 / 2) % 2 == 1

/-- Flag bit 2: read-only view responder returning `arg0` (32 bytes) without writing storage. -/
def isPureWord (world : Verity.ContractState) (account : Nat) : Bool :=
  (slotValue world account 5 / 4) % 2 == 1

/-- The callback calldata: the four selector bytes, then `argumentCount` 32-byte words. -/
def payload (world : Verity.ContractState) (account : Nat) : Bytes :=
  let selector := (List.range 4).map fun index =>
    UInt8.ofNat (slotValue world account 0 / 2 ^ (8 * (3 - index)) % 256)
  let count := slotValue world account 1
  let words := (List.range count).flatMap fun argIndex =>
    (List.range 32).map fun byteIndex =>
      UInt8.ofNat (slotValue world account (2 + argIndex) / 2 ^ (8 * (31 - byteIndex)) % 256)
  selector ++ words

/-- The calldata words after the selector, zero padded, as the frame's `calldata`. -/
def payloadWords (calldata : Bytes) : List Nat :=
  (List.range ((calldata.length - 4 + 31) / 32)).map fun index =>
    calldataWord calldata (4 + 32 * index)

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

/-- Run the model's public entry point named by the payload selector in the callback frame,
using `nestedCalls` for any nested byte calls inside the callback. `none` is an instrumentation
failure. -/
def runCallback (model : CompilationModel) (oracle : DenoteOracle) (world : Verity.ContractState)
    (callee : Nat) (calldata : Bytes) (nestedCalls : ByteCallEnvironment := {}) :
    Option FrameResult :=
  let frame := callbackWorld world callee calldata
  let selector := payloadSelector calldata
  match model.functions.filter fun fn =>
      !fn.isInternal &&
        (KeccakEngine.keccak256_selector (functionSignature fn)).toNat == selector with
  | [fn] =>
      match bindExternalParams selector fn.bindingParams frame.calldata with
      | none => some ⟨false, [], beginReentrantFrame frame⟩
      | some bindings =>
          match executeReentrantBody oracle (effectiveFields model) frame bindings fn.body
              model.errors (byteCalls := nestedCalls) with
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
    if key == .contractSlot account 6 then
      Verity.Core.Uint256.ofNat ((slotValue world account 6 + 1) % 2 ^ 256)
    else world.storageWords key

/-- Slots a call reads or writes: the configuration and the counter. -/
def touchedSlots (account : Nat) : List Verity.StorageKey :=
  (List.range 7).map (.contractSlot account)

/-- Every configured account holds a well-formed configuration and an unsaturated counter. -/
def wellFormed (world : Verity.ContractState) (account : Nat) : Bool :=
  slotValue world account 0 < 2 ^ 32 && slotValue world account 1 ≤ 3 &&
    slotValue world account 6 + 1 < 2 ^ 256

/-- Response of the configured accounts up to `depth` nested callback levels; empty accounts
answer every call with empty success and touch nothing. -/
def respondWith (model : CompilationModel) (oracle : DenoteOracle) (accounts : List Nat)
    (nestedCalls : ByteCallEnvironment) (allowCallback : Bool)
    (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if request.value != 0 then .revert [] []
  else if accounts.contains request.target then
    let account := request.target
    let touched := touchedSlots account
    if isPureWord world account then
      .success world (wordBytes (slotValue world account 2)) touched
    else if request.kind != .call then .exceptional touched
    else
      let counted := countCall world account
      if isNoCallback world account then
        if isRevertAfter world account then .revert [] touched
        else .success counted [] touched
      else if !allowCallback then .revert instrumentationBytes touched
      else
        match runCallback model oracle counted account (payload world account) nestedCalls with
        | none => .revert instrumentationBytes touched
        | some result =>
            if !result.success then .revert result.data touched
            else if isRevertAfter world account then .revert [] touched
            else .success (commitCallback counted result.world) [] touched
  else .success world [] []

/-- A `staticcall` commits only the world it started from. -/
theorem respondWith_staticcall_valid (model : CompilationModel) (oracle : DenoteOracle)
    (accounts : List Nat) (nestedCalls : ByteCallEnvironment) (allowCallback : Bool)
    (request : Request) (world : Verity.ContractState)
    (hstatic : request.kind = .staticcall) :
    Response.valid request world
      (respondWith model oracle accounts nestedCalls allowCallback request world) := by
  unfold respondWith
  by_cases hvalue : (request.value != 0) = true
  · simp [hvalue, Response.valid]
  · by_cases haccount : request.target ∈ accounts
    · by_cases hpure : isPureWord world request.target = true
      · simp [hvalue, haccount, hpure, Response.valid]
      · simp [hvalue, haccount, hpure, hstatic, Response.valid,
          show (Kind.staticcall != Kind.call) = true from rfl]
    · simp [hvalue, haccount, Response.valid]

/-- Depth-bounded re-entrant byte-call environment. At `depth = 0` only `isPureWord`,
`isNoCallback`, and `emptyAccounts` are accepted; at `depth + 1`, callback-making hooks invoke
`runCallback` with the `depth` environment. -/
def environmentAt (model : CompilationModel) (oracle : DenoteOracle) (accounts : List Nat)
    (gas : Nat) (emptyAccounts : List Nat := []) : Nat → ByteCallEnvironment
  | 0 =>
      { gas := some gas
        adversary := some
          { respond := respondWith model oracle accounts {} false
            accepts := fun request world =>
              (request.kind == .call || request.kind == .staticcall) && request.value == 0 &&
              request.target != world.thisAddress.val && !reservedPrecompile request.target &&
              (emptyAccounts.contains request.target ||
                (accounts.contains request.target && wellFormed world request.target &&
                  (isPureWord world request.target || isNoCallback world request.target ||
                    request.kind != .call)))
            valid := by
              intro request world
              by_cases hstatic : request.kind = .staticcall
              · exact respondWith_staticcall_valid model oracle accounts {} false request world
                  hstatic
              · cases respondWith model oracle accounts {} false request world <;>
                  simp [Response.valid, hstatic] } }
  | depth + 1 =>
      let nested := environmentAt model oracle accounts gas emptyAccounts depth
      { gas := some gas
        adversary := some
          { respond := respondWith model oracle accounts nested true
            accepts := fun request world =>
              (request.kind == .call || request.kind == .staticcall) && request.value == 0 &&
              request.target != world.thisAddress.val && !reservedPrecompile request.target &&
              (emptyAccounts.contains request.target ||
                (accounts.contains request.target && wellFormed world request.target &&
                  (isPureWord world request.target || isNoCallback world request.target ||
                    request.kind != .call ||
                    (runCallback model oracle (countCall world request.target) request.target
                      (payload world request.target) nested).isSome)))
            valid := by
              intro request world
              by_cases hstatic : request.kind = .staticcall
              · exact respondWith_staticcall_valid model oracle accounts nested true request world
                  hstatic
              · cases respondWith model oracle accounts nested true request world <;>
                  simp [Response.valid, hstatic] } }

/-- Default re-entrant byte-call environment allowing one callback level (whose body may invoke
inert or view callees). -/
def environment (model : CompilationModel) (oracle : DenoteOracle) (accounts : List Nat)
    (gas : Nat) (emptyAccounts : List Nat := []) : ByteCallEnvironment :=
  environmentAt model oracle accounts gas emptyAccounts 1

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
