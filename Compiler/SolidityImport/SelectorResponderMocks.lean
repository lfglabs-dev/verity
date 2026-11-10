import Compiler.SolidityImport.CallResponderMocks

/-! Explicit configurable selector-dispatched call responder for differential
validation of contracts that call several functions of one account, some by
`STATICCALL`. It mirrors `SelectorCallResponder` in
`Contracts/SolidityImportSmoke/SelectorCallResponder.sol`. Slot 0 holds the entry
count `n ≤ 8`; entry `i` occupies slots `16 + 8 i` (selector), `+ 1` (flags: bit 0
fails the answer, bit 1 marks a view entry), `+ 2` (answer length `≤ 128`) and
`+ 3 … + 6` (answer words). The first entry whose selector equals the first four
calldata bytes answers; none answering is an empty revert. A view entry answers
without writing, so a `STATICCALL` gets it too. A non-view entry increments the
counter in slot 1 and records the calldata size and first four calldata words in
slots 2..6 before answering; under `STATICCALL` that write is an exceptional halt,
and a failing answer rolls it back. Answers, writes and accesses are computed from
the current world and request, never copied from an EVM trace.
-/
namespace Compiler.CompilationModel.SolidityImport.SelectorResponderMocks

open Denote DenoteByteExternalCalls ByteExternalCall StaticOracleMocks CallResponderMocks

/-- Largest entry table the responder accepts. -/
def maxEntries : Nat := 8

/-- First slot of entry `i`. -/
def entryBase (index : Nat) : Nat := 16 + 8 * index

/-- The responder's storage word at `slot`. -/
def slotValue (world : Verity.ContractState) (account slot : Nat) : Nat :=
  (world.storageWords (.contractSlot account slot)).val

/-- The first entry whose selector matches, scanning the `n` entries in order. -/
def findEntry (world : Verity.ContractState) (account selector : Nat) : Option Nat :=
  (List.range (slotValue world account 0)).find? fun index =>
    slotValue world account (entryBase index) == selector

/-- The first `length` bytes of four big-endian words. -/
def wordsBytes (words : List Nat) (length : Nat) : Bytes :=
  (List.range length).map fun offset =>
    UInt8.ofNat (words.getD (offset / 32) 0 / 2 ^ (8 * (31 - offset % 32)) % 256)

/-- Entry answer bytes: the four answer words, truncated to the entry's length. -/
def answer (world : Verity.ContractState) (account base : Nat) : Bytes :=
  wordsBytes ((List.range 4).map fun word => slotValue world account (base + 3 + word))
    (slotValue world account (base + 2))

/-- The responder's storage after one recorded call to `account`. -/
def recordCall (world : Verity.ContractState) (account : Nat) (calldata : Bytes) :
    Verity.ContractState :=
  let recorded : List (Nat × Nat) :=
    [(1, (slotValue world account 1 + 1) % 2^256), (2, calldata.length),
     (3, calldataWord calldata 0), (4, calldataWord calldata 32),
     (5, calldataWord calldata 64), (6, calldataWord calldata 96)]
  world.withStorageWords fun key =>
    match recorded.find? (fun (slot, _) => key == .contractSlot account slot) with
    | some (_, value) => Verity.Core.Uint256.ofNat value
    | none => world.storageWords key

/-- Slots a call may read or write: the header, the records and every entry's words. -/
def touchedSlots (world : Verity.ContractState) (account : Nat) : List Verity.StorageKey :=
  ((List.range 7) ++ (List.range (8 * min (slotValue world account 0) maxEntries)).map (16 + ·)).map
    (.contractSlot account)

/-- Response of the configured accounts; empty accounts answer every call with
empty success and touch nothing. -/
def respond (accounts : List Nat) (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if request.value != 0 then .revert [] []
  else if accounts.contains request.target then
    let account := request.target
    let touched := touchedSlots world account
    match findEntry world account (calldataWord request.calldata 0 / 2^224) with
    | none => .revert [] touched
    | some index =>
        let base := entryBase index
        let flags := slotValue world account (base + 1)
        let data := answer world account base
        if flags / 2 % 2 == 1 then
          if flags % 2 == 1 then .revert data touched else .success world data touched
        else if request.kind != .call then .exceptional touched
        else if flags % 2 == 1 then .revert data touched
        else .success (recordCall world account request.calldata) data touched
  else .success world [] []

/-- A `STATICCALL` commits only the world it started from. -/
theorem respond_staticcall_valid (accounts : List Nat) (request : Request)
    (world : Verity.ContractState) (hstatic : request.kind = .staticcall) :
    Response.valid request world (respond accounts request world) := by
  unfold respond
  by_cases hvalue : (request.value != 0) = true
  · simp [hvalue, Response.valid]
  · by_cases haccount : request.target ∈ accounts
    · simp only [hvalue, haccount, List.contains_iff_mem, if_true, if_false, Bool.false_eq_true]
      split
      · simp [Response.valid]
      · split <;> (try split) <;> (try split) <;>
          simp_all [Response.valid, show (Kind.staticcall != Kind.call) = true from rfl]
    · simp [hvalue, haccount, Response.valid]

/-- Every configured account holds a well-formed table and an unsaturated counter. -/
def wellFormed (world : Verity.ContractState) (account : Nat) : Bool :=
  slotValue world account 0 ≤ maxEntries &&
    (List.range (slotValue world account 0)).all
      (fun index => slotValue world account (entryBase index + 2) ≤ 128) &&
    slotValue world account 1 + 1 < 2^256

def environment (accounts : List Nat) (gas : Nat) (emptyAccounts : List Nat := []) :
    ByteCallEnvironment :=
  { gas := some gas
    adversary := some
      { respond := respond accounts
        accepts := fun request world =>
          (request.kind == .call || request.kind == .staticcall) && request.value == 0 &&
          request.target != world.thisAddress.val && !reservedPrecompile request.target &&
          (emptyAccounts.contains request.target ||
            (accounts.contains request.target && wellFormed world request.target))
        valid := by
          intro request world
          by_cases hstatic : request.kind = .staticcall
          · exact respond_staticcall_valid accounts request world hstatic
          · cases respond accounts request world <;> simp [Response.valid, hstatic] } }

private def decimal (value : Lean.Json) : Except String Nat := do
  let text ← value.getStr?
  let some n := text.toNat? | throw "selector responder mock expects decimal words"
  unless n < 2^256 do throw "selector responder mock word exceeds uint256"
  return n

/-- Parse `selector-call-responder-v1`; every other program is configured by
`CallResponderMocks.configure`. The account lists are a code deployment model,
not inferred from requested slots. -/
def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  let program ← config.getObjValAs? String "program"
  unless program == "selector-call-responder-v1" do return ← CallResponderMocks.configure input
  let caller ← decimal (← input.getObjVal? "account")
  let accounts ← (← (← config.getObjVal? "accounts").getArr?).toList.mapM fun entry => do
    let address ← decimal entry
    unless address < 2^160 && !reservedPrecompile address && address != caller do
      throw "invalid selector responder account"
    return address
  unless accounts.eraseDups.length == accounts.length do throw "duplicate selector responder account"
  let emptyAccounts ← (← (← config.getObjVal? "emptyAccounts").getArr?).toList.mapM fun entry => do
    let address ← decimal entry
    unless address < 2^160 && !reservedPrecompile address && address != caller &&
        !accounts.contains address do
      throw "invalid empty selector responder account"
    return address
  unless emptyAccounts.eraseDups.length == emptyAccounts.length do
    throw "duplicate empty selector responder account"
  return environment accounts (← decimal (← config.getObjVal? "gas")) emptyAccounts

end Compiler.CompilationModel.SolidityImport.SelectorResponderMocks
