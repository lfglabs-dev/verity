import Compiler.SolidityImport.StaticOracleMocks

/-! Explicit configurable recording call responder for differential validation
of value-free low-level `CALL`s. It mirrors `RecordingCallResponder` in
`Contracts/SolidityImportSmoke/ExternalCodeAndLowLevelCallResponder.sol`: slots
0..2 are the response value, failure flag and response length; every call reads
them, increments the call counter in slot 3 and records the calldata size and
first four calldata words in slots 4..8 before answering. A failed response rolls
those writes back; the accessed slots stay observable. Response bytes, writes and
accesses are computed from the current world and request, never copied from an
EVM trace. Gas equivalence is not claimed; campaigns supply ample real EVM gas.
-/
namespace Compiler.CompilationModel.SolidityImport.CallResponderMocks

open Denote DenoteByteExternalCalls ByteExternalCall StaticOracleMocks

/-- `calldataload(offset)`: 32 calldata bytes from `offset`, zero padded. -/
def calldataWord (calldata : Bytes) (offset : Nat) : Nat :=
  (List.range 32).foldl (fun word index => word * 256 + (calldata.getD (offset + index) 0).toNat) 0

/-- The responder's storage after one recorded call to `account`. -/
def record (world : Verity.ContractState) (account : Nat) (calldata : Bytes) :
    Verity.ContractState :=
  let recorded : List (Nat × Nat) :=
    [(3, ((world.storageWords (.contractSlot account 3)).val + 1) % 2^256),
     (4, calldata.length), (5, calldataWord calldata 0), (6, calldataWord calldata 32),
     (7, calldataWord calldata 64), (8, calldataWord calldata 96)]
  world.withStorageWords fun key =>
    match recorded.find? (fun (slot, _) => key == .contractSlot account slot) with
    | some (_, value) => Verity.Core.Uint256.ofNat value
    | none => world.storageWords key

/-- Response of the configured accounts; empty accounts answer every call with
empty success and touch nothing. -/
def respond (accounts : List Nat) (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if request.kind != .call || request.value != 0 then .revert [] []
  else if accounts.contains request.target then
    let slot := fun index => (world.storageWords (.contractSlot request.target index)).val
    let touched := (List.range 9).map (Verity.StorageKey.contractSlot request.target)
    let data := responseBytes (slot 0) (slot 2)
    if slot 1 % 256 != 0 then .revert data touched
    else .success (record world request.target request.calldata) data touched
  else .success world [] []

def environment (accounts : List Nat) (gas : Nat) (emptyAccounts : List Nat := []) :
    ByteCallEnvironment :=
  { gas := some gas
    adversary := some
      { respond := respond accounts
        -- The counter never overflows within a campaign; its wrap is outside the domain.
        accepts := fun request world =>
          request.kind == .call && request.value == 0 &&
          request.target != world.thisAddress.val && !reservedPrecompile request.target &&
          (emptyAccounts.contains request.target ||
            (accounts.contains request.target &&
              (world.storageWords (.contractSlot request.target 3)).val + 1 < 2^256))
        valid := by
          intro request world
          by_cases hstatic : request.kind = .staticcall
          · have hrevert : respond accounts request world = .revert [] [] := by
              simp [respond, hstatic, show (Kind.staticcall != Kind.call) = true from rfl]
            rw [hrevert]
            trivial
          · cases respond accounts request world <;> simp [Response.valid, hstatic] } }

private def decimal (value : Lean.Json) : Except String Nat := do
  let text ← value.getStr?
  let some n := text.toNat? | throw "call responder mock expects decimal words"
  unless n < 2^256 do throw "call responder mock word exceeds uint256"
  return n

/-- Parse `recording-call-responder-v1`; every other program is configured by
`StaticOracleMocks.configure`. The account lists are a code deployment model,
not inferred from requested slots. -/
def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  let program ← config.getObjValAs? String "program"
  unless program == "recording-call-responder-v1" do return ← StaticOracleMocks.configure input
  let caller ← decimal (← input.getObjVal? "account")
  let accounts ← (← (← config.getObjVal? "accounts").getArr?).toList.mapM fun entry => do
    let address ← decimal entry
    unless address < 2^160 && !reservedPrecompile address && address != caller do
      throw "invalid call responder mock account"
    return address
  unless accounts.eraseDups.length == accounts.length do throw "duplicate call responder account"
  let emptyAccounts ← (← (← config.getObjVal? "emptyAccounts").getArr?).toList.mapM fun entry => do
    let address ← decimal entry
    unless address < 2^160 && !reservedPrecompile address && address != caller &&
        !accounts.contains address do
      throw "invalid empty call responder account"
    return address
  unless emptyAccounts.eraseDups.length == emptyAccounts.length do
    throw "duplicate empty call responder account"
  return environment accounts (← decimal (← config.getObjVal? "gas")) emptyAccounts

end Compiler.CompilationModel.SolidityImport.CallResponderMocks
