import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.ReentrantCallResponderMocks
import Compiler.CompilationModel

/-!
Denote twin of `ForwardedBytesTupleResponder.sol` for `ForwardedBytesTupleCall.sol`
A/B/C differential campaigns (Refs #2803, Refs #2842).
-/
namespace SolidityImportSmoke.ForwardedBytesTupleCallMocks

open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport
open Compiler.CompilationModel.Denote Compiler.CompilationModel.DenoteByteExternalCalls
open Compiler.CompilationModel.ByteExternalCall
open Compiler.CompilationModel.SolidityImport.StaticOracleMocks
open Compiler.CompilationModel.SolidityImport.CallResponderMocks
open Compiler.CompilationModel.SolidityImport.ReentrantCallResponderMocks

private def rSlot (world : Verity.ContractState) (account slot : Nat) : Nat :=
  (world.storageWords (.contractSlot account slot)).val

private def rawResponseBytes (world : Verity.ContractState) (account : Nat) : Bytes :=
  let len := rSlot world account 6
  let full := (List.range 6).flatMap fun i => wordBytes (rSlot world account i)
  full.take len

private def cbPayload (world : Verity.ContractState) (account : Nat) : Bytes :=
  let sel := rSlot world account 8
  let flags := rSlot world account 7
  let selBytes := (List.range 4).map fun i => UInt8.ofNat (sel / 2 ^ (8 * (3 - i)) % 256)
  if (flags / 4) % 2 == 1 then
    selBytes ++ wordBytes (rSlot world account 9)
  else
    selBytes

private def recordResponderCall (world : Verity.ContractState) (account : Nat) (calldata : Bytes) :
    Verity.ContractState :=
  let cnt := (rSlot world account 10 + 1) % 2 ^ 256
  world.withStorageWords fun key =>
    if key == .contractSlot account 10 then Verity.Core.Uint256.ofNat cnt
    else if key == .contractSlot account 11 then Verity.Core.Uint256.ofNat calldata.length
    else if key == .contractSlot account 12 then Verity.Core.Uint256.ofNat (calldataWord calldata 0)
    else world.storageWords key

private def responderTouched (account : Nat) : List Verity.StorageKey :=
  (List.range 13).map (.contractSlot account)

private def responderWellFormed (world : Verity.ContractState) (account : Nat) : Bool :=
  rSlot world account 6 ≤ 192 && rSlot world account 8 < 2 ^ 32 &&
    rSlot world account 10 + 1 < 2 ^ 256

private def respondTuple (m : CompilationModel) (o : DenoteOracle) (accounts : List Nat)
    (allowCallback : Bool) (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if request.value != 0 then .revert [] []
  else if accounts.contains request.target then
    if request.kind != .call then .exceptional (responderTouched request.target)
    else
      let account := request.target
      let touched := responderTouched account
      let recorded := recordResponderCall world account request.calldata
      let flags := rSlot world account 7
      let doRevert := flags % 2 == 1
      let doCallback := (flags / 2) % 2 == 1
      let data := rawResponseBytes world account
      if doCallback then
        if !allowCallback then .revert instrumentationBytes touched
        else
          match runCallback m o recorded account (cbPayload world account) {} with
          | none => .revert instrumentationBytes touched
          | some result =>
              if !result.success then .revert result.data touched
              else
                let committed := commitCallback recorded result.world
                if doRevert then .revert data touched
                else .success committed data touched
      else
        if doRevert then .revert data touched
        else .success recorded data touched
  else .success world [] []

private def tupleEnvironment (m : CompilationModel) (o : DenoteOracle)
    (accounts : List Nat) (gas : Nat) (emptyAccounts : List Nat := []) : ByteCallEnvironment :=
  { gas := some gas
    adversary := some
      { respond := respondTuple m o accounts true
        accepts := fun request world =>
          (request.kind == .call || request.kind == .staticcall) && request.value == 0 &&
          request.target != world.thisAddress.val && !reservedPrecompile request.target &&
          (emptyAccounts.contains request.target ||
            (accounts.contains request.target && responderWellFormed world request.target &&
              (request.kind != .call ||
                (rSlot world request.target 7 / 2) % 2 == 0 ||
                (runCallback m o (recordResponderCall world request.target request.calldata)
                  request.target (cbPayload world request.target) {}).isSome)))
        valid := by
          intro request world
          by_cases hstatic : request.kind = .staticcall
          · unfold respondTuple
            by_cases hv : (request.value != 0) = true
            · simp [hv, Response.valid]
            · by_cases ha : request.target ∈ accounts
              · simp [hv, ha, hstatic, Response.valid,
                  show (Kind.staticcall != Kind.call) = true from rfl]
              · simp [hv, ha, Response.valid]
          · cases respondTuple m o accounts true request world <;> simp [Response.valid, hstatic] } }

private def parseNat (j : Lean.Json) : Except String Nat :=
  match j with
  | .num n =>
      if n.exponent == 0 && n.mantissa ≥ 0 then .ok n.mantissa.toNat
      else .error s!"expected non-negative integer, got {j}"
  | .str s =>
      match s.toNat? with
      | some n => .ok n
      | none => .error s!"expected uint string, got {s}"
  | _ => .error s!"expected nat JSON, got {j}"

def configure (m : CompilationModel) (o : DenoteOracle) (input : Lean.Json) :
    Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  match config.getObjVal? "program" with
  | .ok (.str "forwarded-bytes-tuple-v1") =>
      let gas ← parseNat (← config.getObjVal? "gas")
      let accounts ← match ← config.getObjVal? "accounts" with
        | .arr items => items.toList.mapM parseNat
        | _ => .error "forwarded-bytes-tuple-v1 accounts must be an array"
      let emptyAccounts ← match config.getObjVal? "emptyAccounts" with
        | .ok (.arr items) => items.toList.mapM parseNat
        | .ok _ => .error "forwarded-bytes-tuple-v1 emptyAccounts must be an array"
        | .error _ => .ok []
      .ok (tupleEnvironment m o accounts gas emptyAccounts)
  | _ => ReentrantCallResponderMocks.configure m o input

end SolidityImportSmoke.ForwardedBytesTupleCallMocks
