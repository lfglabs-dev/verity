import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.CallResponderMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LowLevelReturnDataModel
open Compiler.CompilationModel Denote DenoteByteExternalCalls ByteExternalCall
open Compiler.CompilationModel.SolidityImport.StaticOracleMocks

solidity_import imported from "Contracts/SolidityImportSmoke" entry "LowLevelReturnDataFixture.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract LowLevelReturnDataFixture
  function callRawBytes(address,bytes)
  function callDecodeWord(address,bytes)
  function callWithValueDecode(address,bytes,uint256)
  function callDiscard(address,bytes)
  function staticCallRawBytes(address,bytes)
  function staticCallDecodeWord(address,bytes)
  function directReturnData(address,bytes)
  function directReturnDataLength(address,bytes)
  function readState()

def model : CompilationModel := imported.model
def oracle : DenoteOracle := SolidityImport.Differential.oracle

/-- Explicit configurable responder for R7 differential validation covering both
state-changing `call` (with optional ETH value) and read-only `staticcall`.
Storage layout of the paired Solidity responder (`LowLevelR7Responder`):
  slot 0: response value
  slot 1: failure flag (nonzero -> revert)
  slot 2: response byte length
  slot 3: static-safe flag (nonzero -> never writes storage, so staticcall succeeds)
  slot 4: call counter (incremented only when static-safe == 0)
  slot 5: last msg.value (recorded only when static-safe == 0)
  slot 6: last calldatasize (recorded only when static-safe == 0) -/
def respondR7 (accounts : List Nat) (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if accounts.contains request.target then
    let slot := fun index => (world.storageWords (.contractSlot request.target index)).val
    let val := slot 0
    let failed := slot 1 % 256 != 0
    let respLen := slot 2
    let staticSafe := slot 3 % 256 != 0
    if staticSafe then
      if request.value != 0 then .revert [] []
      else
        let touched := (List.range 4).map (Verity.StorageKey.contractSlot request.target)
        let data := responseBytes (val + request.calldata.length) respLen
        if failed then .revert data touched else .success world data touched
    else
      if request.kind != .call then .revert [] []
      else
        let touched := (List.range 7).map (Verity.StorageKey.contractSlot request.target)
        let data := responseBytes (val + request.value + request.calldata.length) respLen
        if failed then .revert data touched
        else
          let recorded : List (Nat × Nat) :=
            [(4, ((slot 4) + 1) % 2^256), (5, request.value), (6, request.calldata.length)]
          let nextWorld := world.withStorageWords fun key =>
            match recorded.find? (fun (s, _) => key == .contractSlot request.target s) with
            | some (_, v) => Verity.Core.Uint256.ofNat v
            | none => world.storageWords key
          .success nextWorld data touched
  else
    .success world [] []

theorem respondR7_staticcall_valid (accounts : List Nat) (request : Request)
    (world : Verity.ContractState) (hstatic : request.kind = .staticcall) :
    Response.valid request world (respondR7 accounts request world) := by
  unfold respondR7
  by_cases hacc : request.target ∈ accounts
  · simp only [List.contains_iff_mem, hacc, ↓reduceIte]
    by_cases hss : ((world.storageWords (.contractSlot request.target 3)).val % 256 != 0) = true
    · simp only [hss, ↓reduceIte]
      by_cases hv : (request.value != 0) = true
      · simp [hv, Response.valid]
      · simp only [hv, Bool.false_eq_true, ↓reduceIte]
        by_cases hf : ((world.storageWords (.contractSlot request.target 1)).val % 256 != 0) = true <;>
          simp [hf, Response.valid]
    · simp only [hss, Bool.false_eq_true, ↓reduceIte, hstatic,
        show (Kind.staticcall != Kind.call) = true from rfl, Response.valid]
  · simp [hacc, Response.valid]

private def decimal (value : Lean.Json) : Except String Nat := do
  let text ← value.getStr?
  let some n := text.toNat? | throw "r7 responder expects decimal words"
  unless n < 2^256 do throw "r7 responder word exceeds uint256"
  return n

def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  let program ← config.getObjValAs? String "program"
  unless program == "r7-responder-v1" do return ← SolidityImport.CallResponderMocks.configure input
  let caller ← decimal (← input.getObjVal? "account")
  let accounts ← (← (← config.getObjVal? "accounts").getArr?).toList.mapM fun entry => do
    let address ← decimal entry
    unless address < 2^160 && !reservedPrecompile address && address != caller do
      throw "invalid r7 responder account"
    return address
  let emptyAccounts ← (← (← config.getObjVal? "emptyAccounts").getArr?).toList.mapM fun entry => do
    let address ← decimal entry
    unless address < 2^160 && !reservedPrecompile address && address != caller &&
        !accounts.contains address do
      throw "invalid empty r7 responder account"
    return address
  let gas ← decimal (← config.getObjVal? "gas")
  pure
    { gas := some gas
      adversary := some
        { respond := respondR7 accounts
          accepts := fun request world =>
            (request.kind == .call || request.kind == .staticcall) &&
            request.target != world.thisAddress.val && !reservedPrecompile request.target &&
            (emptyAccounts.contains request.target || accounts.contains request.target)
          valid := by
            intro request world
            by_cases hstatic : request.kind = .staticcall
            · exact respondR7_staticcall_valid accounts request world hstatic
            · cases respondR7 accounts request world <;> simp [Response.valid, hstatic] } }

end SolidityImportSmoke.LowLevelReturnDataModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LowLevelReturnDataModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LowLevelReturnDataModel.model
        SolidityImportSmoke.LowLevelReturnDataModel.oracle args
        (configure := SolidityImportSmoke.LowLevelReturnDataModel.configure)
