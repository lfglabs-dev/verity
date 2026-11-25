import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.CallResponderMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.TransientWithSlotGetterModel
open Compiler.CompilationModel Denote DenoteByteExternalCalls ByteExternalCall
open Compiler.CompilationModel.SolidityImport.StaticOracleMocks

solidity_import imported from "Contracts/SolidityImportSmoke" entry "TransientWithSlotGetterFixture.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract TransientWithSlotGetterFixture
  function addDirect(uint256,address)
  function addInBatch(uint256,uint256,address)
  function addInBatchRevert(uint256,address)
  function staticCallInBatch(address,bytes,address)
  function callInBatch(address,bytes,address)
  function renamedStaticCallInBatch(address,bytes,address)
  function readState(address)
  function queuePushAndSumInBatch(uint256,uint256,address,bytes,address)
  function queuePushAndRevert(uint256,address)
  function readQueueProbe(uint256)

def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle

/-- Configurable differential responder matching the Solidity mock in
`check_transient_with_slot_getter.py` (same layout as `LowLevelR7Responder`). -/
def respondR9b (accounts : List Nat) (request : Request) (world : Verity.ContractState) :
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

theorem respondR9b_staticcall_valid (accounts : List Nat) (request : Request)
    (world : Verity.ContractState) (hstatic : request.kind = .staticcall) :
    Response.valid request world (respondR9b accounts request world) := by
  unfold respondR9b
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
  let some n := text.toNat? | throw "r9b responder expects decimal words"
  unless n < 2^256 do throw "r9b responder word exceeds uint256"
  return n

def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  let program ← config.getObjValAs? String "program"
  unless program == "r9b-responder-v1" do return ← SolidityImport.CallResponderMocks.configure input
  let caller ← decimal (← input.getObjVal? "account")
  let accounts ← (← (← config.getObjVal? "accounts").getArr?).toList.mapM fun entry => do
    let address ← decimal entry
    unless address < 2^160 && !reservedPrecompile address && address != caller do
      throw "invalid r9b responder account"
    return address
  let emptyAccounts ← (← (← config.getObjVal? "emptyAccounts").getArr?).toList.mapM fun entry => do
    let address ← decimal entry
    unless address < 2^160 && !reservedPrecompile address && address != caller &&
        !accounts.contains address do
      throw "invalid empty r9b responder account"
    return address
  let gas ← decimal (← config.getObjVal? "gas")
  pure
    { gas := some gas
      adversary := some
        { respond := respondR9b accounts
          accepts := fun request world =>
            (request.kind == .call || request.kind == .staticcall) &&
            request.target != world.thisAddress.val && !reservedPrecompile request.target &&
            (emptyAccounts.contains request.target || accounts.contains request.target)
          valid := by
            intro request world
            by_cases hstatic : request.kind = .staticcall
            · exact respondR9b_staticcall_valid accounts request world hstatic
            · cases respondR9b accounts request world <;> simp [Response.valid, hstatic] } }

end SolidityImportSmoke.TransientWithSlotGetterModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.TransientWithSlotGetterModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.TransientWithSlotGetterModel.model
        SolidityImportSmoke.TransientWithSlotGetterModel.oracle args
        (configure := SolidityImportSmoke.TransientWithSlotGetterModel.configure)
