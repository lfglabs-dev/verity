import Verity.Core.Model.DenoteByteExternalCalls
import Lean.Data.Json

/-! Explicit configurable raw-oracle program for differential validation.
Its three storage slots are value, boolean failure, and response length. The
runtime has only a fallback, so arbitrary calldata executes the same program.
Response bytes and accessed slots are computed from the current world, not
copied from an EVM trace. Callee memory is fresh and private. Gas equivalence is
not claimed by this functional boundary; campaigns supply ample real EVM gas.
-/
namespace Compiler.CompilationModel.SolidityImport.StaticOracleMocks

open Denote DenoteByteExternalCalls ByteExternalCall

/-- The memory-safe fallback writes its return word at zero. Solidity's entry
preamble initializes mload(64)=128; remaining memory is zero. -/
def responseBytes (value length : Nat) : Bytes :=
  let memory := (DenoteMemory.Memory.empty.writeWord 64
    (DenoteMemory.valueWord (Verity.Core.Uint256.ofNat 128))).writeWord 0
    (DenoteMemory.valueWord (Verity.Core.Uint256.ofNat value))
  (List.range length).map fun offset => UInt8.ofNat (memory.readByte offset).val

/-- Only configured accounts contain the oracle program in this mock world.
Only explicitly listed empty accounts have empty code. Unknown requests and
reserved precompiles are outside this program's domain. Configured fallback
calls read all three slots before success/revert, and cannot mutate the world. -/
def reservedPrecompile (account : Nat) : Bool :=
  (1 ≤ account && account ≤ 17) || account == 256

def environment (accounts : List Nat) (gas : Nat) (emptyAccounts : List Nat := []) : ByteCallEnvironment :=
  { gas := some gas
    adversary := some { (staticAdversary fun request world =>
      if request.kind != .staticcall || request.value != 0 then (false, [], [])
      else if accounts.contains request.target then
        let value := (world.storageWords (.contractSlot request.target 0)).val
        let failure := (world.storageWords (.contractSlot request.target 1)).val % 256 != 0
        let length := (world.storageWords (.contractSlot request.target 2)).val
        (!failure, responseBytes value length,
          [.contractSlot request.target 0, .contractSlot request.target 1,
           .contractSlot request.target 2])
      else (true, [], [])) with
        accepts := fun request world =>
          request.kind == .staticcall && request.value == 0 &&
          request.target != world.thisAddress.val && !reservedPrecompile request.target &&
          (accounts.contains request.target || emptyAccounts.contains request.target) } }

private def decimal (value : Lean.Json) : Except String Nat := do
  let text ← value.getStr?
  let some n := text.toNat? | throw "oracle mock expects decimal words"
  unless n < 2^256 do throw "oracle mock word exceeds uint256"
  return n

/-- Parse the explicit mock program configuration supplied by the harness.
The account list is a code deployment model, not inferred from requested slots. -/
def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  let program ← config.getObjValAs? String "program"
  unless program == "raw-static-oracle-v1" do throw "unsupported byte-call mock program"
  let caller ← decimal (← input.getObjVal? "account")
  let accounts ← (← (← config.getObjVal? "accounts").getArr?).toList.mapM fun entry => do
    let address ← decimal entry
    unless address < 2^160 do throw "oracle mock account exceeds address width"
    unless !reservedPrecompile address do throw "oracle mock cannot replace a reserved precompile"
    unless address != caller do throw "oracle mock cannot replace caller code"
    return address
  unless accounts.eraseDups.length == accounts.length do throw "duplicate oracle mock code account"
  let emptyAccounts ← (← (← config.getObjVal? "emptyAccounts").getArr?).toList.mapM fun entry => do
    let address ← decimal entry
    unless address < 2^160 do throw "empty mock account exceeds address width"
    unless !reservedPrecompile address do throw "empty mock account is a reserved precompile"
    unless address != caller do throw "empty mock account cannot replace caller code"
    unless !accounts.contains address do throw "mock code and empty accounts overlap"
    return address
  unless emptyAccounts.eraseDups.length == emptyAccounts.length do throw "duplicate empty mock account"
  let gas ← decimal (← config.getObjVal? "gas")
  return environment accounts gas emptyAccounts

end Compiler.CompilationModel.SolidityImport.StaticOracleMocks
