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

/-- Revert payload of the selector-checked program for unexpected calldata. -/
def calldataMismatchBytes : Bytes := [0xba, 0xd0, 0xca, 0x11]

/-- `calldataload(0)`: the first 32 calldata bytes, zero padded. -/
def firstCalldataWord (calldata : Bytes) : Nat :=
  (List.range 32).foldl (fun word index => word * 256 + (calldata.getD index 0).toNat) 0

/-- `CheckedStaticOracle` in `Contracts/SolidityImportSmoke/InterfaceStaticCallOracle.sol`:
slots 0..2 are the `raw-static-oracle-v1` value, failure flag and response
length; slots 3 and 4 are the expected first calldata word and calldata length.
All five slots are read before dispatch; mismatching calldata reverts with
`calldataMismatchBytes`, otherwise the raw program's response is produced. -/
def checkedEnvironment (accounts : List Nat) (gas : Nat) (emptyAccounts : List Nat := []) :
    ByteCallEnvironment :=
  { gas := some gas
    adversary := some { (staticAdversary fun request world =>
      if request.kind != .staticcall || request.value != 0 then (false, [], [])
      else if accounts.contains request.target then
        let slot := fun index => (world.storageWords (.contractSlot request.target index)).val
        let touched := (List.range 5).map (Verity.StorageKey.contractSlot request.target)
        if request.calldata.length != slot 4 || firstCalldataWord request.calldata != slot 3 then
          (false, calldataMismatchBytes, touched)
        else
          (slot 1 % 256 == 0, responseBytes (slot 0) (slot 2), touched)
      else (true, [], [])) with
        accepts := fun request world =>
          request.kind == .staticcall && request.value == 0 &&
          request.target != world.thisAddress.val && !reservedPrecompile request.target &&
          (accounts.contains request.target || emptyAccounts.contains request.target) } }

/-- The order-sensitive calldata fold of `WordStaticOracle` in
`Contracts/SolidityImportSmoke/InterfaceWordStaticCallOracle.sol`, modulo `2^256`:
start from `31 * calldatasize + selector`, then mix in `calldataload(offset)`
for `offset = 4, 36, …` below the calldata size. -/
def calldataFold (calldata : Bytes) : Nat :=
  let size := calldata.length
  let words := (List.range ((size - 4 + 31) / 32)).map fun index =>
    firstCalldataWord (calldata.drop (4 + 32 * index))
  words.foldl (fun acc word => (acc * 31 + word) % 2^256)
    ((size * 31 + firstCalldataWord calldata / 2^224) % 2^256)

/-- `WordStaticOracle`: slots 0..3 are value, failure flag, response length and
mask, all read before responding. The response word is
`value ^ (calldataFold calldata & mask)`, so a nonzero mask makes selector,
argument words, argument order and calldata length observable. -/
def wordEnvironment (accounts : List Nat) (gas : Nat) (emptyAccounts : List Nat := []) :
    ByteCallEnvironment :=
  { gas := some gas
    adversary := some { (staticAdversary fun request world =>
      if request.kind != .staticcall || request.value != 0 then (false, [], [])
      else if accounts.contains request.target then
        let slot := fun index => (world.storageWords (.contractSlot request.target index)).val
        let touched := (List.range 4).map (Verity.StorageKey.contractSlot request.target)
        let word := Nat.xor (slot 0) (Nat.land (calldataFold request.calldata) (slot 3))
        (slot 1 % 256 == 0, responseBytes word (slot 2), touched)
      else (true, [], [])) with
        accepts := fun request world =>
          request.kind == .staticcall && request.value == 0 &&
          request.target != world.thisAddress.val && !reservedPrecompile request.target &&
          (accounts.contains request.target || emptyAccounts.contains request.target) } }

/-- Three-word response buffer for `MultiWordStaticOracle` in
`Contracts/SolidityImportSmoke/MultiWordStaticOracle.sol`: writes `w0`, `w1`, `w2`
at offsets `0`, `32`, `64` and slices `length` bytes (zero-padded past byte 96). -/
def multiWordResponseBytes (w0 w1 w2 length : Nat) : Bytes :=
  let memory := ((DenoteMemory.Memory.empty.writeWord 0
    (DenoteMemory.valueWord (Verity.Core.Uint256.ofNat w0))).writeWord 32
    (DenoteMemory.valueWord (Verity.Core.Uint256.ofNat w1))).writeWord 64
    (DenoteMemory.valueWord (Verity.Core.Uint256.ofNat w2))
  (List.range length).map fun offset => UInt8.ofNat (memory.readByte offset).val

/-- `MultiWordStaticOracle`: slots 0..5 are `word0`, `word1`, `word2`, failure flag,
response length and mask, all read before responding. `word0` is XORed with
`calldataFold calldata & mask`, so multi-return ABI decoding (valid, dirty narrow words,
short returndata, extra words, revert forwarding) and calldata folding are all observable. -/
def multiWordEnvironment (accounts : List Nat) (gas : Nat) (emptyAccounts : List Nat := []) :
    ByteCallEnvironment :=
  { gas := some gas
    adversary := some { (staticAdversary fun request world =>
      if request.kind != .staticcall || request.value != 0 then (false, [], [])
      else if accounts.contains request.target then
        let slot := fun index => (world.storageWords (.contractSlot request.target index)).val
        let touched := (List.range 6).map (Verity.StorageKey.contractSlot request.target)
        let w0 := Nat.xor (slot 0) (Nat.land (calldataFold request.calldata) (slot 5))
        (slot 3 % 256 == 0, multiWordResponseBytes w0 (slot 1) (slot 2) (slot 4), touched)
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
  unless ["raw-static-oracle-v1", "checked-static-oracle-v1", "word-static-oracle-v1",
      "multi-word-static-oracle-v1"].contains program do
    throw "unsupported byte-call mock program"
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
  return if program == "checked-static-oracle-v1" then checkedEnvironment accounts gas emptyAccounts
    else if program == "word-static-oracle-v1" then wordEnvironment accounts gas emptyAccounts
    else if program == "multi-word-static-oracle-v1" then multiWordEnvironment accounts gas emptyAccounts
    else environment accounts gas emptyAccounts

end Compiler.CompilationModel.SolidityImport.StaticOracleMocks
