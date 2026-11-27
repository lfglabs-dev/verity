import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.Transactions

/-!
Synthetic clean-room smoke checks for R7:
- OpenZeppelin v5 `LowLevelCall.returnData()` (`InlineAssembly` returning `bytes memory`
  via `returndatasize()` + `returndatacopy(...)`)
- `Address.functionCall`, `Address.functionCallWithValue`, `Address.functionStaticCall`
- Direct `LowLevelCall.returnData()` and `.length`
- `abi.decode(Address.functionCall(...), (uint256))` and `abi.decode(Address.functionStaticCall(...), (uint256))`
- `Errors.InsufficientBalance`, `AddressEmptyCode`, `LowLevelCall.bubbleRevert`, `Errors.FailedCall`
- Negative control: `delegatecall` (`Address.functionDelegateCall`) remains rejected.
-/
namespace SolidityImportSmoke.LowLevelReturnDataChecks
open Compiler.CompilationModel Denote ByteExternalCall
open Compiler.CompilationModel.SolidityImport.Transactions

solidity_profile r7Profile where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import imported from "Contracts/SolidityImportSmoke" entry "LowLevelReturnDataFixture.sol"
  using r7Profile
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

#guard imported.report.functions.length == 9
#guard imported.report.functions.all (·.denoteCovered)

-- Delegatecall must remain rejected.
/--
error: LowLevelReturnDataFixture.sol:143:39: MemberAccess: [solidity-import:unsupported] external contract calls are outside this slice
closure: LowLevelDelegateCallRejected.exec -> DelegateCallLib.functionDelegateCall
target.delegatecall
-/
#guard_msgs in
solidity_import rejectedDelegateCall from "Contracts/SolidityImportSmoke" entry "LowLevelReturnDataFixture.sol"
  using r7Profile
  contract LowLevelDelegateCallRejected
  function exec(address,bytes)

private def selfAddr : Nat := 0xc0de
private def wordTarget : Nat := 0xa1
private def echoTarget : Nat := 0xa2
private def silentTarget : Nat := 0xa3
private def revertPayloadTarget : Nat := 0xb1
private def revertEmptyTarget : Nat := 0xb2
private def eoaTarget : Nat := 0xe0

private def respond (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if request.target == wordTarget then
    let val := 42 + request.value + request.calldata.length
    .success world (wordBytes val) []
  else if request.target == echoTarget then
    .success world request.calldata []
  else if request.target == silentTarget then
    .success world [] []
  else if request.target == revertPayloadTarget then
    .revert [0xde, 0xad, 0xbe, 0xef, 0x01, 0x02] []
  else if request.target == revertEmptyTarget then
    .revert [] []
  else
    .success world [] []

private def env : ByteCallEnvironment :=
  { gas := some 1000000
    adversary := some
      { respond
        valid := by
          intro request world
          unfold respond
          by_cases h1 : (request.target == wordTarget) = true
          · simp [h1, Response.valid]
          · simp only [h1, Bool.false_eq_true, ↓reduceIte]
            by_cases h2 : (request.target == echoTarget) = true
            · simp [h2, Response.valid]
            · simp only [h2, Bool.false_eq_true, ↓reduceIte]
              by_cases h3 : (request.target == silentTarget) = true
              · simp [h3, Response.valid]
              · simp only [h3, Bool.false_eq_true, ↓reduceIte]
                by_cases h4 : (request.target == revertPayloadTarget) = true
                · simp [h4, Response.valid]
                · simp only [h4, Bool.false_eq_true, ↓reduceIte]
                  by_cases h5 : (request.target == revertEmptyTarget) = true <;>
                    simp [h5, Response.valid] } }

private def bytesTail (data : List UInt8) : List Nat :=
  data.length :: (List.range ((data.length + 31) / 32)).map fun word =>
    (List.range 32).foldl (fun acc lane => acc * 256 + (data.getD (32 * word + lane) 0).toNat) 0

private def mkWorld (balance : Nat := 1000) (tx : DenoteTransaction) : Verity.ContractState :=
  let base := { withTransactionContext Verity.defaultState tx with
    selfBalance := Verity.Core.Uint256.ofNat balance }
  { base with
    accountWorld := fun a =>
      let prev := base.accountWorld a
      if a.val == selfAddr || a.val == wordTarget || a.val == echoTarget ||
         a.val == silentTarget || a.val == revertPayloadTarget || a.val == revertEmptyTarget then
        { prev with code := [⟨0x60, by decide⟩, ⟨0x00, by decide⟩] }
      else prev }

private def observe (name : String) (args : List Nat) (balance : Nat := 1000) :
    Option (Bool × List UInt8 × Nat × Nat × Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let tx : DenoteTransaction := { sender := 0x5e, thisAddress := selfAddr, functionSelector := 0, args }
  let world := mkWorld balance tx
  let bindings ← bindExternalParams 0 fn.bindingParams args
  match executeBody SolidityImport.Differential.oracle (effectiveFields imported.model) world
      bindings fn.body imported.model.errors env with
  | .ok r => some (r.success, r.data, r.world.selfBalance.val,
      (r.world.readSlot 0).val, (r.world.readSlot 1).val)
  | .error _ => none

-- `FailedCall()` selector: 0xd6bda275
private def failedCallBytes : List UInt8 := [0xd6, 0xbd, 0xa2, 0x75]
-- `AddressEmptyCode(address)` selector: 0x9996b315
private def addressEmptyCodeBytes (addr : Nat) : List UInt8 :=
  [0x99, 0x96, 0xb3, 0x15] ++ wordBytes addr
-- `InsufficientBalance(uint256,uint256)` selector: 0xcf479181
private def insufficientBalanceBytes (bal need : Nat) : List UInt8 :=
  [0xcf, 0x47, 0x91, 0x81] ++ wordBytes bal ++ wordBytes need

-- ABI encoding of `bytes memory` return: offset=32, length, padded payload words.
private def abiBytesReturn (data : List UInt8) : List UInt8 :=
  let padded := data ++ List.replicate ((32 - data.length % 32) % 32) 0
  wordBytes 32 ++ wordBytes data.length ++ padded

-- 1. `Address.functionCall` returning raw `bytes memory` (non-32-byte payload).
#guard observe "callRawBytes" ([echoTarget, 64] ++ bytesTail [0x11, 0x22, 0x33, 0x44, 0x55]) ==
  some (true, abiBytesReturn [0x11, 0x22, 0x33, 0x44, 0x55], 1000, 1, 0)

-- 2. `Address.functionCall` to a contract returning empty bytes (has code -> succeeds with empty bytes).
#guard observe "callRawBytes" ([silentTarget, 64] ++ bytesTail [0xaa]) ==
  some (true, abiBytesReturn [], 1000, 1, 0)

-- 3. `Address.functionCall` to an EOA (empty code + empty returndata -> reverts `AddressEmptyCode`).
#guard observe "callRawBytes" ([eoaTarget, 64] ++ bytesTail [0xaa]) ==
  some (false, addressEmptyCodeBytes eoaTarget, 1000, 0, 0)

-- 4. `Address.functionCall` bubbles custom revert payload verbatim.
#guard observe "callRawBytes" ([revertPayloadTarget, 64] ++ bytesTail [0x01]) ==
  some (false, [0xde, 0xad, 0xbe, 0xef, 0x01, 0x02], 1000, 0, 0)

-- 5. `Address.functionCall` on empty revert reverts `Errors.FailedCall()`.
#guard observe "callRawBytes" ([revertEmptyTarget, 64] ++ bytesTail [0x01]) ==
  some (false, failedCallBytes, 1000, 0, 0)

-- 6. `abi.decode(Address.functionCall(...), (uint256))`: 42 + 0 + 4 = 46.
#guard observe "callDecodeWord" ([wordTarget, 64] ++ bytesTail [1, 2, 3, 4]) ==
  some (true, wordBytes 46, 1000, 1, 0)

-- 7. `Address.functionCallWithValue` with nonzero value: 42 + 25 + 2 = 69, balance debited to 975.
#guard observe "callWithValueDecode" ([wordTarget, 96, 25] ++ bytesTail [9, 8]) ==
  some (true, wordBytes 69, 975, 1, 0)

-- 8. `Address.functionCallWithValue` when balance < value -> reverts `Errors.InsufficientBalance`.
#guard observe "callWithValueDecode" ([wordTarget, 96, 2000] ++ bytesTail [9]) (balance := 1000) ==
  some (false, insufficientBalanceBytes 1000 2000, 1000, 0, 0)

-- 9. Discarded `Address.functionCall` still executes and reverts on failure.
#guard observe "callDiscard" ([silentTarget, 64] ++ bytesTail [0x01]) ==
  some (true, wordBytes 1, 1000, 1, 0)
#guard observe "callDiscard" ([revertPayloadTarget, 64] ++ bytesTail [0x01]) ==
  some (false, [0xde, 0xad, 0xbe, 0xef, 0x01, 0x02], 1000, 0, 0)

-- 10. `Address.functionStaticCall` raw bytes + `abi.decode` + empty-code + bubbleRevert + FailedCall.
#guard observe "staticCallRawBytes" ([echoTarget, 64] ++ bytesTail [7, 8, 9]) ==
  some (true, abiBytesReturn [7, 8, 9], 1000, 0, 0)
#guard observe "staticCallDecodeWord" ([wordTarget, 64] ++ bytesTail [1, 2, 3]) ==
  some (true, wordBytes 45, 1000, 0, 0)
#guard observe "staticCallRawBytes" ([eoaTarget, 64] ++ bytesTail [1]) ==
  some (false, addressEmptyCodeBytes eoaTarget, 1000, 0, 0)
#guard observe "staticCallRawBytes" ([revertPayloadTarget, 64] ++ bytesTail [1]) ==
  some (false, [0xde, 0xad, 0xbe, 0xef, 0x01, 0x02], 1000, 0, 0)
#guard observe "staticCallRawBytes" ([revertEmptyTarget, 64] ++ bytesTail [1]) ==
  some (false, failedCallBytes, 1000, 0, 0)

-- 11. Direct `LowLevelCall.returnData()` and `LowLevelCall.returnData().length`.
#guard observe "directReturnData" ([echoTarget, 64] ++ bytesTail [1, 2, 3, 4, 5, 6, 7]) ==
  some (true, wordBytes 1 ++ wordBytes 7, 1000, 1, 0)
#guard observe "directReturnData" ([revertPayloadTarget, 64] ++ bytesTail [1]) ==
  some (true, wordBytes 0 ++ wordBytes 6, 1000, 1, 0)
#guard observe "directReturnDataLength" ([echoTarget, 64] ++ bytesTail [1, 2, 3, 4, 5]) ==
  some (true, wordBytes 1 ++ wordBytes 5, 1000, 0, 0)

end SolidityImportSmoke.LowLevelReturnDataChecks
