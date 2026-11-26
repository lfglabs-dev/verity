import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.Transactions

namespace SolidityImportSmoke.SelfDelegateAndRawSlotEip712Checks

open Compiler.CompilationModel Denote ByteExternalCall
open Compiler.CompilationModel.SolidityImport
open Compiler.CompilationModel.SolidityImport.Transactions

solidity_profile selfDelegateOsaka where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

-- Imports:
-- * `initDomain(string,string)` and `domainSeparator()`: raw-slot struct `string` + cached EIP-712 separator
-- * `permitWithBytes(address,address,uint,uint256,«bytes calldata»)`: tests `uint`/`bytes calldata` written-type matching
-- * `multicall(«bytes[]»)` and `selfDispatchSingle(bytes)`: generic `address(this).delegatecall(...)` self-dispatch
solidity_import imported from "Contracts/SolidityImportSmoke"
  entry "SelfDelegateAndRawSlotEip712Checks.sol"
  using selfDelegateOsaka
  contract SelfDelegateAndRawSlotEip712Fixture
  function initDomain(string,string)
  function domainSeparator()
  function permitWithBytes(address,address,uint,uint256,«bytes calldata»)
  function multicall(«bytes[]»)
  function selfDispatchSingle(bytes)

#guard imported.report.functions.length == 5
#guard imported.report.functions.all (·.denoteCovered)

-- Denote check: `domainSeparator()` computes a non-zero EIP-712 hash from the raw-slot struct.
private def baseWorld : Verity.ContractState :=
  { Verity.defaultState with
    thisAddress := Verity.Core.Address.ofNat 0x1000
    sender := Verity.Core.Address.ofNat 0x2000
    chainId := Verity.Core.Uint256.ofNat 1 }

#guard
  match runFunction SolidityImport.Differential.oracle imported.model "domainSeparator" baseWorld [] with
  | some [sep] => sep != 0
  | _ => false

-- Denote observations for `YulMemoryDelegateCall`:
-- * Preserves outer `CALLER` (`sender`) and `CALLVALUE` (`msgValue`) on every sub-call.
-- * Commits sub-call storage writes and forwards returned bytes on success.
-- * Bubbles custom-error revert bytes and empty reverts on failure, rolling back earlier writes.
private def selfAddr : Nat := 0x1000
private def outerSender : Nat := 0x2000
private def outerValue : Nat := 7

private def delegateResponse (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if request.kind != .delegatecall || request.target != selfAddr then
    .revert [0xff] []
  else if request.calldata == [0x01] then
    -- Record `(caller, value, counter + 1)` in slots 10, 11, 12 and return `[0xaa, 0xbb, 0xcc]`.
    let count := (world.readSlot 12).val + 1
    let w1 := world.writePhysicalSlot 10 (Verity.Core.Uint256.ofNat request.caller)
    let w2 := w1.writePhysicalSlot 11 (Verity.Core.Uint256.ofNat request.value)
    let w3 := w2.writePhysicalSlot 12 (Verity.Core.Uint256.ofNat count)
    .success w3 [0xaa, 0xbb, 0xcc] [.slot 10, .slot 11, .slot 12]
  else if request.calldata == [0x02] then
    .revert [0xde, 0xad, 0xbe, 0xef] []
  else if request.calldata == [0x03] then
    .revert [] []
  else
    .success world request.calldata []

private def delegateEnv : ByteCallEnvironment :=
  { gas := some 1000000
    adversary := some
      { respond := delegateResponse
        valid := by
          intro request world
          by_cases hstatic : request.kind = .staticcall
          · simp [delegateResponse, hstatic, Response.valid,
              show (Kind.staticcall != Kind.delegatecall) = true from rfl]
          · cases delegateResponse request world <;> simp [Response.valid, hstatic] } }

private def bytesTail (data : List UInt8) : List Nat :=
  data.length :: (List.range ((data.length + 31) / 32)).map fun word =>
    (List.range 32).foldl (fun acc lane => acc * 256 + (data.getD (32 * word + lane) 0).toNat) 0

private def observeDelegate (name : String) (args : List Nat) :
    Option (Bool × List UInt8 × Nat × Nat × Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let tx : DenoteTransaction :=
    { sender := outerSender, thisAddress := selfAddr, msgValue := outerValue,
      functionSelector := 0, args }
  let world := withTransactionContext Verity.defaultState tx
  let bindings ← bindExternalParams 0 fn.bindingParams args
  match executeBody SolidityImport.Differential.oracle (effectiveFields imported.model) world
      bindings fn.body imported.model.errors delegateEnv with
  | .ok r => some (r.success, r.data, (r.world.readSlot 10).val,
      (r.world.readSlot 11).val, (r.world.readSlot 12).val)
  | .error _ => none

-- `selfDispatchSingle` success: returns ABI-encoded bytes `[0xaa, 0xbb, 0xcc]` and observes
-- outer `sender` and `msgValue` (NOT `thisAddress` / `0`).
#guard observeDelegate "selfDispatchSingle" ([32] ++ bytesTail [0x01]) ==
  some (true, wordBytes 32 ++ wordBytes 3 ++ wordBytes (0xaabbcc * 2 ^ 232),
    outerSender, outerValue, 1)

-- `selfDispatchSingle` adversary revert with custom-error payload: bubbles `[0xde, 0xad, 0xbe, 0xef]`.
#guard observeDelegate "selfDispatchSingle" ([32] ++ bytesTail [0x02]) ==
  some (false, [0xde, 0xad, 0xbe, 0xef], 0, 0, 0)

-- `selfDispatchSingle` adversary empty revert: bubbles `[]`.
#guard observeDelegate "selfDispatchSingle" ([32] ++ bytesTail [0x03]) ==
  some (false, [], 0, 0, 0)

-- `multicall` batch of 2 successful sub-calls: commits both writes and preserves outer context.
-- ABI encoding of `bytes[]` with two 1-byte items `[0x01]` and `[0x01]`:
-- head: [offset=32], array: [len=2, off0=64, off1=128, len0=1, w0, len1=1, w1].
#guard observeDelegate "multicall" ([32, 2, 64, 128] ++ bytesTail [0x01] ++ bytesTail [0x01]) ==
  some (true, wordBytes 2, outerSender, outerValue, 2)

-- `multicall` batch where 2nd sub-call reverts with data: bubbles `[0xde, 0xad, 0xbe, 0xef]`
-- and rolls back the 1st sub-call's storage writes.
#guard observeDelegate "multicall" ([32, 2, 64, 128] ++ bytesTail [0x01] ++ bytesTail [0x02]) ==
  some (false, [0xde, 0xad, 0xbe, 0xef], 0, 0, 0)

-- `multicall` batch where 2nd sub-call reverts empty: bubbles `[]` and rolls back.
#guard observeDelegate "multicall" ([32, 2, 64, 128] ++ bytesTail [0x01] ++ bytesTail [0x03]) ==
  some (false, [], 0, 0, 0)

-- Fail-closed control: external `target.delegatecall(payload)` stays rejected.
/--
error: SelfDelegateAndRawSlotEip712Checks.sol:107:28: MemberAccess: [solidity-import:unsupported] external contract calls are outside this slice
closure: SelfDelegateAndRawSlotEip712Fixture.externalDelegateRejected
target.delegatecall
-/
#guard_msgs in
solidity_import externalDelegateForm from "Contracts/SolidityImportSmoke"
  entry "SelfDelegateAndRawSlotEip712Checks.sol"
  using selfDelegateOsaka
  contract SelfDelegateAndRawSlotEip712Fixture
  function externalDelegateRejected(address,bytes)

-- Fail-closed control: `address(this).delegatecall{gas: 50000}(payload)` stays rejected.
/--
error: SelfDelegateAndRawSlotEip712Checks.sol:113:28: FunctionCallOptions: [solidity-import:unsupported] external contract calls are outside this slice
closure: SelfDelegateAndRawSlotEip712Fixture.gassedSelfDelegateRejected
address(this).delegatecall{gas: 50000}
-/
#guard_msgs in
solidity_import gassedSelfDelegateForm from "Contracts/SolidityImportSmoke"
  entry "SelfDelegateAndRawSlotEip712Checks.sol"
  using selfDelegateOsaka
  contract SelfDelegateAndRawSlotEip712Fixture
  function gassedSelfDelegateRejected(bytes)

-- Fail-closed control: storage write after self-delegatecall loop stays rejected by CEI.
/--
error: SelfDelegateAndRawSlotEip712Checks.sol:118:5: FunctionDefinition: [solidity-import:unsupported] storage reads, storage writes and logs after an external CALL are supported only when every external interaction of the function is a closed transport: another interaction follows a CALL that may re-enter this contract
closure: SelfDelegateAndRawSlotEip712Fixture.multicallPostWriteRejected
function multicallPostWriteRejected(bytes[] calldata data) external returns (uint256 executed) {
        for (uint256 i
-/
#guard_msgs in
solidity_import postWriteForm from "Contracts/SolidityImportSmoke"
  entry "SelfDelegateAndRawSlotEip712Checks.sol"
  using selfDelegateOsaka
  contract SelfDelegateAndRawSlotEip712Fixture
  function multicallPostWriteRejected(«bytes[]»)

-- Fail-closed control: `payable` self-delegatecall stays rejected.
/--
error: SelfDelegateAndRawSlotEip712Checks.sol:133:5: FunctionDefinition: [solidity-import:unsupported] payable self-delegatecall is outside this slice
closure: SelfDelegateAndRawSlotEip712Fixture.payableMulticallRejected
function payableMulticallRejected(bytes[] calldata data) external payable returns (uint256 executed) {
        for (uint
-/
#guard_msgs in
solidity_import payableMulticallForm from "Contracts/SolidityImportSmoke"
  entry "SelfDelegateAndRawSlotEip712Checks.sol"
  using selfDelegateOsaka
  contract SelfDelegateAndRawSlotEip712Fixture
  function payableMulticallRejected(«bytes[]»)

end SolidityImportSmoke.SelfDelegateAndRawSlotEip712Checks
