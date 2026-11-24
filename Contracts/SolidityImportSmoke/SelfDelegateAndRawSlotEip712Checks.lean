import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.SelfDelegateAndRawSlotEip712Checks

open Compiler.CompilationModel
open Compiler.CompilationModel.SolidityImport

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

-- Post-CALL state access (6e): a storage write after a closed self-delegatecall loop is
-- admitted when every interaction is a closed transport, tagged `solidity_post_call_state_access`.
solidity_import postWriteForm from "Contracts/SolidityImportSmoke"
  entry "SelfDelegateAndRawSlotEip712Checks.sol"
  using selfDelegateOsaka
  contract SelfDelegateAndRawSlotEip712Fixture
  function multicallPostWriteRejected(«bytes[]»)

#guard
  match postWriteForm.model.functions.find? (·.name == "multicallPostWriteRejected") with
  | some f =>
      f.allowPostInteractionWrites && f.reentrancyTrusted &&
        (f.localObligations.map (·.name)).contains "solidity_post_call_state_access"
  | none => false

end SolidityImportSmoke.SelfDelegateAndRawSlotEip712Checks
