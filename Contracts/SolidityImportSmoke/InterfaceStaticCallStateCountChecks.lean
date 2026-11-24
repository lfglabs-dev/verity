import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.StaticOracleMocks

/-! A typed interface staticcall lowers the same way whatever the contract's state-variable
count (#2830). Each pair imports two contracts that differ only by one unrelated state
variable and one unused function; every imported body must be identical. Behaviour is checked
against solc 0.8.34 on Anvil (osaka, runs 466), legacy and via-IR: the `WordStaticOracle` mock
(`InterfaceWordStaticCallOracle.sol`, `StaticOracleMocks.wordEnvironment`) is deployed at the
same addresses in both worlds, so the expected words and revert payloads below are the EVM's.
The two pipelines differ only in binary operand order (legacy right-to-left, via-IR
left-to-right), observable when a checked subtraction and a failing call compete. -/

namespace SolidityImportSmoke.InterfaceStaticCallStateCountChecks
open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport

solidity_import oneLegacy from "Contracts/SolidityImportSmoke" entry "InterfaceStaticCallOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract InterfaceStaticCallOneSlot
  function peerQuote(address,address)
  function typedReceiver(IWordFeed,uint256)
  function narrowQuote(address,uint128,int256,bytes4)
  function ownerWord(address)
  function smallWord(address)
  function convertedArgument(address,uint8)
  function returned(address,uint256)
  function leftOperand(address,uint256)
  function rightOperand(address,uint256)
  function compound(address,uint256)
  function mappingTarget(address,uint256)
  function conditional(address,uint256)
  function nestedReceiver(address,uint256)
  function helperReturn(address,uint256)
  function negatedCondition(address,address)
  function equalityRequire(address,uint256)
  function helperArguments(address,uint256)
  function discardedOwner(address)
  function discardedSmall(address)
  function rateWord(address)
  function discardedRate(address)

solidity_import twoLegacy from "Contracts/SolidityImportSmoke" entry "InterfaceStaticCallTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract InterfaceStaticCallTwoSlots
  function peerQuote(address,address)
  function typedReceiver(IWordFeed,uint256)
  function narrowQuote(address,uint128,int256,bytes4)
  function ownerWord(address)
  function smallWord(address)
  function convertedArgument(address,uint8)
  function returned(address,uint256)
  function leftOperand(address,uint256)
  function rightOperand(address,uint256)
  function compound(address,uint256)
  function mappingTarget(address,uint256)
  function conditional(address,uint256)
  function nestedReceiver(address,uint256)
  function helperReturn(address,uint256)
  function negatedCondition(address,address)
  function equalityRequire(address,uint256)
  function helperArguments(address,uint256)
  function discardedOwner(address)
  function discardedSmall(address)
  function rateWord(address)
  function discardedRate(address)

solidity_import oneIr from "Contracts/SolidityImportSmoke" entry "InterfaceStaticCallOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract InterfaceStaticCallOneSlot
  function peerQuote(address,address)
  function typedReceiver(IWordFeed,uint256)
  function narrowQuote(address,uint128,int256,bytes4)
  function ownerWord(address)
  function smallWord(address)
  function convertedArgument(address,uint8)
  function returned(address,uint256)
  function leftOperand(address,uint256)
  function rightOperand(address,uint256)
  function compound(address,uint256)
  function mappingTarget(address,uint256)
  function conditional(address,uint256)
  function nestedReceiver(address,uint256)
  function helperReturn(address,uint256)
  function negatedCondition(address,address)
  function equalityRequire(address,uint256)
  function helperArguments(address,uint256)
  function discardedOwner(address)
  function discardedSmall(address)
  function rateWord(address)
  function discardedRate(address)

solidity_import twoIr from "Contracts/SolidityImportSmoke" entry "InterfaceStaticCallTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract InterfaceStaticCallTwoSlots
  function peerQuote(address,address)
  function typedReceiver(IWordFeed,uint256)
  function narrowQuote(address,uint128,int256,bytes4)
  function ownerWord(address)
  function smallWord(address)
  function convertedArgument(address,uint8)
  function returned(address,uint256)
  function leftOperand(address,uint256)
  function rightOperand(address,uint256)
  function compound(address,uint256)
  function mappingTarget(address,uint256)
  function conditional(address,uint256)
  function nestedReceiver(address,uint256)
  function helperReturn(address,uint256)
  function negatedCondition(address,address)
  function equalityRequire(address,uint256)
  function helperArguments(address,uint256)
  function discardedOwner(address)
  function discardedSmall(address)
  function rateWord(address)
  function discardedRate(address)

/-- Oracle mock that returns 5. -/
private def feedFive : Nat := 0x5fbdb2315678afecb367f032d93f642f64180aa3
/-- Oracle mock that reverts with the word 11. -/
private def feedFail : Nat := 0xe7f1725e7734ce288f8367e1bb143e90bb3f0512
/-- Oracle mock that returns `2^160 + 7`. -/
private def feedDirtyAddr : Nat := 0x9fe46736679d2d9a65f0992f2272de9f3c7fa6e0
/-- Oracle mock that returns `0xabcdef`. -/
private def feedCleanAddr : Nat := 0xcf7ed3acca5a467e9e704c703e8d87f634fb0fc9
/-- Oracle mock that returns 300. -/
private def feedDirtyU8 : Nat := 0xdc64a140aa3e981100a9beca4e685f962f0cf6c9
/-- Oracle mock that returns 2. -/
private def feedBool2 : Nat := 0x5fc8d32690cc91d4c39d9d3abcbd16989f875707
/-- Oracle mock that returns 1. -/
private def feedOne : Nat := 0x0165878a594ca255338adfa4d48449f69242eb8f
/-- Oracle mock that returns the calldata feedFold (selector, length and every argument word). -/
private def feedFold : Nat := 0xa513e6e4b8f2a923d98304ec87f64353c4d5c853
/-- Oracle mock that returns 31 bytes. -/
private def feedShort : Nat := 0x2279b7a0a67db372996a5fab50d91eaa73d2ebe6
/-- Oracle mock that returns the address of `feedFive`. -/
private def feedSelf : Nat := 0x8a791620dd6260079bf849dc5567adc3f2fdc318

/-- Mock accounts as deployed on Anvil: address, value, failure flag, response length, mask. -/
private def oracles : List (Nat × Nat × Nat × Nat × Nat) := [
  (feedFive, 5, 0, 32, 0),
  (feedFail, 11, 1, 32, 0),
  (feedDirtyAddr, 0x10000000000000000000000000000000000000007, 0, 32, 0),
  (feedCleanAddr, 11259375, 0, 32, 0),
  (feedDirtyU8, 300, 0, 32, 0),
  (feedBool2, 2, 0, 32, 0),
  (feedOne, 1, 0, 32, 0),
  (feedFold, 0, 0, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
  (feedShort, 5, 0, 31, 0),
  (feedSelf, 0x5fbdb2315678afecb367f032d93f642f64180aa3, 0, 32, 0)
]

/-- The code-less account of the campaign. -/
private def emptyAccount : Nat := 0x77

private def world : Verity.ContractState :=
  Verity.defaultState.withStorageWords fun key =>
    match key with
    | .contractSlot owner slot =>
        match oracles.find? (·.1 == owner) with
        | some (_, value, failed, length, mask) =>
            Verity.Core.Uint256.ofNat ([value, failed, length, mask].getD slot 0)
        | none => 0
    | _ => 0

private def calls : Denote.ByteCallEnvironment :=
  StaticOracleMocks.wordEnvironment (oracles.map (·.1)) 30000000 [emptyAccount]

private def body (model : CompilationModel) (name : String) : String :=
  match model.functions.find? (·.name == name) with
  | some f => (repr f.body).pretty 100000
  | none => ""

/-- The function imports and its body does not depend on the unrelated slot. -/
private def sameBody (one two : CompilationModel) (name : String) : Bool :=
  body one name != "" && body one name == body two name

/-- Expected outcome on Anvil: `.ok word` or `.revert payload` (hex, no `0x`). -/
private inductive Outcome where
  | ok (word : Nat)
  | revert (data : String)

private def hexBytes (hex : String) : List UInt8 :=
  let digits := hex.toList.filterMap Compiler.Hex.hexCharToNat?
  (List.range (digits.length / 2)).map fun i =>
    UInt8.ofNat (digits.getD (2 * i) 0 * 16 + digits.getD (2 * i + 1) 0)

private def outcome (model : CompilationModel) (name : String) (args : List Nat) :
    Option (Bool × Nat × List UInt8) :=
  (model.functions.find? (·.name == name)).map fun f =>
    let r := Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args } world (byteCalls := calls)
    let word := match r.returnWords, r.returnValue with
      | [w], _ => w
      | [], some w => w
      | _, _ => 2 ^ 256
    (r.success, word, r.revertData.getD [0xff, 0xff])

private def agrees (model : CompilationModel) (name : String) :
    List Nat × Outcome → Bool
  | (args, .ok w) => match outcome model name args with
      | some (true, v, _) => v == w
      | _ => false
  | (args, .revert d) => match outcome model name args with
      | some (false, _, e) => e == hexBytes d
      | _ => false

#guard sameBody oneLegacy.model twoLegacy.model "peerQuote"
#guard sameBody oneIr.model twoIr.model "peerQuote"
#guard sameBody oneLegacy.model twoLegacy.model "typedReceiver"
#guard sameBody oneIr.model twoIr.model "typedReceiver"
#guard sameBody oneLegacy.model twoLegacy.model "narrowQuote"
#guard sameBody oneIr.model twoIr.model "narrowQuote"
#guard sameBody oneLegacy.model twoLegacy.model "ownerWord"
#guard sameBody oneIr.model twoIr.model "ownerWord"
#guard sameBody oneLegacy.model twoLegacy.model "smallWord"
#guard sameBody oneIr.model twoIr.model "smallWord"
#guard sameBody oneLegacy.model twoLegacy.model "convertedArgument"
#guard sameBody oneIr.model twoIr.model "convertedArgument"
#guard sameBody oneLegacy.model twoLegacy.model "returned"
#guard sameBody oneIr.model twoIr.model "returned"
#guard sameBody oneLegacy.model twoLegacy.model "leftOperand"
#guard sameBody oneIr.model twoIr.model "leftOperand"
#guard sameBody oneLegacy.model twoLegacy.model "rightOperand"
#guard sameBody oneIr.model twoIr.model "rightOperand"
#guard sameBody oneLegacy.model twoLegacy.model "compound"
#guard sameBody oneIr.model twoIr.model "compound"
#guard sameBody oneLegacy.model twoLegacy.model "mappingTarget"
#guard sameBody oneIr.model twoIr.model "mappingTarget"
#guard sameBody oneLegacy.model twoLegacy.model "conditional"
#guard sameBody oneIr.model twoIr.model "conditional"
#guard sameBody oneLegacy.model twoLegacy.model "nestedReceiver"
#guard sameBody oneIr.model twoIr.model "nestedReceiver"
#guard sameBody oneLegacy.model twoLegacy.model "helperReturn"
#guard sameBody oneIr.model twoIr.model "helperReturn"
#guard sameBody oneLegacy.model twoLegacy.model "negatedCondition"
#guard sameBody oneIr.model twoIr.model "negatedCondition"
#guard sameBody oneLegacy.model twoLegacy.model "equalityRequire"
#guard sameBody oneIr.model twoIr.model "equalityRequire"
#guard sameBody oneLegacy.model twoLegacy.model "helperArguments"
#guard sameBody oneIr.model twoIr.model "helperArguments"
#guard sameBody oneLegacy.model twoLegacy.model "discardedOwner"
#guard sameBody oneIr.model twoIr.model "discardedOwner"
#guard sameBody oneLegacy.model twoLegacy.model "discardedSmall"
#guard sameBody oneIr.model twoIr.model "discardedSmall"
#guard sameBody oneLegacy.model twoLegacy.model "rateWord"
#guard sameBody oneIr.model twoIr.model "rateWord"
#guard sameBody oneLegacy.model twoLegacy.model "discardedRate"
#guard sameBody oneIr.model twoIr.model "discardedRate"

/-- `peerQuote` on Anvil, legacy. -/
private def peerQuoteLegacy : List (List Nat × Outcome) := [
  ([feedFive, feedOne], .ok 5),
  ([feedFail, feedOne], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, feedOne], .ok 0x165878a594ca255338adfa4d4844a0d2950e7d8),
  ([feedShort, feedOne], .revert ""),
  ([emptyAccount, feedOne], .revert "")]
#guard !peerQuoteLegacy.isEmpty && peerQuoteLegacy.all (agrees oneLegacy.model "peerQuote")
#guard !peerQuoteLegacy.isEmpty && peerQuoteLegacy.all (agrees twoLegacy.model "peerQuote")

/-- `typedReceiver` on Anvil, legacy. -/
private def typedReceiverLegacy : List (List Nat × Outcome) := [
  ([feedFive, 9], .ok 5),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 9], .ok 123318803777),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 9], .revert "")]
#guard !typedReceiverLegacy.isEmpty && typedReceiverLegacy.all (agrees oneLegacy.model "typedReceiver")
#guard !typedReceiverLegacy.isEmpty && typedReceiverLegacy.all (agrees twoLegacy.model "typedReceiver")

/-- `narrowQuote` on Anvil, legacy. -/
private def narrowQuoteLegacy : List (List Nat × Outcome) := [
  ([feedFive, 77, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x1234567800000000000000000000000000000000000000000000000000000000], .ok 5),
  ([feedFail, 77, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x1234567800000000000000000000000000000000000000000000000000000000], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 77, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x1234567800000000000000000000000000000000000000000000000000000000], .ok 0x1234567800000000000000000000000000000000000000000000486e8e073b10),
  ([feedShort, 77, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x1234567800000000000000000000000000000000000000000000000000000000], .revert ""),
  ([emptyAccount, 77, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x1234567800000000000000000000000000000000000000000000000000000000], .revert "")]
#guard !narrowQuoteLegacy.isEmpty && narrowQuoteLegacy.all (agrees oneLegacy.model "narrowQuote")
#guard !narrowQuoteLegacy.isEmpty && narrowQuoteLegacy.all (agrees twoLegacy.model "narrowQuote")

/-- `ownerWord` on Anvil, legacy. -/
private def ownerWordLegacy : List (List Nat × Outcome) := [
  ([feedDirtyAddr], .revert ""),
  ([feedCleanAddr], .ok 11259375),
  ([feedDirtyU8], .ok 300),
  ([feedFive], .ok 5),
  ([feedFail], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedShort], .revert ""),
  ([emptyAccount], .revert "")]
#guard !ownerWordLegacy.isEmpty && ownerWordLegacy.all (agrees oneLegacy.model "ownerWord")
#guard !ownerWordLegacy.isEmpty && ownerWordLegacy.all (agrees twoLegacy.model "ownerWord")

/-- `smallWord` on Anvil, legacy. -/
private def smallWordLegacy : List (List Nat × Outcome) := [
  ([feedDirtyAddr], .revert ""),
  ([feedCleanAddr], .revert ""),
  ([feedDirtyU8], .revert ""),
  ([feedFive], .ok 5),
  ([feedFail], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedShort], .revert ""),
  ([emptyAccount], .revert "")]
#guard !smallWordLegacy.isEmpty && smallWordLegacy.all (agrees oneLegacy.model "smallWord")
#guard !smallWordLegacy.isEmpty && smallWordLegacy.all (agrees twoLegacy.model "smallWord")

/-- `convertedArgument` on Anvil, legacy. -/
private def convertedArgumentLegacy : List (List Nat × Outcome) := [
  ([feedFive, 200], .ok 5),
  ([feedFail, 200], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 200], .ok 123318803968),
  ([feedShort, 200], .revert ""),
  ([emptyAccount, 200], .revert "")]
#guard !convertedArgumentLegacy.isEmpty && convertedArgumentLegacy.all (agrees oneLegacy.model "convertedArgument")
#guard !convertedArgumentLegacy.isEmpty && convertedArgumentLegacy.all (agrees twoLegacy.model "convertedArgument")

/-- `returned` on Anvil, legacy. -/
private def returnedLegacy : List (List Nat × Outcome) := [
  ([feedFive, 9], .ok 5),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 9], .ok 123318803777),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 9], .revert "")]
#guard !returnedLegacy.isEmpty && returnedLegacy.all (agrees oneLegacy.model "returned")
#guard !returnedLegacy.isEmpty && returnedLegacy.all (agrees twoLegacy.model "returned")

/-- `leftOperand` on Anvil, legacy. -/
private def leftOperandLegacy : List (List Nat × Outcome) := [
  ([feedFive, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFive, 9], .ok 13),
  ([feedFail, 0], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFold, 9], .ok 123318803785),
  ([feedShort, 0], .revert ""),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 0], .revert ""),
  ([emptyAccount, 9], .revert "")]
#guard !leftOperandLegacy.isEmpty && leftOperandLegacy.all (agrees oneLegacy.model "leftOperand")
#guard !leftOperandLegacy.isEmpty && leftOperandLegacy.all (agrees twoLegacy.model "leftOperand")

/-- `rightOperand` on Anvil, legacy. -/
private def rightOperandLegacy : List (List Nat × Outcome) := [
  ([feedFive, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFive, 9], .ok 13),
  ([feedFail, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFold, 9], .ok 123318803785),
  ([feedShort, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([emptyAccount, 9], .revert "")]
#guard !rightOperandLegacy.isEmpty && rightOperandLegacy.all (agrees oneLegacy.model "rightOperand")
#guard !rightOperandLegacy.isEmpty && rightOperandLegacy.all (agrees twoLegacy.model "rightOperand")

/-- `compound` on Anvil, legacy. -/
private def compoundLegacy : List (List Nat × Outcome) := [
  ([feedFive, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFive, 3], .ok 8),
  ([feedFail, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFail, 3], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFold, 3], .ok 123318803774),
  ([feedShort, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff], .revert ""),
  ([feedShort, 3], .revert ""),
  ([emptyAccount, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff], .revert ""),
  ([emptyAccount, 3], .revert "")]
#guard !compoundLegacy.isEmpty && compoundLegacy.all (agrees oneLegacy.model "compound")
#guard !compoundLegacy.isEmpty && compoundLegacy.all (agrees twoLegacy.model "compound")

/-- `mappingTarget` on Anvil, legacy. -/
private def mappingTargetLegacy : List (List Nat × Outcome) := [
  ([feedFive, 0], .ok 5),
  ([feedFive, 9], .ok 5),
  ([feedFail, 0], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0], .ok 123318803768),
  ([feedFold, 9], .ok 123318803777),
  ([feedShort, 0], .revert ""),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 0], .revert ""),
  ([emptyAccount, 9], .revert "")]
#guard !mappingTargetLegacy.isEmpty && mappingTargetLegacy.all (agrees oneLegacy.model "mappingTarget")
#guard !mappingTargetLegacy.isEmpty && mappingTargetLegacy.all (agrees twoLegacy.model "mappingTarget")

/-- `conditional` on Anvil, legacy. -/
private def conditionalLegacy : List (List Nat × Outcome) := [
  ([feedFive, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFive, 9], .ok 5),
  ([feedFail, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFold, 9], .ok 123318803777),
  ([feedShort, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([emptyAccount, 9], .revert "")]
#guard !conditionalLegacy.isEmpty && conditionalLegacy.all (agrees oneLegacy.model "conditional")
#guard !conditionalLegacy.isEmpty && conditionalLegacy.all (agrees twoLegacy.model "conditional")

/-- `nestedReceiver` on Anvil, legacy. -/
private def nestedReceiverLegacy : List (List Nat × Outcome) := [
  ([feedSelf, 9], .ok 5)]
#guard !nestedReceiverLegacy.isEmpty && nestedReceiverLegacy.all (agrees oneLegacy.model "nestedReceiver")
#guard !nestedReceiverLegacy.isEmpty && nestedReceiverLegacy.all (agrees twoLegacy.model "nestedReceiver")

/-- `helperReturn` on Anvil, legacy. -/
private def helperReturnLegacy : List (List Nat × Outcome) := [
  ([feedFive, 9], .ok 5),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 9], .ok 123318803777),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 9], .revert "")]
#guard !helperReturnLegacy.isEmpty && helperReturnLegacy.all (agrees oneLegacy.model "helperReturn")
#guard !helperReturnLegacy.isEmpty && helperReturnLegacy.all (agrees twoLegacy.model "helperReturn")

/-- `negatedCondition` on Anvil, legacy. -/
private def negatedConditionLegacy : List (List Nat × Outcome) := [
  ([feedFive, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert ""),
  ([feedFail, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert ""),
  ([feedShort, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert ""),
  ([emptyAccount, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert ""),
  ([feedBool2, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert ""),
  ([feedOne, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .ok 1),
  ([feedFive, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert "")]
#guard !negatedConditionLegacy.isEmpty && negatedConditionLegacy.all (agrees oneLegacy.model "negatedCondition")
#guard !negatedConditionLegacy.isEmpty && negatedConditionLegacy.all (agrees twoLegacy.model "negatedCondition")

/-- `equalityRequire` on Anvil, legacy. -/
private def equalityRequireLegacy : List (List Nat × Outcome) := [
  ([feedFive, 0], .ok 0),
  ([feedFive, 9], .ok 9),
  ([feedFail, 0], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0], .revert "08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000571756f7465000000000000000000000000000000000000000000000000000000"),
  ([feedFold, 9], .revert "08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000571756f7465000000000000000000000000000000000000000000000000000000"),
  ([feedShort, 0], .revert ""),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 0], .revert ""),
  ([emptyAccount, 9], .revert "")]
#guard !equalityRequireLegacy.isEmpty && equalityRequireLegacy.all (agrees oneLegacy.model "equalityRequire")
#guard !equalityRequireLegacy.isEmpty && equalityRequireLegacy.all (agrees twoLegacy.model "equalityRequire")

/-- `helperArguments` on Anvil, legacy. -/
private def helperArgumentsLegacy : List (List Nat × Outcome) := [
  ([feedFive, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFive, 9], .ok 13),
  ([feedFail, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFold, 9], .ok 123318803785),
  ([feedShort, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([emptyAccount, 9], .revert "")]
#guard !helperArgumentsLegacy.isEmpty && helperArgumentsLegacy.all (agrees oneLegacy.model "helperArguments")
#guard !helperArgumentsLegacy.isEmpty && helperArgumentsLegacy.all (agrees twoLegacy.model "helperArguments")

/-- `discardedOwner` on Anvil, legacy. -/
private def discardedOwnerLegacy : List (List Nat × Outcome) := [
  ([feedDirtyAddr], .revert ""),
  ([feedCleanAddr], .ok 1),
  ([feedDirtyU8], .ok 1),
  ([feedFive], .ok 1),
  ([feedFail], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedShort], .revert ""),
  ([emptyAccount], .revert "")]
#guard !discardedOwnerLegacy.isEmpty && discardedOwnerLegacy.all (agrees oneLegacy.model "discardedOwner")
#guard !discardedOwnerLegacy.isEmpty && discardedOwnerLegacy.all (agrees twoLegacy.model "discardedOwner")

/-- `discardedSmall` on Anvil, legacy. -/
private def discardedSmallLegacy : List (List Nat × Outcome) := [
  ([feedDirtyAddr], .revert ""),
  ([feedCleanAddr], .revert ""),
  ([feedDirtyU8], .revert ""),
  ([feedFive], .ok 1),
  ([feedFail], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedShort], .revert ""),
  ([emptyAccount], .revert "")]
#guard !discardedSmallLegacy.isEmpty && discardedSmallLegacy.all (agrees oneLegacy.model "discardedSmall")
#guard !discardedSmallLegacy.isEmpty && discardedSmallLegacy.all (agrees twoLegacy.model "discardedSmall")

/-- `rateWord` (`uint16` return, #2914) on Anvil, legacy: a word of `2^16` or more reverts
with no data, so `300` is clean and `0xabcdef` is not. -/
private def rateWordLegacy : List (List Nat × Outcome) := [
  ([feedDirtyAddr], .revert ""),
  ([feedCleanAddr], .revert ""),
  ([feedDirtyU8], .ok 300),
  ([feedFive], .ok 5),
  ([feedFail], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedShort], .revert ""),
  ([emptyAccount], .revert "")]
#guard !rateWordLegacy.isEmpty && rateWordLegacy.all (agrees oneLegacy.model "rateWord")
#guard !rateWordLegacy.isEmpty && rateWordLegacy.all (agrees twoLegacy.model "rateWord")

/-- `discardedRate` on Anvil, legacy: the discarded `uint16` word is still validated. -/
private def discardedRateLegacy : List (List Nat × Outcome) := [
  ([feedDirtyAddr], .revert ""),
  ([feedCleanAddr], .revert ""),
  ([feedDirtyU8], .ok 1),
  ([feedFive], .ok 1),
  ([feedFail], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedShort], .revert ""),
  ([emptyAccount], .revert "")]
#guard !discardedRateLegacy.isEmpty && discardedRateLegacy.all (agrees oneLegacy.model "discardedRate")
#guard !discardedRateLegacy.isEmpty && discardedRateLegacy.all (agrees twoLegacy.model "discardedRate")

/-- `peerQuote` on Anvil, ir. -/
private def peerQuoteIr : List (List Nat × Outcome) := [
  ([feedFive, feedOne], .ok 5),
  ([feedFail, feedOne], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, feedOne], .ok 0x165878a594ca255338adfa4d4844a0d2950e7d8),
  ([feedShort, feedOne], .revert ""),
  ([emptyAccount, feedOne], .revert "")]
#guard !peerQuoteIr.isEmpty && peerQuoteIr.all (agrees oneIr.model "peerQuote")
#guard !peerQuoteIr.isEmpty && peerQuoteIr.all (agrees twoIr.model "peerQuote")

/-- `typedReceiver` on Anvil, ir. -/
private def typedReceiverIr : List (List Nat × Outcome) := [
  ([feedFive, 9], .ok 5),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 9], .ok 123318803777),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 9], .revert "")]
#guard !typedReceiverIr.isEmpty && typedReceiverIr.all (agrees oneIr.model "typedReceiver")
#guard !typedReceiverIr.isEmpty && typedReceiverIr.all (agrees twoIr.model "typedReceiver")

/-- `narrowQuote` on Anvil, ir. -/
private def narrowQuoteIr : List (List Nat × Outcome) := [
  ([feedFive, 77, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x1234567800000000000000000000000000000000000000000000000000000000], .ok 5),
  ([feedFail, 77, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x1234567800000000000000000000000000000000000000000000000000000000], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 77, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x1234567800000000000000000000000000000000000000000000000000000000], .ok 0x1234567800000000000000000000000000000000000000000000486e8e073b10),
  ([feedShort, 77, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x1234567800000000000000000000000000000000000000000000000000000000], .revert ""),
  ([emptyAccount, 77, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd, 0x1234567800000000000000000000000000000000000000000000000000000000], .revert "")]
#guard !narrowQuoteIr.isEmpty && narrowQuoteIr.all (agrees oneIr.model "narrowQuote")
#guard !narrowQuoteIr.isEmpty && narrowQuoteIr.all (agrees twoIr.model "narrowQuote")

/-- `ownerWord` on Anvil, ir. -/
private def ownerWordIr : List (List Nat × Outcome) := [
  ([feedDirtyAddr], .revert ""),
  ([feedCleanAddr], .ok 11259375),
  ([feedDirtyU8], .ok 300),
  ([feedFive], .ok 5),
  ([feedFail], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedShort], .revert ""),
  ([emptyAccount], .revert "")]
#guard !ownerWordIr.isEmpty && ownerWordIr.all (agrees oneIr.model "ownerWord")
#guard !ownerWordIr.isEmpty && ownerWordIr.all (agrees twoIr.model "ownerWord")

/-- `smallWord` on Anvil, ir. -/
private def smallWordIr : List (List Nat × Outcome) := [
  ([feedDirtyAddr], .revert ""),
  ([feedCleanAddr], .revert ""),
  ([feedDirtyU8], .revert ""),
  ([feedFive], .ok 5),
  ([feedFail], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedShort], .revert ""),
  ([emptyAccount], .revert "")]
#guard !smallWordIr.isEmpty && smallWordIr.all (agrees oneIr.model "smallWord")
#guard !smallWordIr.isEmpty && smallWordIr.all (agrees twoIr.model "smallWord")

/-- `convertedArgument` on Anvil, ir. -/
private def convertedArgumentIr : List (List Nat × Outcome) := [
  ([feedFive, 200], .ok 5),
  ([feedFail, 200], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 200], .ok 123318803968),
  ([feedShort, 200], .revert ""),
  ([emptyAccount, 200], .revert "")]
#guard !convertedArgumentIr.isEmpty && convertedArgumentIr.all (agrees oneIr.model "convertedArgument")
#guard !convertedArgumentIr.isEmpty && convertedArgumentIr.all (agrees twoIr.model "convertedArgument")

/-- `returned` on Anvil, ir. -/
private def returnedIr : List (List Nat × Outcome) := [
  ([feedFive, 9], .ok 5),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 9], .ok 123318803777),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 9], .revert "")]
#guard !returnedIr.isEmpty && returnedIr.all (agrees oneIr.model "returned")
#guard !returnedIr.isEmpty && returnedIr.all (agrees twoIr.model "returned")

/-- `leftOperand` on Anvil, ir. -/
private def leftOperandIr : List (List Nat × Outcome) := [
  ([feedFive, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFive, 9], .ok 13),
  ([feedFail, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFold, 9], .ok 123318803785),
  ([feedShort, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([emptyAccount, 9], .revert "")]
#guard !leftOperandIr.isEmpty && leftOperandIr.all (agrees oneIr.model "leftOperand")
#guard !leftOperandIr.isEmpty && leftOperandIr.all (agrees twoIr.model "leftOperand")

/-- `rightOperand` on Anvil, ir. -/
private def rightOperandIr : List (List Nat × Outcome) := [
  ([feedFive, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFive, 9], .ok 13),
  ([feedFail, 0], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFold, 9], .ok 123318803785),
  ([feedShort, 0], .revert ""),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 0], .revert ""),
  ([emptyAccount, 9], .revert "")]
#guard !rightOperandIr.isEmpty && rightOperandIr.all (agrees oneIr.model "rightOperand")
#guard !rightOperandIr.isEmpty && rightOperandIr.all (agrees twoIr.model "rightOperand")

/-- `compound` on Anvil, ir. -/
private def compoundIr : List (List Nat × Outcome) := [
  ([feedFive, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFive, 3], .ok 8),
  ([feedFail, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFail, 3], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFold, 3], .ok 123318803774),
  ([feedShort, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff], .revert ""),
  ([feedShort, 3], .revert ""),
  ([emptyAccount, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff], .revert ""),
  ([emptyAccount, 3], .revert "")]
#guard !compoundIr.isEmpty && compoundIr.all (agrees oneIr.model "compound")
#guard !compoundIr.isEmpty && compoundIr.all (agrees twoIr.model "compound")

/-- `mappingTarget` on Anvil, ir. -/
private def mappingTargetIr : List (List Nat × Outcome) := [
  ([feedFive, 0], .ok 5),
  ([feedFive, 9], .ok 5),
  ([feedFail, 0], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0], .ok 123318803768),
  ([feedFold, 9], .ok 123318803777),
  ([feedShort, 0], .revert ""),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 0], .revert ""),
  ([emptyAccount, 9], .revert "")]
#guard !mappingTargetIr.isEmpty && mappingTargetIr.all (agrees oneIr.model "mappingTarget")
#guard !mappingTargetIr.isEmpty && mappingTargetIr.all (agrees twoIr.model "mappingTarget")

/-- `conditional` on Anvil, ir. -/
private def conditionalIr : List (List Nat × Outcome) := [
  ([feedFive, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFive, 9], .ok 5),
  ([feedFail, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFold, 9], .ok 123318803777),
  ([feedShort, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([emptyAccount, 9], .revert "")]
#guard !conditionalIr.isEmpty && conditionalIr.all (agrees oneIr.model "conditional")
#guard !conditionalIr.isEmpty && conditionalIr.all (agrees twoIr.model "conditional")

/-- `nestedReceiver` on Anvil, ir. -/
private def nestedReceiverIr : List (List Nat × Outcome) := [
  ([feedSelf, 9], .ok 5)]
#guard !nestedReceiverIr.isEmpty && nestedReceiverIr.all (agrees oneIr.model "nestedReceiver")
#guard !nestedReceiverIr.isEmpty && nestedReceiverIr.all (agrees twoIr.model "nestedReceiver")

/-- `helperReturn` on Anvil, ir. -/
private def helperReturnIr : List (List Nat × Outcome) := [
  ([feedFive, 9], .ok 5),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 9], .ok 123318803777),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 9], .revert "")]
#guard !helperReturnIr.isEmpty && helperReturnIr.all (agrees oneIr.model "helperReturn")
#guard !helperReturnIr.isEmpty && helperReturnIr.all (agrees twoIr.model "helperReturn")

/-- `negatedCondition` on Anvil, ir. -/
private def negatedConditionIr : List (List Nat × Outcome) := [
  ([feedFive, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert ""),
  ([feedFail, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert ""),
  ([feedShort, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert ""),
  ([emptyAccount, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert ""),
  ([feedBool2, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert ""),
  ([feedOne, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .ok 1),
  ([feedFive, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266], .revert "")]
#guard !negatedConditionIr.isEmpty && negatedConditionIr.all (agrees oneIr.model "negatedCondition")
#guard !negatedConditionIr.isEmpty && negatedConditionIr.all (agrees twoIr.model "negatedCondition")

/-- `equalityRequire` on Anvil, ir. -/
private def equalityRequireIr : List (List Nat × Outcome) := [
  ([feedFive, 0], .ok 0),
  ([feedFive, 9], .ok 9),
  ([feedFail, 0], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0], .revert "08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000571756f7465000000000000000000000000000000000000000000000000000000"),
  ([feedFold, 9], .revert "08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000571756f7465000000000000000000000000000000000000000000000000000000"),
  ([feedShort, 0], .revert ""),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 0], .revert ""),
  ([emptyAccount, 9], .revert "")]
#guard !equalityRequireIr.isEmpty && equalityRequireIr.all (agrees oneIr.model "equalityRequire")
#guard !equalityRequireIr.isEmpty && equalityRequireIr.all (agrees twoIr.model "equalityRequire")

/-- `helperArguments` on Anvil, ir. -/
private def helperArgumentsIr : List (List Nat × Outcome) := [
  ([feedFive, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFive, 9], .ok 13),
  ([feedFail, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFail, 9], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedFold, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedFold, 9], .ok 123318803785),
  ([feedShort, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([feedShort, 9], .revert ""),
  ([emptyAccount, 0], .revert "4e487b710000000000000000000000000000000000000000000000000000000000000011"),
  ([emptyAccount, 9], .revert "")]
#guard !helperArgumentsIr.isEmpty && helperArgumentsIr.all (agrees oneIr.model "helperArguments")
#guard !helperArgumentsIr.isEmpty && helperArgumentsIr.all (agrees twoIr.model "helperArguments")

/-- `discardedOwner` on Anvil, ir. -/
private def discardedOwnerIr : List (List Nat × Outcome) := [
  ([feedDirtyAddr], .revert ""),
  ([feedCleanAddr], .ok 1),
  ([feedDirtyU8], .ok 1),
  ([feedFive], .ok 1),
  ([feedFail], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedShort], .revert ""),
  ([emptyAccount], .revert "")]
#guard !discardedOwnerIr.isEmpty && discardedOwnerIr.all (agrees oneIr.model "discardedOwner")
#guard !discardedOwnerIr.isEmpty && discardedOwnerIr.all (agrees twoIr.model "discardedOwner")

/-- `discardedSmall` on Anvil, ir. -/
private def discardedSmallIr : List (List Nat × Outcome) := [
  ([feedDirtyAddr], .revert ""),
  ([feedCleanAddr], .revert ""),
  ([feedDirtyU8], .revert ""),
  ([feedFive], .ok 1),
  ([feedFail], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedShort], .revert ""),
  ([emptyAccount], .revert "")]
#guard !discardedSmallIr.isEmpty && discardedSmallIr.all (agrees oneIr.model "discardedSmall")
#guard !discardedSmallIr.isEmpty && discardedSmallIr.all (agrees twoIr.model "discardedSmall")

/-- `rateWord` (`uint16` return, #2914) on Anvil, ir: a word of `2^16` or more reverts
with no data, so `300` is clean and `0xabcdef` is not. -/
private def rateWordIr : List (List Nat × Outcome) := [
  ([feedDirtyAddr], .revert ""),
  ([feedCleanAddr], .revert ""),
  ([feedDirtyU8], .ok 300),
  ([feedFive], .ok 5),
  ([feedFail], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedShort], .revert ""),
  ([emptyAccount], .revert "")]
#guard !rateWordIr.isEmpty && rateWordIr.all (agrees oneIr.model "rateWord")
#guard !rateWordIr.isEmpty && rateWordIr.all (agrees twoIr.model "rateWord")

/-- `discardedRate` on Anvil, ir: the discarded `uint16` word is still validated. -/
private def discardedRateIr : List (List Nat × Outcome) := [
  ([feedDirtyAddr], .revert ""),
  ([feedCleanAddr], .revert ""),
  ([feedDirtyU8], .ok 1),
  ([feedFive], .ok 1),
  ([feedFail], .revert "000000000000000000000000000000000000000000000000000000000000000b"),
  ([feedShort], .revert ""),
  ([emptyAccount], .revert "")]
#guard !discardedRateIr.isEmpty && discardedRateIr.all (agrees oneIr.model "discardedRate")
#guard !discardedRateIr.isEmpty && discardedRateIr.all (agrees twoIr.model "discardedRate")

end SolidityImportSmoke.InterfaceStaticCallStateCountChecks
