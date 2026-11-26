import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.EncodingScalarUnorderedChecks
open Compiler.CompilationModel Denote

solidity_profile viaIr0834 where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_profile legacy0834 where
  evmVersion := "osaka"
  viaIR := false
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_profile viaIr0838 where
  solc := "0.8.38+commit.1835d247"
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_profile legacy0838 where
  solc := "0.8.38+commit.1835d247"
  evmVersion := "osaka"
  viaIR := false
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import seqViaIr0834 from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedSequence.sol"
  using viaIr0834
  contract SequenceFixture
  function change(uint256)
  function read()

solidity_import seqLegacy0834 from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedSequence.sol"
  using legacy0834
  contract SequenceFixture
  function change(uint256)
  function read()

solidity_import seqViaIr0838 from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedSequence.sol"
  using viaIr0838
  contract SequenceFixture
  function change(uint256)
  function read()

solidity_import seqLegacy0838 from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedSequence.sol"
  using legacy0838
  contract SequenceFixture
  function change(uint256)
  function read()

solidity_import posViaIr0838 from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function calldataStructBeforeInert(NarrowPair,uint256)
  function panicBeforeCalldataStruct(NarrowPair,uint256)
  function unguardedCalldataStructBeforePanic(FullPair,uint256)
  function storageSignatureBeforeInert(uint256)

solidity_import posLegacy0838 from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using legacy0838
  contract EncodingScalarUnorderedOrderRejects
  function calldataStructBeforeInert(NarrowPair,uint256)
  function panicBeforeCalldataStruct(NarrowPair,uint256)
  function unguardedCalldataStructBeforePanic(FullPair,uint256)
  function storageSignatureBeforeInert(uint256)

private def oracle := SolidityImport.Differential.oracle

private def runChange (m : CompilationModel) (x : Nat) :
    Option (Bool × Option (List UInt8) × Nat) := do
  let fn ← m.functions.find? (·.name == "change")
  let r := denoteFunction oracle m fn { sender := 0x1234, functionSelector := 0, args := [x] } Verity.defaultState
  return (r.success, r.revertData, r.finalStorage 0)

-- Branch 0, y = 0 (`x = 0`): `(10 / y) + (y - 1)` panics with 0x12 on via-IR (left first)
-- and 0x11 on legacy (right first), across both solc 0.8.34 and solc 0.8.38.
#guard runChange seqViaIr0834.model 0 == some (false, some (panicBytes 0x12), 0)
#guard runChange seqViaIr0838.model 0 == some (false, some (panicBytes 0x12), 0)
#guard runChange seqLegacy0834.model 0 == some (false, some (panicBytes 0x11), 0)
#guard runChange seqLegacy0838.model 0 == some (false, some (panicBytes 0x11), 0)

-- Branch 1, y = 0: `flag = false` (`x = 1`) skips `10 / y` and panics at `y - 1` (0x11);
-- `flag = true` (`x = 9`) panics at `10 / y` (0x12), on all four profiles.
#guard runChange seqViaIr0834.model 1 == some (false, some (panicBytes 0x11), 0)
#guard runChange seqLegacy0834.model 1 == some (false, some (panicBytes 0x11), 0)
#guard runChange seqViaIr0838.model 1 == some (false, some (panicBytes 0x11), 0)
#guard runChange seqLegacy0838.model 1 == some (false, some (panicBytes 0x11), 0)
#guard runChange seqViaIr0834.model 9 == some (false, some (panicBytes 0x12), 0)
#guard runChange seqLegacy0834.model 9 == some (false, some (panicBytes 0x12), 0)
#guard runChange seqViaIr0838.model 9 == some (false, some (panicBytes 0x12), 0)
#guard runChange seqLegacy0838.model 9 == some (false, some (panicBytes 0x12), 0)

-- Valid inputs (`y = 2`, `x = 32..47`) agree across all four pinned profiles.
#guard (List.range 16).all fun k =>
  let x := 32 + k
  let base := runChange seqViaIr0834.model x
  base.any (·.1) &&
    runChange seqLegacy0834.model x == base &&
    runChange seqViaIr0838.model x == base &&
    runChange seqLegacy0838.model x == base

/--
error: EncodingScalarUnorderedOrderRejects.sol:50:37: Identifier: [solidity-import:unsupported] calldata or enum-storage struct ABI encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.calldataStructBeforePanic
p
-/
#guard_msgs in
solidity_import rejCalldataStruct from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function calldataStructBeforePanic(NarrowPair,uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:54:37: Identifier: [solidity-import:unsupported] calldata or enum-storage struct ABI encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.enumStorageStructBeforePanic
enumStored
-/
#guard_msgs in
solidity_import rejEnumStorageStruct from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function enumStorageStructBeforePanic(uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:58:37: MemberAccess: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.enumStorageMemberInEncode
enumStored.m
-/
#guard_msgs in
solidity_import rejEnumStorageMember from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function enumStorageMemberInEncode(uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:62:50: Identifier: [solidity-import:unsupported] storage bytes/string encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.storageSignatureBeforePanic
sigStored
-/
#guard_msgs in
solidity_import rejStorageSignature from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function storageSignatureBeforePanic(uint256)

end SolidityImportSmoke.EncodingScalarUnorderedChecks
