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
  function calldataStructBeforeCalldataMember(NarrowPair,NarrowPair)
  function storageArrayBeforeInert(uint256)

solidity_import posLegacy0838 from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using legacy0838
  contract EncodingScalarUnorderedOrderRejects
  function calldataStructBeforeInert(NarrowPair,uint256)
  function panicBeforeCalldataStruct(NarrowPair,uint256)
  function unguardedCalldataStructBeforePanic(FullPair,uint256)
  function storageSignatureBeforeInert(uint256)
  function calldataStructBeforeCalldataMember(NarrowPair,NarrowPair)
  function storageArrayBeforeInert(uint256)

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

-- Branches 2..6, y = 0 (`x = 2..6` with `flag = false`, `x = 10..14` with `flag = true`):
-- competing sibling panics (`10 / y` before `y - 1`) always hit `Panic(0x12)` first across
-- dynamic `abi.encode`, dynamic `emit`, `abi.encodePacked`, `bytes.concat`,
-- `abi.encodeWithSelector` (static & dynamic), `abi.encodeWithSignature` (static & dynamic),
-- and `abi.encodeCall` (static & dynamic) on all four pinned profiles.
#guard [2, 3, 4, 5, 6, 10, 11, 12, 13, 14].all fun x =>
  runChange seqViaIr0834.model x == some (false, some (panicBytes 0x12), 0) &&
  runChange seqLegacy0834.model x == some (false, some (panicBytes 0x12), 0) &&
  runChange seqViaIr0838.model x == some (false, some (panicBytes 0x12), 0) &&
  runChange seqLegacy0838.model x == some (false, some (panicBytes 0x12), 0)

-- Valid inputs (`y = 2`, `x = 32..47`) agree across all four pinned profiles.
#guard (List.range 16).all fun k =>
  let x := 32 + k
  let base := runChange seqViaIr0834.model x
  base.any (·.1) &&
    runChange seqLegacy0834.model x == base &&
    runChange seqViaIr0838.model x == base &&
    runChange seqLegacy0838.model x == base

/--
error: EncodingScalarUnorderedOrderRejects.sol:51:37: Identifier: [solidity-import:unsupported] calldata or enum-storage struct ABI encoding argument before a sibling that can revert or write is unsupported
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
error: EncodingScalarUnorderedOrderRejects.sol:55:37: Identifier: [solidity-import:unsupported] calldata or enum-storage struct ABI encoding argument before a sibling that can revert or write is unsupported
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
error: EncodingScalarUnorderedOrderRejects.sol:59:37: MemberAccess: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
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
error: EncodingScalarUnorderedOrderRejects.sol:63:50: Identifier: [solidity-import:unsupported] storage bytes/string encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.storageSignatureBeforePanic
sigStored
-/
#guard_msgs in
solidity_import rejStorageSignature from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function storageSignatureBeforePanic(uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:67:37: Identifier: [solidity-import:unsupported] calldata or enum-storage struct ABI encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.enumStorageStructBeforeCalldataMember
enumStored
-/
#guard_msgs in
solidity_import rejEnumStorageBeforeCalldataMember from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function enumStorageStructBeforeCalldataMember(NarrowPair)

/--
error: EncodingScalarUnorderedOrderRejects.sol:71:50: Identifier: [solidity-import:unsupported] storage bytes/string encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.storageSignatureBeforeCalldataMember
sigStored
-/
#guard_msgs in
solidity_import rejStorageSigBeforeCalldataMember from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function storageSignatureBeforeCalldataMember(NarrowPair)

/--
error: EncodingScalarUnorderedOrderRejects.sol:75:50: Identifier: [solidity-import:unsupported] storage bytes/string encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.storageSignatureBeforeCalldataStruct
sigStored
-/
#guard_msgs in
solidity_import rejStorageSigBeforeCalldataStruct from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using legacy0838
  contract EncodingScalarUnorderedOrderRejects
  function storageSignatureBeforeCalldataStruct(NarrowPair)

/--
error: EncodingScalarUnorderedOrderRejects.sol:79:50: Identifier: [solidity-import:unsupported] storage bytes/string encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.storageSignatureBeforeEnumStorageStruct
sigStored
-/
#guard_msgs in
solidity_import rejStorageSigBeforeEnumStorageStruct from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using legacy0838
  contract EncodingScalarUnorderedOrderRejects
  function storageSignatureBeforeEnumStorageStruct()

/--
error: EncodingScalarUnorderedOrderRejects.sol:83:48: Identifier: [solidity-import:unsupported] enum-storage struct ABI encoding argument beside a storage bytes/string argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.storageStringBesideEnumStorageStruct
enumStored
-/
#guard_msgs in
solidity_import rejStorageStringBesideEnumStorageStruct from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function storageStringBesideEnumStorageStruct(uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:87:41: Identifier: [solidity-import:unsupported] enum-storage struct ABI encoding argument after a calldata array or dynamic struct is unsupported
closure: EncodingScalarUnorderedOrderRejects.calldataArrayBeforeEnumStorageStruct
enumStored
-/
#guard_msgs in
solidity_import rejCalldataArrayBeforeEnumStorageStruct from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function calldataArrayBeforeEnumStorageStruct(«uint8[]»)

/--
error: EncodingScalarUnorderedOrderRejects.sol:99:37: Identifier: [solidity-import:unsupported] storage array ABI encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.storageArrayBeforePanic
arrStored
-/
#guard_msgs in
solidity_import rejStorageArrayBeforePanic from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function storageArrayBeforePanic(uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:103:37: Identifier: [solidity-import:unsupported] storage array ABI encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.storageArrayBeforeCalldataMember
arrStored
-/
#guard_msgs in
solidity_import rejStorageArrayBeforeCalldataMember from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function storageArrayBeforeCalldataMember(NarrowPair)

/--
error: EncodingScalarUnorderedOrderRejects.sol:107:48: Identifier: [solidity-import:unsupported] storage array ABI encoding argument beside a storage bytes/string argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.storageStringBesideStorageArray
arrStored
-/
#guard_msgs in
solidity_import rejStorageStringBesideStorageArray from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function storageStringBesideStorageArray(uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:111:41: Identifier: [solidity-import:unsupported] storage array ABI encoding argument after a calldata array or dynamic struct is unsupported
closure: EncodingScalarUnorderedOrderRejects.calldataArrayBeforeStorageArray
arrStored
-/
#guard_msgs in
solidity_import rejCalldataArrayBeforeStorageArray from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function calldataArrayBeforeStorageArray(«uint8[]»)

/--
error: EncodingScalarUnorderedOrderRejects.sol:115:48: Conditional: [solidity-import:unsupported] non-deferred storage bytes/string encoding argument after a storage bytes/string argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.storageStringBeforeStorageConditionalEncode
c ? sigMap[1] : sigMap[2]
-/
#guard_msgs in
solidity_import rejStorageStringBeforeStorageCondEncode from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function storageStringBeforeStorageConditionalEncode(bool,uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:119:54: Conditional: [solidity-import:unsupported] non-deferred storage bytes/string encoding argument after a storage bytes/string argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.storageStringBeforeStorageConditionalPacked
c ? sigMap[1] : sigMap[2]
-/
#guard_msgs in
solidity_import rejStorageStringBeforeStorageCondPacked from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function storageStringBeforeStorageConditionalPacked(bool,uint256)

end SolidityImportSmoke.EncodingScalarUnorderedChecks
