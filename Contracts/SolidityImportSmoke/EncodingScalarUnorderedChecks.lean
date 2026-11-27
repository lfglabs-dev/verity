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

solidity_import posViaIr0834 from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0834
  contract EncodingScalarUnorderedOrderRejects
  function calldataStructBeforeInert(NarrowPair,uint256)
  function panicBeforeCalldataStruct(NarrowPair,uint256)
  function unguardedCalldataStructBeforePanic(FullPair,uint256)
  function storageSignatureBeforeInert(uint256)
  function calldataStructBeforeCalldataMember(NarrowPair,NarrowPair)
  function storageArrayBeforeInert(uint256)
  function scalarReadBeforeMemoryWriteStatic(«Elem[]»)
  function scalarReadBeforeMemoryWriteDynamic(«Elem[]»)
  function scalarMemberBeforeMemoryWrite(«Elem[]»,uint256)

solidity_import posLegacy0834 from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using legacy0834
  contract EncodingScalarUnorderedOrderRejects
  function calldataStructBeforeInert(NarrowPair,uint256)
  function panicBeforeCalldataStruct(NarrowPair,uint256)
  function unguardedCalldataStructBeforePanic(FullPair,uint256)
  function storageSignatureBeforeInert(uint256)
  function calldataStructBeforeCalldataMember(NarrowPair,NarrowPair)
  function storageArrayBeforeInert(uint256)
  function scalarReadBeforeMemoryWriteStatic(«Elem[]»)
  function scalarReadBeforeMemoryWriteDynamic(«Elem[]»)
  function scalarMemberBeforeMemoryWrite(«Elem[]»,uint256)

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
  function scalarReadBeforeMemoryWriteStatic(«Elem[]»)
  function scalarReadBeforeMemoryWriteDynamic(«Elem[]»)
  function scalarMemberBeforeMemoryWrite(«Elem[]»,uint256)

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
  function scalarReadBeforeMemoryWriteStatic(«Elem[]»)
  function scalarReadBeforeMemoryWriteDynamic(«Elem[]»)
  function scalarMemberBeforeMemoryWrite(«Elem[]»,uint256)

private def oracle := SolidityImport.Differential.oracle

private def observePos (m : CompilationModel) (name : String) (args : List Nat) :
    Option (Bool × Option (List UInt8) × List Nat) := do
  let fn ← m.functions.find? (·.name == name)
  let r := denoteFunction oracle m fn { sender := 0x1234, functionSelector := 0, args } Verity.defaultState
  return (r.success, r.revertData, if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords)

-- Positive-control runtime denotation checks across all four pinned profiles (0.8.34 & 0.8.38, via-IR & legacy):
-- 1. `panicBeforeCalldataStruct` and `unguardedCalldataStructBeforePanic` hit `Panic(0x12)` at `x = 0`.
#guard [posViaIr0834.model, posLegacy0834.model, posViaIr0838.model, posLegacy0838.model].all fun m =>
  observePos m "panicBeforeCalldataStruct" [5, 7, 0] == some (false, some (panicBytes 0x12), []) &&
  observePos m "unguardedCalldataStructBeforePanic" [5, 7, 0] == some (false, some (panicBytes 0x12), [])

-- 2. `calldataStructBeforeInert`, `storageSignatureBeforeInert`, `calldataStructBeforeCalldataMember`,
-- and `storageArrayBeforeInert` succeed and agree across all four pinned profiles.
#guard let b := observePos posViaIr0834.model "calldataStructBeforeInert" [5, 7, 0]
  b.any (·.1) && [posLegacy0834.model, posViaIr0838.model, posLegacy0838.model].all fun m =>
    observePos m "calldataStructBeforeInert" [5, 7, 0] == b
#guard let b := observePos posViaIr0834.model "storageSignatureBeforeInert" [0]
  b.any (·.1) && [posLegacy0834.model, posViaIr0838.model, posLegacy0838.model].all fun m =>
    observePos m "storageSignatureBeforeInert" [0] == b
#guard let b := observePos posViaIr0834.model "calldataStructBeforeCalldataMember" [5, 7, 0, 8]
  b.any (·.1) && [posLegacy0834.model, posViaIr0838.model, posLegacy0838.model].all fun m =>
    observePos m "calldataStructBeforeCalldataMember" [5, 7, 0, 8] == b
#guard let b := observePos posViaIr0834.model "storageArrayBeforeInert" [0]
  b.any (·.1) && [posLegacy0834.model, posViaIr0838.model, posLegacy0838.model].all fun m =>
    observePos m "storageArrayBeforeInert" [0] == b

-- 3. `scalarReadBeforeMemoryWriteStatic` and `scalarReadBeforeMemoryWriteDynamic` on `xs = [Elem(1)]`
-- (`[32, 1, 1]`) evaluate `e.a == 1` (`true`) before `_writeElem(e, 9)` (`e.a = 9`) across all four
-- pinned profiles (`0.8.34` and `0.8.38`, via-IR and legacy), matching Anvil solc ground truth.
#guard [posViaIr0834.model, posLegacy0834.model, posViaIr0838.model, posLegacy0838.model].all fun m =>
  observePos m "scalarReadBeforeMemoryWriteStatic" [32, 1, 1] ==
    some (true, none, [0x4155c2f711f2cdd34f8262ab8fb9b7020a700fe7b6948222152f7670d1fdf34d]) &&
  observePos m "scalarReadBeforeMemoryWriteDynamic" [32, 1, 1] ==
    some (true, none, [0xfdf50d0c5ec00001cecd52e44009e09154678e69abaf7ce5d70eef8a05006e9a]) &&
  observePos m "scalarMemberBeforeMemoryWrite" [64, 0, 1, 1] ==
    some (true, none, [0x4155c2f711f2cdd34f8262ab8fb9b7020a700fe7b6948222152f7670d1fdf34d])

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

/--
error: EncodingScalarUnorderedOrderRejects.sol:123:37: Identifier: [solidity-import:unsupported] calldata or enum-storage struct ABI encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.enumStorageStructBeforeMemoryCondFromStorage
enumStored
-/
#guard_msgs in
solidity_import rejEnumStorageBeforeMemCondFromStorage from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function enumStorageStructBeforeMemoryCondFromStorage(bool)

/--
error: EncodingScalarUnorderedOrderRejects.sol:127:37: Identifier: [solidity-import:unsupported] calldata or enum-storage struct ABI encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.calldataStructBeforeMemoryCondFromStorage
p
-/
#guard_msgs in
solidity_import rejCalldataStructBeforeMemCondFromStorage from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function calldataStructBeforeMemoryCondFromStorage(NarrowPair,bool)

/--
error: EncodingScalarUnorderedOrderRejects.sol:131:37: Identifier: [solidity-import:unsupported] storage array ABI encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.storageArrayBeforeMemoryCondFromStorage
arrStored
-/
#guard_msgs in
solidity_import rejStorageArrayBeforeMemCondFromStorage from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function storageArrayBeforeMemoryCondFromStorage(bool)

/--
error: EncodingScalarUnorderedOrderRejects.sol:135:43: Conditional: [solidity-import:unsupported] storage bytes/string encoding argument before a sibling that can revert or write is unsupported
closure: EncodingScalarUnorderedOrderRejects.storageConditionalBeforeMemoryCondFromStorage
c1 ? sigMap[0] : sigMap[1]
-/
#guard_msgs in
solidity_import rejStorageCondBeforeMemCondFromStorage from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function storageConditionalBeforeMemoryCondFromStorage(bool,bool)

/--
error: EncodingScalarUnorderedOrderRejects.sol:176:37: Identifier: [solidity-import:unsupported] memory struct ABI encoding argument before a memory-writing sibling is unsupported
closure: EncodingScalarUnorderedOrderRejects.memoryStructBeforeMemoryWrite
e
-/
#guard_msgs in
solidity_import rejMemoryStructBeforeMemWrite from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function memoryStructBeforeMemoryWrite(«Elem[]»,bool)

/--
error: EncodingScalarUnorderedOrderRejects.sol:180:37: MemberAccess: [solidity-import:unsupported] memory bytes/string ABI encoding argument before a memory-writing sibling is unsupported
closure: EncodingScalarUnorderedOrderRejects.memoryBytesBeforeMemoryWrite
d.b
-/
#guard_msgs in
solidity_import rejMemoryBytesBeforeMemWrite from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function memoryBytesBeforeMemoryWrite(DynElem,bool)

/--
error: EncodingScalarUnorderedOrderRejects.sol:184:43: MemberAccess: [solidity-import:unsupported] memory bytes/string ABI encoding argument before a memory-writing sibling is unsupported
closure: EncodingScalarUnorderedOrderRejects.memoryBytesPackedBeforeMemoryWrite
d.b
-/
#guard_msgs in
solidity_import rejMemoryBytesPackedBeforeMemWrite from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function memoryBytesPackedBeforeMemoryWrite(DynElem,bool)

/--
error: EncodingScalarUnorderedOrderRejects.sol:189:37: Identifier: [solidity-import:unsupported] memory array ABI encoding argument before a memory-writing sibling is unsupported
closure: EncodingScalarUnorderedOrderRejects.memoryArrayBeforeMemoryWrite
ys
-/
#guard_msgs in
solidity_import rejMemoryArrayBeforeMemWrite from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function memoryArrayBeforeMemoryWrite(bool)

/--
error: EncodingScalarUnorderedOrderRejects.sol:194:36: Conditional: [solidity-import:unsupported] memory-writing event data argument before an indexed argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.emitDataMemoryWriteBeforeTopic
c ? _writeElem(e, 9) : 0
-/
#guard_msgs in
solidity_import rejEmitDataMemWriteBeforeTopic from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function emitDataMemoryWriteBeforeTopic(bytes,«Elem[]»,bool)

/--
error: EncodingScalarUnorderedOrderRejects.sol:217:41: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.enumStorageHelperBeforePanic
_readEnumStored()
-/
#guard_msgs in
solidity_import rejEnumStorageHelperBeforePanic from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function enumStorageHelperBeforePanic(bool,uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:223:37: IndexAccess: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.enumStorageOrderedIndexBeforePanic
modeArr[0]
-/
#guard_msgs in
solidity_import rejEnumStorageOrderedIndexBeforePanic from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function enumStorageOrderedIndexBeforePanic(uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:228:47: FunctionCall: [solidity-import:unsupported] memory bytes/string ABI encoding argument before a memory-writing sibling is unsupported
closure: EncodingScalarUnorderedOrderRejects.memorySignatureBeforeMemoryWrite
string(b)
-/
#guard_msgs in
solidity_import rejMemorySignatureBeforeMemWrite from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function memorySignatureBeforeMemoryWrite(bool)

/--
error: EncodingScalarUnorderedOrderRejects.sol:248:76: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.keccakConditionalAssignInEncodeWithSelector
keccak256((y = 2) > 0 ? bytes("a") : bytes("b"))
-/
#guard_msgs in
solidity_import rejKeccakConditionalAssignInSelector from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function keccakConditionalAssignInEncodeWithSelector(bool)

/--
error: EncodingScalarUnorderedOrderRejects.sol:252:62: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.keccakStatefulBytesHelperInEncode
keccak256(_writeStateBytes())
-/
#guard_msgs in
solidity_import rejKeccakStatefulBytesHelperInEncode from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function keccakStatefulBytesHelperInEncode(bool)

/--
error: EncodingScalarUnorderedOrderRejects.sol:257:37: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.enumStorageFnPtrHelperBeforePanic
_wrapEnumFnPtr()
-/
#guard_msgs in
solidity_import rejEnumStorageFnPtrHelperBeforePanic from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function enumStorageFnPtrHelperBeforePanic(uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:286:41: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.enumStorageModifiedHelperBeforePanic
_withEnumModArg()
-/
#guard_msgs in
solidity_import rejEnumStorageModifiedHelperBeforePanic from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function enumStorageModifiedHelperBeforePanic(bool,uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:290:43: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.packedKeccakEnumBytesHelperBeforePanic
keccak256(_bytesReadingEnum())
-/
#guard_msgs in
solidity_import rejPackedKeccakEnumBytesHelperBeforePanic from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function packedKeccakEnumBytesHelperBeforePanic(uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:294:37: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.encodeEnumBytesHelperBeforePanic
_bytesReadingEnum()
-/
#guard_msgs in
solidity_import rejEncodeEnumBytesHelperBeforePanic from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function encodeEnumBytesHelperBeforePanic(uint256)

/--
error: EncodingScalarUnorderedOrderRejects.sol:298:50: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: EncodingScalarUnorderedOrderRejects.signatureEnumStringHelperBeforePanic
_stringReadingEnum()
-/
#guard_msgs in
solidity_import rejSignatureEnumStringHelperBeforePanic from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedOrderRejects.sol"
  using viaIr0838
  contract EncodingScalarUnorderedOrderRejects
  function signatureEnumStringHelperBeforePanic(uint256)

end SolidityImportSmoke.EncodingScalarUnorderedChecks
