import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.StaticOracleMocks

namespace SolidityImportSmoke.BytesMemberStructChecks
open Compiler.CompilationModel Denote
open Compiler.CompilationModel.SolidityImport

solidity_profile viaIr0834 where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 200
  bytecodeHash := "none"

solidity_profile legacy0834 where
  evmVersion := "cancun"
  viaIR := false
  optimizerRuns := some 200
  bytecodeHash := "none"

solidity_profile viaIr0838 where
  solc := "0.8.38+commit.1835d247"
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 200
  bytecodeHash := "none"

solidity_profile legacy0838 where
  solc := "0.8.38+commit.1835d247"
  evmVersion := "cancun"
  viaIR := false
  optimizerRuns := some 200
  bytecodeHash := "none"

solidity_import importedViaIr0834 from "Contracts/SolidityImportSmoke" entry "BytesMemberStructSequence.sol"
  using viaIr0834
  contract SequenceFixture
  function change(uint256)
  function inspectCalldata(Clause,uint256)
  function inspectMemory(Clause,bytes)
  function decodeCalldata(bytes)
  function read()

solidity_import importedLegacy0834 from "Contracts/SolidityImportSmoke" entry "BytesMemberStructSequence.sol"
  using legacy0834
  contract SequenceFixture
  function change(uint256)
  function inspectCalldata(Clause,uint256)
  function inspectMemory(Clause,bytes)
  function decodeCalldata(bytes)
  function read()

solidity_import importedViaIr0838 from "Contracts/SolidityImportSmoke" entry "BytesMemberStructSequence.sol"
  using viaIr0838
  contract SequenceFixture
  function change(uint256)
  function inspectCalldata(Clause,uint256)
  function inspectMemory(Clause,bytes)
  function decodeCalldata(bytes)
  function read()

solidity_import importedLegacy0838 from "Contracts/SolidityImportSmoke" entry "BytesMemberStructSequence.sol"
  using legacy0838
  contract SequenceFixture
  function change(uint256)
  function inspectCalldata(Clause,uint256)
  function inspectMemory(Clause,bytes)
  function decodeCalldata(bytes)
  function read()

solidity_import namedViaIr0838 from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructOrderAndRejects
  function namedReordered(bytes)

private def oracle := SolidityImport.Differential.oracle

private def runFn (m : CompilationModel) (name : String) (args : List Nat) :
    Option (Bool × Option (List UInt8) × List Nat) := do
  let fn ← m.functions.find? (·.name == name)
  let r := denoteFunction oracle m fn { sender := 0x1234, functionSelector := 0, args } Verity.defaultState
  return (r.success, r.revertData, r.returnWords)

private def runChange (m : CompilationModel) (x : Nat) :
    Option (Bool × Option (List UInt8) × List Nat) :=
  runFn m "change" [x]

-- Shape 0 across payload lengths 0, 31, 32, 33, 70: all four pinned profiles (0.8.34 & 0.8.38, legacy & via-IR) agree!
private def shape0 (lenSel : Nat) : Nat := ((1 + (2 <<< 3) + (lenSel <<< 5) + (9 <<< 17) + (1 <<< 25)) * 8) + 0
#guard (runChange importedViaIr0834.model (shape0 0)).isSome
#guard runChange importedViaIr0834.model (shape0 0) == runChange importedLegacy0834.model (shape0 0)
#guard runChange importedViaIr0834.model (shape0 0) == runChange importedViaIr0838.model (shape0 0)
#guard runChange importedViaIr0834.model (shape0 0) == runChange importedLegacy0838.model (shape0 0)

#guard runChange importedViaIr0838.model (shape0 1) == runChange importedLegacy0838.model (shape0 1)
#guard runChange importedViaIr0838.model (shape0 2) == runChange importedLegacy0838.model (shape0 2)
#guard runChange importedViaIr0838.model (shape0 3) == runChange importedLegacy0838.model (shape0 3)
#guard runChange importedViaIr0838.model (shape0 4) == runChange importedLegacy0838.model (shape0 4)

-- Out-of-range Kind(4) in shape 0 => Panic(0x21) across all four profiles.
private def shape0BadKind : Nat := 4 * 8 + 0
#guard runChange importedViaIr0834.model shape0BadKind == some (false, some (panicBytes 0x21), [])
#guard runChange importedLegacy0834.model shape0BadKind == some (false, some (panicBytes 0x21), [])
#guard runChange importedViaIr0838.model shape0BadKind == some (false, some (panicBytes 0x21), [])
#guard runChange importedLegacy0838.model shape0BadKind == some (false, some (panicBytes 0x21), [])

-- Shape 1: `delete primary` preserves `aliasRef` (bit 14 = 1, bit 15 = 0 selects `aliasRef` with mutated parent 5+3 = 8, whereas bit 15 = 1 selects zeroed `primary` with parent 0).
private def shape1DeletePreservesAlias : Nat := ((2 + (5 <<< 0) + (1 <<< 14)) * 8) + 1
private def shape1DeleteSelectsPrimary : Nat := ((2 + (5 <<< 0) + (1 <<< 14) + (1 <<< 15)) * 8) + 1
#guard runChange importedViaIr0838.model shape1DeletePreservesAlias == runChange importedLegacy0838.model shape1DeletePreservesAlias
#guard runChange importedViaIr0838.model shape1DeleteSelectsPrimary == runChange importedLegacy0838.model shape1DeleteSelectsPrimary
#guard runChange importedViaIr0838.model shape1DeletePreservesAlias != runChange importedViaIr0838.model shape1DeleteSelectsPrimary

-- Shape 2: bidirectional `bytes memory` <-> `c.payload` sharing across 33-byte and 70-byte payloads.
private def shape2Sharing33 : Nat := ((3 + (11 <<< 8) + (1 <<< 16)) * 8) + 2
private def shape2Sharing70 : Nat := ((4 + (11 <<< 8) + (1 <<< 16)) * 8) + 2
#guard runChange importedViaIr0834.model shape2Sharing33 == runChange importedLegacy0834.model shape2Sharing33
#guard runChange importedViaIr0838.model shape2Sharing33 == runChange importedLegacy0838.model shape2Sharing33
#guard runChange importedViaIr0838.model shape2Sharing70 == runChange importedLegacy0838.model shape2Sharing70

-- Shape 3: multi-return `(Clause memory, uint256)` + tuple reassignment.
private def shape3MultiRet : Nat := ((3 + (2 <<< 8) + (1 <<< 10) + (1 <<< 21) + (1 <<< 22)) * 8) + 3
#guard runChange importedViaIr0838.model shape3MultiRet == runChange importedLegacy0838.model shape3MultiRet

-- Shape 4: out-of-bounds `selected.payload[probeIdx]` on empty uninitialized struct => Panic(0x32).
private def shape4Oob : Nat := (2 * 8) + 4
#guard runChange importedViaIr0838.model shape4Oob == some (false, some (panicBytes 0x32), [])
#guard runChange importedLegacy0838.model shape4Oob == some (false, some (panicBytes 0x32), [])

-- Shape 5: raw `abi.decode` malformed enum (variant 1 -> empty revert) vs huge length 2^64 (variant 5 -> Panic(0x41)).
#guard runChange importedViaIr0838.model (1 * 8 + 5) == some (false, some [], [])
#guard runChange importedLegacy0838.model (1 * 8 + 5) == some (false, some [], [])
#guard runChange importedViaIr0838.model (5 * 8 + 5) == some (false, some (panicBytes 0x41), [])
#guard runChange importedLegacy0838.model (5 * 8 + 5) == some (false, some (panicBytes 0x41), [])

-- Out-of-order named constructor rejects under legacy pipeline:
/--
error: BytesMemberStructOrderAndRejects.sol:29:27: FunctionCall: [solidity-import:unsupported] named arguments of a struct with bytes members must follow the declaration order
closure: BytesMemberStructOrderAndRejects.namedReordered
Clause({payload: data[0:4], kind: Kind.Exact, parent: uint8(data.length - 4)})
-/
#guard_msgs in
solidity_import rejLegacyNamedOrder from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using legacy0838
  contract BytesMemberStructOrderAndRejects
  function namedReordered(bytes)

-- `string` member in constructed struct rejects with location:
/--
error: BytesMemberStructOrderAndRejects.sol:20:9: VariableDeclaration: [solidity-import:unsupported] unsupported flat struct member type string
closure: BytesMemberStructOrderAndRejects.stringMemberConstruct
string label
-/
#guard_msgs in
solidity_import rejStringMember from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructOrderAndRejects
  function stringMemberConstruct()

-- Dynamic array member `bytes32[]` in helper-returned struct rejects with location:
/--
error: BytesMemberStructOrderAndRejects.sol:25:9: VariableDeclaration: [solidity-import:unsupported] unsupported flat struct return member words of type bytes32[]
closure: BytesMemberStructOrderAndRejects.callArrayMemberHelper -> BytesMemberStructOrderAndRejects.arrayMemberHelper
bytes32[] words
-/
#guard_msgs in
solidity_import rejArrayMemberHelper from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructOrderAndRejects
  function callArrayMemberHelper()

-- Yul `mload(c)` and `keccak256(c, 96)` on a `bytes`-member struct reject with locations:
/--
error: BytesMemberStructOrderAndRejects.sol:50:18: YulFunctionCall: [solidity-import:unsupported] unsupported Yul builtin mload
closure: BytesMemberStructOrderAndRejects.yulReadStruct
mload(c)
-/
#guard_msgs in
solidity_import rejYulReadStruct from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructOrderAndRejects
  function yulReadStruct(bytes)

/--
error: BytesMemberStructOrderAndRejects.sol:57:28: YulIdentifier: [solidity-import:unsupported] Yul struct keccak256 requires a static scalar-member memory struct
closure: BytesMemberStructOrderAndRejects.yulHashStruct
c
-/
#guard_msgs in
solidity_import rejYulHashStruct from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructOrderAndRejects
  function yulHashStruct(bytes)

-- Recursive internal call over `Clause memory` fails closed with location (slice (d) boundary):
/--
error: BytesMemberStructOrderAndRejects.sol:63:16: FunctionCall: [solidity-import:unsupported] recursive call 179
closure: BytesMemberStructOrderAndRejects.recursiveWalk -> BytesMemberStructOrderAndRejects._walk
_walk(c, depth - 1)
-/
#guard_msgs in
solidity_import rejRecursiveWalk from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructOrderAndRejects
  function recursiveWalk(bytes,uint256)

-- Mixed `bytes` + `bytes32[]` struct reports the unsupported `bytes32[]` member (slice (b) boundary), not `bytes`:
/--
error: BytesMemberStructOrderAndRejects.sol:76:9: VariableDeclaration: [solidity-import:unsupported] unsupported bytes-struct member type bytes32[]
closure: BytesMemberStructMixedRejects.mixedBytesAndArrayLocal
bytes32[] items
-/
#guard_msgs in
solidity_import rejMixedBytesAndArray from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructMixedRejects
  function mixedBytesAndArrayLocal()

-- `bytes.concat` reassignments (conditional, shared buffer, named helper, multi-return helper),
-- `s.payload[idx] = rhs` & `s.tag += rhs` RHS-first evaluation order, and multi-struct ABI roundtrip:
solidity_import concatOrderViaIr0838 from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructConcatAndOrder
  function caseConcatCond(bytes,bool)
  function caseConcatShare()
  function caseNamedHelperConcat()
  function caseMultiHelperConcat()
  function caseByteWriteOrder(uint256)
  function caseByteWriteMutateBase()
  function caseCompoundMutateBase()
  function caseMultiStructEncode()
  function caseGuardHelperShare(bool)
  function caseStaticcallShare(address)
  function caseByteWriteMutateIdx()
  function caseAbiEncodeScalarBeforeMutatingStruct()

solidity_import concatOrderLegacy0838 from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using legacy0838
  contract BytesMemberStructConcatAndOrder
  function caseConcatCond(bytes,bool)
  function caseConcatShare()
  function caseNamedHelperConcat()
  function caseMultiHelperConcat()
  function caseByteWriteOrder(uint256)
  function caseByteWriteMutateBase()
  function caseCompoundMutateBase()
  function caseMultiStructEncode()
  function caseGuardHelperShare(bool)
  function caseStaticcallShare(address)
  function caseByteWriteMutateIdx()
  function caseAbiEncodeScalarBeforeMutatingStruct()

private def cdFiveBytes (flag : Nat) : List Nat :=
  [64, flag, 5, 0x1122334455000000000000000000000000000000000000000000000000000000]

#guard runFn concatOrderViaIr0838.model "caseConcatCond" (cdFiveBytes 1) ==
  some (true, none, [3, 0x800d501693feda2226878e1ec7869eef8919dbc5bd10c2bcd031b94d73492860])
#guard runFn concatOrderLegacy0838.model "caseConcatCond" (cdFiveBytes 1) ==
  some (true, none, [3, 0x800d501693feda2226878e1ec7869eef8919dbc5bd10c2bcd031b94d73492860])
#guard runFn concatOrderViaIr0838.model "caseConcatCond" (cdFiveBytes 0) ==
  some (true, none, [5, 0x6ccdf593017c9d38b36c1cb00572feae81abc15173860a4e0904a6c45d3b086e])
#guard runFn concatOrderLegacy0838.model "caseConcatCond" (cdFiveBytes 0) ==
  some (true, none, [5, 0x6ccdf593017c9d38b36c1cb00572feae81abc15173860a4e0904a6c45d3b086e])

#guard runFn concatOrderViaIr0838.model "caseConcatShare" [] ==
  some (true, none, [0xaa <<< 248, 0xbb <<< 248, 0xbb <<< 248])
#guard runFn concatOrderLegacy0838.model "caseConcatShare" [] ==
  some (true, none, [0xaa <<< 248, 0xbb <<< 248, 0xbb <<< 248])

#guard runFn concatOrderViaIr0838.model "caseNamedHelperConcat" [] ==
  some (true, none, [3, 0x800d501693feda2226878e1ec7869eef8919dbc5bd10c2bcd031b94d73492860])
#guard runFn concatOrderLegacy0838.model "caseNamedHelperConcat" [] ==
  some (true, none, [3, 0x800d501693feda2226878e1ec7869eef8919dbc5bd10c2bcd031b94d73492860])

#guard runFn concatOrderViaIr0838.model "caseMultiHelperConcat" [] ==
  some (true, none, [4, 0x6fe2683bd1d27cbb7a05c570693bea39e0c082ed16722e5ecadcfb7cfdbd20db])
#guard runFn concatOrderLegacy0838.model "caseMultiHelperConcat" [] ==
  some (true, none, [4, 0x6fe2683bd1d27cbb7a05c570693bea39e0c082ed16722e5ecadcfb7cfdbd20db])

#guard runFn concatOrderViaIr0838.model "caseByteWriteOrder" [0] ==
  some (false, some (panicBytes 0x32), [])
#guard runFn concatOrderLegacy0838.model "caseByteWriteOrder" [0] ==
  some (false, some (panicBytes 0x32), [])

#guard runFn concatOrderViaIr0838.model "caseByteWriteMutateBase" [] ==
  some (false, some (panicBytes 0x32), [])
#guard runFn concatOrderLegacy0838.model "caseByteWriteMutateBase" [] ==
  some (false, some (panicBytes 0x32), [])

#guard runFn concatOrderViaIr0838.model "caseCompoundMutateBase" [] ==
  some (true, none, [105])
#guard runFn concatOrderLegacy0838.model "caseCompoundMutateBase" [] ==
  some (true, none, [105])

#guard runFn concatOrderViaIr0838.model "caseMultiStructEncode" [] ==
  some (true, none, [0xe81046dd2c622af9606f3f856b95c04f597eb75f71939080a24a016cac3c8bc4, 0, 254])
#guard runFn concatOrderLegacy0838.model "caseMultiStructEncode" [] ==
  some (true, none, [0xe81046dd2c622af9606f3f856b95c04f597eb75f71939080a24a016cac3c8bc4, 0, 254])

-- Guard-clause `if (flag) return a; return hex"1122";` helper preserves `hasHeader` and buffer sharing:
#guard runFn concatOrderViaIr0838.model "caseGuardHelperShare" [1] ==
  some (true, none, [0xff <<< 248, 0xff <<< 248])
#guard runFn concatOrderLegacy0838.model "caseGuardHelperShare" [1] ==
  some (true, none, [0xff <<< 248, 0xff <<< 248])
#guard runFn concatOrderViaIr0838.model "caseGuardHelperShare" [0] ==
  some (true, none, [0x41 <<< 248, 0xff <<< 248])
#guard runFn concatOrderLegacy0838.model "caseGuardHelperShare" [0] ==
  some (true, none, [0x41 <<< 248, 0xff <<< 248])

-- Low-level `staticcall` `bytes memory ret` shares its `extract_returndata` buffer with `S(..., ret)`:
private def staticOracleWorld : Verity.ContractState :=
  ({ Verity.defaultState with thisAddress := 0x1111 }).withStorageWords fun key =>
    if key == Verity.StorageKey.contractSlot 0x9999 0 then
      Verity.Core.Uint256.ofNat (0x41424344 <<< 224)
    else if key == Verity.StorageKey.contractSlot 0x9999 2 then
      Verity.Core.Uint256.ofNat 4
    else
      0

private def runFnStatic (m : CompilationModel) (name : String) (args : List Nat) :
    Option (Bool × Option (List UInt8) × List Nat) := do
  let fn ← m.functions.find? (·.name == name)
  let r := denoteFunction oracle m fn { sender := 0x1234, functionSelector := 0, args } staticOracleWorld
    (byteCalls := StaticOracleMocks.environment [0x9999] 1000000 [0x8888])
  return (r.success, r.revertData, r.returnWords)

#guard runFnStatic concatOrderViaIr0838.model "caseStaticcallShare" [0x9999] ==
  some (true, none,
    [0x6d6a8e51518c99969d0854c7fc479d5bcf059160dcd0d02d41d94ee7400484ba,
     0x6d6a8e51518c99969d0854c7fc479d5bcf059160dcd0d02d41d94ee7400484ba])
#guard runFnStatic concatOrderLegacy0838.model "caseStaticcallShare" [0x9999] ==
  some (true, none,
    [0x6d6a8e51518c99969d0854c7fc479d5bcf059160dcd0d02d41d94ee7400484ba,
     0x6d6a8e51518c99969d0854c7fc479d5bcf059160dcd0d02d41d94ee7400484ba])
#guard runFnStatic concatOrderViaIr0838.model "caseStaticcallShare" [0x8888] ==
  some (true, none,
    [0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470,
     0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470])
#guard runFnStatic concatOrderLegacy0838.model "caseStaticcallShare" [0x8888] ==
  some (true, none,
    [0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470,
     0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470])

-- `s.payload[idx] = rhs` loads `s.payload`'s buffer pointer before evaluating `idx`:
#guard runFn concatOrderViaIr0838.model "caseByteWriteMutateIdx" [] ==
  some (true, none, [0x77 <<< 248, 0])
#guard runFn concatOrderLegacy0838.model "caseByteWriteMutateIdx" [] ==
  some (true, none, [0x77 <<< 248, 0])

-- `abi.encode` snapshots `.mload` scalar head words (`p.tag`, `q.tag`) before later mutating arguments:
#guard runFn concatOrderViaIr0838.model "caseAbiEncodeScalarBeforeMutatingStruct" [] ==
  some (true, none,
    [0xa715791b003d1c4c8368f853e5f598500d8c9a5c9c6f5b12e9da2373e670c968,
     0xe87ba6c1df9028194ff1207febc36782b343e43a8b86f7e4c4fd49b014beda44])
#guard runFn concatOrderLegacy0838.model "caseAbiEncodeScalarBeforeMutatingStruct" [] ==
  some (true, none,
    [0xa715791b003d1c4c8368f853e5f598500d8c9a5c9c6f5b12e9da2373e670c968,
     0xe87ba6c1df9028194ff1207febc36782b343e43a8b86f7e4c4fd49b014beda44])

-- Unheadered special byte buffers (directly or through aliases) and Yul word loads on unpadded
-- staticcall returndata routed through helper/struct `bytes` members fail closed with locations:
/--
error: BytesMemberStructOrderAndRejects.sol:258:35: Identifier: [solidity-import:unsupported] unheadered byte buffer local cannot alias a bytes struct member
closure: BytesMemberStructUnheaderedRejects.selfDelegateUnheadered
ret
-/
#guard_msgs in
solidity_import rejSelfDelegateUnheadered from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructUnheaderedRejects
  function selfDelegateUnheadered(bytes)

/--
error: BytesMemberStructOrderAndRejects.sol:266:35: Identifier: [solidity-import:unsupported] unheadered byte buffer local cannot alias a bytes struct member
closure: BytesMemberStructUnheaderedRejects.selfDelegateAliasUnheadered
aliasBuf
-/
#guard_msgs in
solidity_import rejSelfDelegateAliasUnheadered from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructUnheaderedRejects
  function selfDelegateAliasUnheadered(bytes)

/--
error: BytesMemberStructOrderAndRejects.sol:281:18: YulFunctionCall: [solidity-import:unsupported] Yul word load from low-level staticcall return data is outside this slice
closure: BytesMemberStructUnheaderedRejects.yulUnpaddedViaHelperStruct
mload(add(b, 0x20))
-/
#guard_msgs in
solidity_import rejYulUnpaddedViaHelperStruct from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructUnheaderedRejects
  function yulUnpaddedViaHelperStruct(address)

-- Forwarded `(uint256, bytes memory)` roots preserve headered `bytes memory` locals/returns,
-- and `abi.encode` snapshots `keccak256(b)` head words before later memory-mutating arguments:
solidity_import fwdKeccakViaIr0838 from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructForwardedAndKeccak
  function fwdRootOut(bool)
  function fwdLocalB(bool)
  function fwdNamedHelper(bool)
  function fwdMultiHelper(bool)
  function encodeKeccakBeforeMutate()
  function caseBranchFnPtrShare(bool)

solidity_import fwdKeccakLegacy0838 from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using legacy0838
  contract BytesMemberStructForwardedAndKeccak
  function fwdRootOut(bool)
  function fwdLocalB(bool)
  function fwdNamedHelper(bool)
  function fwdMultiHelper(bool)
  function encodeKeccakBeforeMutate()
  function caseBranchFnPtrShare(bool)

private def expectedFwdFalse : Option (Bool × Option (List UInt8) × List Nat) :=
  some (true, none, [4, 64, 4, 0x11223344 <<< 224])

private def expectedFwdTrue : Option (Bool × Option (List UInt8) × List Nat) :=
  some (true, none, [77, 64, 32, 123])

#guard runFn fwdKeccakViaIr0838.model "fwdRootOut" [0] == expectedFwdFalse
#guard runFn fwdKeccakLegacy0838.model "fwdRootOut" [0] == expectedFwdFalse
#guard runFn fwdKeccakViaIr0838.model "fwdRootOut" [1] == expectedFwdTrue
#guard runFn fwdKeccakLegacy0838.model "fwdRootOut" [1] == expectedFwdTrue

#guard runFn fwdKeccakViaIr0838.model "fwdLocalB" [0] == expectedFwdFalse
#guard runFn fwdKeccakLegacy0838.model "fwdLocalB" [0] == expectedFwdFalse
#guard runFn fwdKeccakViaIr0838.model "fwdLocalB" [1] == expectedFwdTrue
#guard runFn fwdKeccakLegacy0838.model "fwdLocalB" [1] == expectedFwdTrue

#guard runFn fwdKeccakViaIr0838.model "fwdNamedHelper" [0] == expectedFwdFalse
#guard runFn fwdKeccakLegacy0838.model "fwdNamedHelper" [0] == expectedFwdFalse
#guard runFn fwdKeccakViaIr0838.model "fwdNamedHelper" [1] == expectedFwdTrue
#guard runFn fwdKeccakLegacy0838.model "fwdNamedHelper" [1] == expectedFwdTrue

#guard runFn fwdKeccakViaIr0838.model "fwdMultiHelper" [0] == expectedFwdFalse
#guard runFn fwdKeccakLegacy0838.model "fwdMultiHelper" [0] == expectedFwdFalse
#guard runFn fwdKeccakViaIr0838.model "fwdMultiHelper" [1] == expectedFwdTrue
#guard runFn fwdKeccakLegacy0838.model "fwdMultiHelper" [1] == expectedFwdTrue

#guard runFn fwdKeccakViaIr0838.model "encodeKeccakBeforeMutate" [] ==
  some (true, none,
    [0x1df5d90ce225586a8e44922d57c83920210b1c6f4dbf7dd0837edfa1dd196225,
     0xd91ccc7ee0af07afc11947154cf01b151a9e75bbf0e1439d2b04b893eedbd148])
#guard runFn fwdKeccakLegacy0838.model "encodeKeccakBeforeMutate" [] ==
  some (true, none,
    [0x1df5d90ce225586a8e44922d57c83920210b1c6f4dbf7dd0837edfa1dd196225,
     0xd91ccc7ee0af07afc11947154cf01b151a9e75bbf0e1439d2b04b893eedbd148])

#guard runFn fwdKeccakViaIr0838.model "caseBranchFnPtrShare" [1] ==
  some (true, none, [0xff <<< 248, 0xff <<< 248])
#guard runFn fwdKeccakLegacy0838.model "caseBranchFnPtrShare" [1] ==
  some (true, none, [0xff <<< 248, 0xff <<< 248])
#guard runFn fwdKeccakViaIr0838.model "caseBranchFnPtrShare" [0] ==
  some (true, none, [0xff <<< 248, 0xff <<< 248])
#guard runFn fwdKeccakLegacy0838.model "caseBranchFnPtrShare" [0] ==
  some (true, none, [0xff <<< 248, 0xff <<< 248])

-- `bytes(string)` conversions in `bytes` struct members (direct or via local aliases),
-- Yul word loads on `0x60`-default/struct `bytes` buffers, and inline assembly in closures
-- using `bytes`-member memory structs fail closed with locations:
/--
error: BytesMemberStructOrderAndRejects.sol:399:35: FunctionCall: [solidity-import:unsupported] bytes(...) conversion of string in a bytes struct member is outside this slice
closure: BytesMemberStructR5Rejects.stringCastDirect
bytes(str)
-/
#guard_msgs in
solidity_import rejStringCastDirect from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR5Rejects
  function stringCastDirect(string)

/--
error: BytesMemberStructOrderAndRejects.sol:405:35: Identifier: [solidity-import:unsupported] unheadered byte buffer local cannot alias a bytes struct member
closure: BytesMemberStructR5Rejects.stringCastViaLocal
b
-/
#guard_msgs in
solidity_import rejStringCastViaLocal from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR5Rejects
  function stringCastViaLocal(string)

/--
error: BytesMemberStructOrderAndRejects.sol:417:18: YulFunctionCall: [solidity-import:unsupported] Yul word load from a default-empty or struct bytes buffer is outside this slice
closure: BytesMemberStructR5Rejects.emptyBytesYulWordLoad
mload(add(b, 0x20))
-/
#guard_msgs in
solidity_import rejEmptyBytesYulWordLoad from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR5Rejects
  function emptyBytesYulWordLoad(bool)

/--
error: BytesMemberStructOrderAndRejects.sol:425:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that uses a bytes-member memory struct is outside this slice
closure: BytesMemberStructR5Rejects.asmInBytesStructClosure
assembly { w := x }
-/
#guard_msgs in
solidity_import rejAsmInBytesStructClosure from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR5Rejects
  function asmInBytesStructClosure(uint256)

/--
error: BytesMemberStructOrderAndRejects.sol:431:35: Identifier: [solidity-import:unsupported] unheadered byte buffer local cannot alias a bytes struct member
closure: BytesMemberStructR5Rejects.namedStringRetCast
b
-/
#guard_msgs in
solidity_import rejNamedStringRetCast from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR5Rejects
  function namedStringRetCast()

/--
error: BytesMemberStructOrderAndRejects.sol:437:35: Identifier: [solidity-import:unsupported] unheadered byte buffer local cannot alias a bytes struct member
closure: BytesMemberStructR5Rejects.condStringCast
b
-/
#guard_msgs in
solidity_import rejCondStringCast from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR5Rejects
  function condStringCast(bool,string)

/--
error: BytesMemberStructOrderAndRejects.sol:445:35: Identifier: [solidity-import:unsupported] unheadered byte buffer local cannot alias a bytes struct member
closure: BytesMemberStructR5Rejects.selfDelegateCondUnheadered
aliasBuf
-/
#guard_msgs in
solidity_import rejSelfDelegateCondUnheadered from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR5Rejects
  function selfDelegateCondUnheadered(bytes,bool)

/--
error: BytesMemberStructOrderAndRejects.sol:455:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that uses a bytes-member memory struct is outside this slice
closure: BytesMemberStructR5Rejects.calldataToMemScratchAsm
assembly { mstore(0, sum) return(0, 32) }
-/
#guard_msgs in
solidity_import rejCalldataToMemScratchAsm from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR5Rejects
  function calldataToMemScratchAsm(S,uint256)

solidity_import r7CasesViaIr0838 from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR7Cases
  function casePosCtorAssign()
  function casePosCtorPostInc()

solidity_import r7CasesLegacy0838 from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using legacy0838
  contract BytesMemberStructR7Cases
  function casePosCtorAssign()
  function casePosCtorPostInc()

#guard runFn r7CasesViaIr0838.model "casePosCtorAssign" [] == some (true, none, [10, 99])
#guard runFn r7CasesLegacy0838.model "casePosCtorAssign" [] == some (true, none, [10, 99])
#guard runFn r7CasesViaIr0838.model "casePosCtorPostInc" [] == some (true, none, [10, 10])
#guard runFn r7CasesLegacy0838.model "casePosCtorPostInc" [] == some (true, none, [10, 10])

/--
error: BytesMemberStructOrderAndRejects.sol:493:13: Identifier: [solidity-import:unsupported] unheadered byte buffer local cannot alias a bytes struct member
closure: BytesMemberStructR7Cases.stringCastReassignByteWrite
b
-/
#guard_msgs in
solidity_import rejStringCastReassignByteWrite from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR7Cases
  function stringCastReassignByteWrite()

/--
error: BytesMemberStructOrderAndRejects.sol:502:41: YulIdentifier: [solidity-import:unsupported] unbound Yul identifier v
closure: BytesMemberStructR7Cases.deleteNewBytesYul
v
-/
#guard_msgs in
solidity_import rejDeleteNewBytesYul from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR7Cases
  function deleteNewBytesYul()

/--
error: BytesMemberStructOrderAndRejects.sol:510:36: YulIdentifier: [solidity-import:unsupported] unbound Yul identifier v
closure: BytesMemberStructR7Cases.concatReassignBytesYulWrite
v
-/
#guard_msgs in
solidity_import rejConcatReassignBytesYulWrite from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR7Cases
  function concatReassignBytesYulWrite()

/--
error: BytesMemberStructOrderAndRejects.sol:517:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that uses a bytes-member memory struct is outside this slice
closure: BytesMemberStructR7Cases.nestedOuterBytesWriteAsm
assembly { mstore8(0x140, 0xff) }
-/
#guard_msgs in
solidity_import rejNestedOuterBytesWriteAsm from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR7Cases
  function nestedOuterBytesWriteAsm(Outer)

solidity_import r8CasesViaIr0838 from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR8Cases
  function caseYulOverwriteViaBytesCast(address)
  function caseYulOverwriteViaStringReadBytes(address)
  function caseNewStringCastYulMstore()

solidity_import r8CasesLegacy0838 from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using legacy0838
  contract BytesMemberStructR8Cases
  function caseYulOverwriteViaBytesCast(address)
  function caseYulOverwriteViaStringReadBytes(address)
  function caseNewStringCastYulMstore()

#guard runFnStatic r8CasesViaIr0838.model "caseYulOverwriteViaBytesCast" [0x9999] ==
  some (true, none, [25342555104619065936111544627061517515100423381350577477266317912997047271227])
#guard runFnStatic r8CasesLegacy0838.model "caseYulOverwriteViaBytesCast" [0x9999] ==
  some (true, none, [25342555104619065936111544627061517515100423381350577477266317912997047271227])
#guard runFnStatic r8CasesViaIr0838.model "caseYulOverwriteViaStringReadBytes" [0x9999] ==
  some (true, none, [25342555104619065936111544627061517515100423381350577477266317912997047271227])
#guard runFnStatic r8CasesLegacy0838.model "caseYulOverwriteViaStringReadBytes" [0x9999] ==
  some (true, none, [25342555104619065936111544627061517515100423381350577477266317912997047271227])
#guard runFn r8CasesViaIr0838.model "caseNewStringCastYulMstore" [] ==
  some (true, none, [0xff <<< 248, 0xff <<< 248])
#guard runFn r8CasesLegacy0838.model "caseNewStringCastYulMstore" [] ==
  some (true, none, [0xff <<< 248, 0xff <<< 248])

/--
error: BytesMemberStructOrderAndRejects.sol:564:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that uses a bytes-member memory struct is outside this slice
closure: BytesMemberStructR8Cases.nestedCalldataToMemCorruptAsm
assembly { mstore8(0x180, 0xff) }
-/
#guard_msgs in
solidity_import rejNestedCalldataToMemCorruptAsm from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR8Cases
  function nestedCalldataToMemCorruptAsm(Outer)

/--
error: BytesMemberStructOrderAndRejects.sol:573:13: Identifier: [solidity-import:unsupported] unheadered byte buffer local cannot alias a bytes struct member
closure: BytesMemberStructR8Cases.stringRoundtripRawByteWrite
raw
-/
#guard_msgs in
solidity_import rejStringRoundtripRawByteWrite from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR8Cases
  function stringRoundtripRawByteWrite(bool)

/--
error: BytesMemberStructOrderAndRejects.sol:591:9: MemberAccess: [solidity-import:unsupported] unheadered byte buffer local cannot alias a bytes struct member
closure: BytesMemberStructR8Cases.multiStringStructMutate
m.payload
-/
#guard_msgs in
solidity_import rejMultiStringStructMutate from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR8Cases
  function multiStringStructMutate(bytes)

/--
error: BytesMemberStructOrderAndRejects.sol:599:9: MemberAccess: [solidity-import:unsupported] unheadered byte buffer local cannot alias a bytes struct member
closure: BytesMemberStructR8Cases.namedStringRetStructMutate
m.payload
-/
#guard_msgs in
solidity_import rejNamedStringRetStructMutate from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR8Cases
  function namedStringRetStructMutate(bytes,bool)

/--
error: BytesMemberStructOrderAndRejects.sol:609:9: MemberAccess: [solidity-import:unsupported] unheadered byte buffer local cannot alias a bytes struct member
closure: BytesMemberStructR8Cases.namedDynTupleStringStructMutate
m.payload
-/
#guard_msgs in
solidity_import rejNamedDynTupleStringStructMutate from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR8Cases
  function namedDynTupleStringStructMutate(bytes)

/--
error: BytesMemberStructOrderAndRejects.sol:616:31: Identifier: [solidity-import:unsupported] unheadered byte buffer local cannot alias a bytes struct member
closure: BytesMemberStructR8Cases.newBytesStructHopRawMutate
raw
-/
#guard_msgs in
solidity_import rejNewBytesStructHopRawMutate from "Contracts/SolidityImportSmoke" entry "BytesMemberStructOrderAndRejects.sol"
  using viaIr0838
  contract BytesMemberStructR8Cases
  function newBytesStructHopRawMutate()

end SolidityImportSmoke.BytesMemberStructChecks
