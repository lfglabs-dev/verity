import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.EnumFlatStructChecks
open Compiler.CompilationModel Denote

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
  evmVersion := "cancun"
  viaIR := true
  optimizerRuns := some 200
  bytecodeHash := "none"

solidity_profile legacy0838 where
  solc := "0.8.38+commit.1835d247"
  evmVersion := "cancun"
  viaIR := false
  optimizerRuns := some 200
  bytecodeHash := "none"

solidity_import importedViaIr0834 from "Contracts/SolidityImportSmoke" entry "EnumFlatStructSequence.sol"
  using viaIr0834
  contract SequenceFixture
  function change(uint256)
  function read()

solidity_import importedLegacy0834 from "Contracts/SolidityImportSmoke" entry "EnumFlatStructSequence.sol"
  using legacy0834
  contract SequenceFixture
  function change(uint256)
  function read()

solidity_import importedViaIr0838 from "Contracts/SolidityImportSmoke" entry "EnumFlatStructSequence.sol"
  using viaIr0838
  contract SequenceFixture
  function change(uint256)
  function read()

solidity_import importedLegacy0838 from "Contracts/SolidityImportSmoke" entry "EnumFlatStructSequence.sol"
  using legacy0838
  contract SequenceFixture
  function change(uint256)
  function read()

solidity_import orderViaIr0838 from "Contracts/SolidityImportSmoke" entry "EnumFlatStructOrderAndRejects.sol"
  using viaIr0838
  contract EnumFlatStructOrderAndRejects
  function namedOrder(uint256,uint256)
  function dirtyNarrowCast()
  function staticCallStructArg(address,Kind)

solidity_import orderLegacy0838 from "Contracts/SolidityImportSmoke" entry "EnumFlatStructOrderAndRejects.sol"
  using legacy0838
  contract EnumFlatStructOrderAndRejects
  function namedOrder(uint256,uint256)
  function dirtyNarrowCast()
  function staticCallStructArg(address,Kind)

private def oracle := SolidityImport.Differential.oracle

private def runFn (m : CompilationModel) (name : String) (args : List Nat) :
    Option (Bool × Option (List UInt8) × List Nat) := do
  let fn ← m.functions.find? (·.name == name)
  let r := denoteFunction oracle m fn { sender := 0x1234, functionSelector := 0, args } Verity.defaultState
  return (r.success, r.revertData, r.returnWords)

private def runChange (m : CompilationModel) (x : Nat) :
    Option (Bool × Option (List UInt8) × List Nat) :=
  runFn m "change" [x]

-- All four pinned profiles (0.8.34 & 0.8.38, legacy & via-IR) agree:
-- shape 0 in-range: y = 2 | (4 << 3) | (7 << 24) => Kind.Gamma (2), Stage.Closed (4), index 7.
private def inRangeShape0 : Nat := (2 + (4 <<< 3) + (7 <<< 24)) * 6 + 0
#guard runChange importedViaIr0834.model inRangeShape0 == some (true, none, [7, 2, 4])
#guard runChange importedLegacy0834.model inRangeShape0 == some (true, none, [7, 2, 4])
#guard runChange importedViaIr0838.model inRangeShape0 == some (true, none, [7, 2, 4])
#guard runChange importedLegacy0838.model inRangeShape0 == some (true, none, [7, 2, 4])

-- Out-of-range integer-to-enum conversion Kind(3) => Panic(0x21).
private def outOfRangeKindCast : Nat := 3 * 6 + 0
#guard runChange importedViaIr0834.model outOfRangeKindCast == some (false, some (panicBytes 0x21), [])
#guard runChange importedLegacy0834.model outOfRangeKindCast == some (false, some (panicBytes 0x21), [])
#guard runChange importedViaIr0838.model outOfRangeKindCast == some (false, some (panicBytes 0x21), [])
#guard runChange importedLegacy0838.model outOfRangeKindCast == some (false, some (panicBytes 0x21), [])

-- Unmasked uint256 256 in Kind(uint256(256)) => Panic(0x21) (must not mask low byte to 0).
private def highByteKindCast : Nat := 256 * 6 + 4
#guard runChange importedViaIr0838.model highByteKindCast == some (false, some (panicBytes 0x21), [])
#guard runChange importedLegacy0838.model highByteKindCast == some (false, some (panicBytes 0x21), [])

-- Negative int256 in Kind(int256(-1)) => Panic(0x21) (y = 1 => 1 - 2 = -1).
private def negativeIntCast : Nat := 1 * 6 + 3
#guard runChange importedViaIr0838.model negativeIntCast == some (false, some (panicBytes 0x21), [])
#guard runChange importedLegacy0838.model negativeIntCast == some (false, some (panicBytes 0x21), [])

-- Out-of-range abi.decode ordinal (y = 3 in shape 5) => empty revert (0x), NOT Panic(0x21).
private def outOfRangeDecode : Nat := 3 * 6 + 5
#guard runChange importedViaIr0838.model outOfRangeDecode == some (false, some [], [])
#guard runChange importedLegacy0838.model outOfRangeDecode == some (false, some [], [])

-- In-range multi-return helper load + promote (shape 1): index 9, Kind.Beta (1), Stage promoted to Active (2).
private def multiReturnPromote : Nat := (9 + (1 <<< 65) + (4 <<< 68) + (1 <<< 71)) * 6 + 1
#guard runChange importedViaIr0838.model multiReturnPromote == some (true, none, [9, 1, 2])
#guard runChange importedLegacy0838.model multiReturnPromote == some (true, none, [9, 1, 2])

-- Named struct constructor evaluation order:
-- via-IR evaluates written order (`kind` first -> Panic(0x21)), legacy evaluates declaration order (`ratio` first -> Panic(0x12)).
#guard runFn orderViaIr0838.model "namedOrder" [0, 9] == some (false, some (panicBytes 0x21), [])
#guard runFn orderLegacy0838.model "namedOrder" [0, 9] == some (false, some (panicBytes 0x12), [])

-- Dirty uint8 local (257) is cleaned to 1 (Kind.Beta) before the enum bound check on both pipelines: 5 + 1 = 6.
#guard runFn orderViaIr0838.model "dirtyNarrowCast" [] == some (true, none, [6])
#guard runFn orderLegacy0838.model "dirtyNarrowCast" [] == some (true, none, [6])

-- Root scalar enum parameter on staticCallStructArg rejects ordinal 3 at entry with empty revert.
#guard runFn orderViaIr0838.model "staticCallStructArg" [0x9999, 3] == some (false, some [], [])
#guard runFn orderLegacy0838.model "staticCallStructArg" [0x9999, 3] == some (false, some [], [])

/--
error: EnumFlatStructOrderAndRejects.sol:56:18: YulFunctionCall: [solidity-import:unsupported] unsupported Yul builtin mload
closure: EnumFlatStructOrderAndRejects.asmReadStruct
mload(p)
-/
#guard_msgs in
solidity_import rejAsmRead from "Contracts/SolidityImportSmoke" entry "EnumFlatStructOrderAndRejects.sol"
  using viaIr0838
  contract EnumFlatStructOrderAndRejects
  function asmReadStruct(uint256)

/--
error: EnumFlatStructOrderAndRejects.sol:65:28: YulIdentifier: [solidity-import:unsupported] unsupported Yul struct keccak256 member type enum EnumFlatStructOrderAndRejects.Kind
closure: EnumFlatStructOrderAndRejects.asmKeccakStruct
p
-/
#guard_msgs in
solidity_import rejAsmKeccak from "Contracts/SolidityImportSmoke" entry "EnumFlatStructOrderAndRejects.sol"
  using viaIr0838
  contract EnumFlatStructOrderAndRejects
  function asmKeccakStruct(uint256)

/--
error: EnumFlatStructOrderAndRejects.sol:73:13: YulAssignment: [solidity-import:unsupported] Yul assignment to enum variable k is unsupported
closure: EnumFlatStructOrderAndRejects.asmDirtyEnumLocal
k := 5
-/
#guard_msgs in
solidity_import rejAsmEnumAssign from "Contracts/SolidityImportSmoke" entry "EnumFlatStructOrderAndRejects.sol"
  using viaIr0838
  contract EnumFlatStructOrderAndRejects
  function asmDirtyEnumLocal()

/--
error: EnumFlatStructOrderAndRejects.sol:22:9: VariableDeclaration: [solidity-import:unsupported] unsupported flat struct member type bytes32[]
closure: EnumFlatStructOrderAndRejects.dynamicArrayMemberStruct
bytes32[] items
-/
#guard_msgs in
solidity_import rejDynArrayMember from "Contracts/SolidityImportSmoke" entry "EnumFlatStructOrderAndRejects.sol"
  using viaIr0838
  contract EnumFlatStructOrderAndRejects
  function dynamicArrayMemberStruct(uint256)

/--
error: EnumFlatStructOrderAndRejects.sol:28:9: VariableDeclaration: [solidity-import:unsupported] unsupported flat struct return member payload of type bytes
closure: EnumFlatStructOrderAndRejects.multiReturnBytesMember -> EnumFlatStructOrderAndRejects._loadWithBytes
bytes payload
-/
#guard_msgs in
solidity_import rejMultiRetBytes from "Contracts/SolidityImportSmoke" entry "EnumFlatStructOrderAndRejects.sol"
  using viaIr0838
  contract EnumFlatStructOrderAndRejects
  function multiReturnBytesMember()

/--
error: EnumFlatStructOrderAndRejects.sol:95:9: VariableDeclaration: [solidity-import:unsupported] unsupported flat struct member type enum EnumFlatStructOrderAndRejects.Kind[]
closure: EnumFlatStructOrderAndRejects.enumArrayMemberStruct
Kind[] modes
-/
#guard_msgs in
solidity_import rejEnumArrayMember from "Contracts/SolidityImportSmoke" entry "EnumFlatStructOrderAndRejects.sol"
  using viaIr0838
  contract EnumFlatStructOrderAndRejects
  function enumArrayMemberStruct(uint256)

/--
error: EnumFlatStructOrderAndRejects.sol:22:9: VariableDeclaration: [solidity-import:unsupported] unsupported flat struct member type bytes32[]
closure: EnumFlatStructOrderAndRejects.uninitArrayMemberLocal
bytes32[] items
-/
#guard_msgs in
solidity_import rejUninitArrayMember from "Contracts/SolidityImportSmoke" entry "EnumFlatStructOrderAndRejects.sol"
  using viaIr0838
  contract EnumFlatStructOrderAndRejects
  function uninitArrayMemberLocal()

-- Whole-struct storage assignment with enum members is admitted with enum validation.
solidity_import wholeStorageWriteOk from "Contracts/SolidityImportSmoke" entry "EnumFlatStructOrderAndRejects.sol"
  using viaIr0838
  contract EnumStorageWriteRejects
  function wholeStorageWrite(uint64,Kind)

/--
error: EnumFlatStructOrderAndRejects.sol:134:9: MemberAccess: [solidity-import:unsupported] nested storage struct assignment with enum members is outside this slice
closure: EnumStorageWriteRejects.nestedStorageWrite
outer.sub
-/
#guard_msgs in
solidity_import rejNestedStorageWrite from "Contracts/SolidityImportSmoke" entry "EnumFlatStructOrderAndRejects.sol"
  using viaIr0838
  contract EnumStorageWriteRejects
  function nestedStorageWrite(uint64,Kind)

end SolidityImportSmoke.EnumFlatStructChecks
