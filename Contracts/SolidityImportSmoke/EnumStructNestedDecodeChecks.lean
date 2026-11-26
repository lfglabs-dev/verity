import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.EnumStructNestedDecodeChecks
open Compiler.CompilationModel Denote

solidity_profile structProfile where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import imported from "Contracts/SolidityImportSmoke" entry "EnumStructNestedDecode.sol"
  using structProfile
  contract EnumStructNestedDecode
  function writePacked(uint64,uint8,uint64,bool)
  function writeLevelParam(Level)
  function readLevelCast()
  function isHigh()
  function readUnusedLevel()
  function copyPackedToMemory()
  function pushAndReadArray(uint64,uint8,uint64,bool)
  function decodeOuter(bytes)
  function decodeOuterTuple(bytes)
  function decodeInterfaceConfig(bytes)
  function processInterfaceOrder(IRegistry.Order)
  function sumInterfaceItems(«IRegistry.Item[]»)

private def oracle := SolidityImport.Differential.oracle

private def runWithWorld (name : String) (args : List Nat) (world : Verity.ContractState) :
    Option (Bool × Option (List UInt8) × List Nat × Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let r := denoteFunction oracle imported.model fn
    { sender := 1, functionSelector := 0, args } world
  let words := if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords
  return (r.success, r.revertData, words, r.finalStorage 0)

private def runBytesArg (name : String) (payloadWords : List Nat) :
    Option (Bool × Option (List UInt8) × List Nat × Nat) :=
  runWithWorld name ([32, 32 * payloadWords.length] ++ payloadWords) Verity.defaultState

private def runCalldataWords (name : String) (words : List Nat) :
    Option (Bool × Option (List UInt8) × List Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let r := denoteFunction oracle imported.model fn
    { sender := 1, functionSelector := 0, args := words } Verity.defaultState
  let out := if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords
  return (r.success, r.revertData, out)

-- Exact packed storage layout for `Packed { uint64 head; Level level; uint64 tail; bool flag; }`:
-- head at bits [0..63], level at [64..71], tail at [72..135], flag at [136..143].
private def packedWord (head level tail flag : Nat) : Nat :=
  head + level * (2 ^ 64) + tail * (2 ^ 72) + flag * (2 ^ 136)

#guard runWithWorld "writePacked" [0x1122, 1, 0x3344, 1] Verity.defaultState ==
  some (true, none, [], packedWord 0x1122 1 0x3344 1)

-- Out-of-range enum cast `Level(2)` panics with Panic(0x21).
#guard runWithWorld "writePacked" [0x1122, 2, 0x3344, 1] Verity.defaultState ==
  some (false, some (panicBytes 0x21), [], 0)

-- Parameter write packs level without clobbering sibling fields.
#guard runWithWorld "writeLevelParam" [1]
    (Verity.defaultState.writePhysicalSlot 0 (.ofNat (packedWord 0xaa 0 0xbb 1))) ==
  some (true, none, [], packedWord 0xaa 1 0xbb 1)

-- Clean enum reads via cast, comparison, and memory copy.
private def cleanWorld :=
  Verity.defaultState.writePhysicalSlot 0 (.ofNat (packedWord 0x55 1 0x66 1))
private def dirtyWorld :=
  Verity.defaultState.writePhysicalSlot 0 (.ofNat (packedWord 0x55 2 0x66 1))

#guard runWithWorld "readLevelCast" [] cleanWorld ==
  some (true, none, [1], packedWord 0x55 1 0x66 1)
#guard runWithWorld "isHigh" [] cleanWorld ==
  some (true, none, [1], packedWord 0x55 1 0x66 1)
#guard runWithWorld "copyPackedToMemory" [] cleanWorld ==
  some (true, none, [0x55, 1, 0x66, 1], packedWord 0x55 1 0x66 1)

-- Dirty storage enum byte (= 2 >= 2) triggers Panic(0x21) on cast, comparison, and copy,
-- while an unreferenced local initializer does not panic (matching solc).
#guard runWithWorld "readLevelCast" [] dirtyWorld ==
  some (false, some (panicBytes 0x21), [], packedWord 0x55 2 0x66 1)
#guard runWithWorld "isHigh" [] dirtyWorld ==
  some (false, some (panicBytes 0x21), [], packedWord 0x55 2 0x66 1)
#guard runWithWorld "copyPackedToMemory" [] dirtyWorld ==
  some (false, some (panicBytes 0x21), [], packedWord 0x55 2 0x66 1)
#guard runWithWorld "readUnusedLevel" [] dirtyWorld ==
  some (true, none, [0x55], packedWord 0x55 2 0x66 1)

-- Raw-slot storage array of packed enum structs.
#guard (runWithWorld "pushAndReadArray" [7, 1, 9, 1] Verity.defaultState).map (fun r => (r.1, r.2.1, r.2.2.1)) ==
  some (true, none, [1])
#guard (runWithWorld "pushAndReadArray" [7, 2, 9, 1] Verity.defaultState).map (fun r => (r.1, r.2.1, r.2.2.1)) ==
  some (false, some (panicBytes 0x21), [])

-- `abi.decode(data, (Outer))` with nested static `Packed` struct + `Level` enums.
#guard (runBytesArg "decodeOuter" [10, 1, 20, 1, 1, 100]).map (fun r => (r.1, r.2.1, r.2.2.1)) ==
  some (true, none, [130, 1, 1, 1])
-- Out-of-range nested enum word (= 2) reverts empty.
#guard (runBytesArg "decodeOuter" [10, 2, 20, 1, 1, 100]).map (fun r => (r.1, r.2.1)) ==
  some (false, some [])
-- Out-of-range outer enum word (= 2) reverts empty.
#guard (runBytesArg "decodeOuter" [10, 1, 20, 1, 2, 100]).map (fun r => (r.1, r.2.1)) ==
  some (false, some [])
-- Dirty nested bool word (= 2) reverts empty.
#guard (runBytesArg "decodeOuter" [10, 1, 20, 2, 1, 100]).map (fun r => (r.1, r.2.1)) ==
  some (false, some [])
-- Too-short buffer (5 words instead of 6) reverts empty.
#guard (runBytesArg "decodeOuter" [10, 1, 20, 1, 1]).map (fun r => (r.1, r.2.1)) ==
  some (false, some [])
-- Tuple decode `(Outer, uint256)`.
#guard (runBytesArg "decodeOuterTuple" [10, 1, 20, 0, 1, 100, 5]).map (fun r => (r.1, r.2.1, r.2.2.1)) ==
  some (true, none, [115, 1])

-- Interface-declared struct with interface-typed field + enum in `abi.decode`.
#guard (runBytesArg "decodeInterfaceConfig" [0x1234, 2, 40]).map (fun r => (r.1, r.2.1, r.2.2.1)) ==
  some (true, none, [0x1234, 2, 41])
-- Dirty interface-typed `IAsset` address word (>= 2^160) reverts empty.
#guard (runBytesArg "decodeInterfaceConfig" [2 ^ 160 + 1, 2, 40]).map (fun r => (r.1, r.2.1)) ==
  some (false, some [])
-- Out-of-range interface enum `Grade` (= 3) reverts empty.
#guard (runBytesArg "decodeInterfaceConfig" [0x1234, 3, 40]).map (fun r => (r.1, r.2.1)) ==
  some (false, some [])

-- Interface-declared dynamic struct (`IRegistry.Order`) with `IAsset` field in ABI schema.
private def orderWords (asset amount : Nat) : List Nat :=
  [32, asset, amount, 96, 3, 0x010203 * (2 ^ 232)]

#guard runCalldataWords "processInterfaceOrder" (orderWords 0xabcd 55) ==
  some (true, none, [0xabcd, 55, 3])
#guard runCalldataWords "processInterfaceOrder" (orderWords (2 ^ 160 + 1) 55) ==
  some (false, some [], [])

-- Interface-declared struct array (`IRegistry.Item[]`) with `IAsset` field in ABI schema.
private def itemsWords (a1 q1 a2 q2 : Nat) : List Nat :=
  [32, 2, a1, q1, a2, q2]

#guard runCalldataWords "sumInterfaceItems" (itemsWords 0x1111 10 0x2222 25) ==
  some (true, none, [35, 0x2222])
#guard runCalldataWords "sumInterfaceItems" (itemsWords 0x1111 10 (2 ^ 160 + 7) 25) ==
  some (false, some [], [])

end SolidityImportSmoke.EnumStructNestedDecodeChecks
