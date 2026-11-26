import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.Transactions

namespace SolidityImportSmoke.RawSlotTwoDimStructMappingChecks
open Compiler.CompilationModel Denote
open Compiler.CompilationModel.SolidityImport.Transactions

solidity_profile rawSlotProfile where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import imported from "Contracts/SolidityImportSmoke" entry "RawSlotTwoDimStructMapping.sol"
  using rawSlotProfile
  contract RawSlotTwoDimStructMapping
  function writeDirectGrid(uint256,uint256,uint128,uint64,uint8,bool,address,uint96)
  function readDirectGrid(uint256,uint256)
  function updateViaPointer(uint256,uint256,uint128,uint64,bool)
  function writeAndReadAccount(address,uint256,uint128,uint8,address,uint96)
  function readRowHelper(uint256,uint256)
  function deleteGridEntry(uint256,uint256)
  function rawGridWords(uint256,uint256)
  function rawAccountWords(address,uint256)

#guard imported.report.functions.length == 8
#guard imported.report.functions.all (·.denoteCovered)

private def oracle := SolidityImport.Differential.oracle

private def decodeWords (bytes : List UInt8) : List Nat :=
  (List.range (bytes.length / 32)).map fun w =>
    (List.range 32).foldl (fun acc i => acc * 256 + (bytes.getD (32 * w + i) 0).toNat) 0

private def callWorld (name : String) (args : List Nat) (world : Verity.ContractState) :
    Option (Bool × Option (List UInt8) × List Nat × Verity.ContractState) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let tx : DenoteTransaction := { sender := 1, functionSelector := 0, args }
  let world' := withTransactionContext world tx
  let bindings ← bindExternalParams 0 fn.bindingParams args
  match executeBody oracle (effectiveFields imported.model) world' bindings fn.body imported.model.errors with
  | .ok r =>
      if r.success then
        some (true, none, decodeWords r.data, r.world)
      else
        some (false, some r.data, [], world)
  | .error _ => none

private def runSeq (steps : List (String × List Nat)) :
    Option (Bool × Option (List UInt8) × List Nat) := do
  let mut w := Verity.defaultState
  let mut last : Bool × Option (List UInt8) × List Nat := (true, none, [])
  for (name, args) in steps do
    let (ok, rev, out, w') ← callWorld name args w
    last := (ok, rev, out)
    if !ok then return last
    w := w'
  return last

-- Expected packed Entry words:
-- word 0: amount [0..127] | updatedAt [128..191] | tier [192..199] | frozen [200..207]
-- word 1: owner [0..159] | cap [160..255]
private def entryWord0 (amount updatedAt tier frozen : Nat) : Nat :=
  amount + updatedAt * (2 ^ 128) + tier * (2 ^ 192) + frozen * (2 ^ 200)

private def entryWord1 (owner cap : Nat) : Nat :=
  owner + cap * (2 ^ 160)

-- Direct write, direct read, inner row helper read, and raw double-Keccak sload match bit-for-bit.
#guard runSeq [
    ("writeDirectGrid", [11, 22, 1000, 500, 2, 1, 0xbeef, 7777]),
    ("readDirectGrid", [11, 22])
  ] == some (true, none, [1000, 500, 2, 1, 0xbeef, 7777])

#guard runSeq [
    ("writeDirectGrid", [11, 22, 1000, 500, 2, 1, 0xbeef, 7777]),
    ("readRowHelper", [11, 22])
  ] == some (true, none, [1000])

#guard runSeq [
    ("writeDirectGrid", [11, 22, 1000, 500, 2, 1, 0xbeef, 7777]),
    ("rawGridWords", [11, 22])
  ] == some (true, none, [entryWord0 1000 500 2 1, entryWord1 0xbeef 7777])

-- Distinct keys stay completely isolated.
#guard runSeq [
    ("writeDirectGrid", [11, 22, 1000, 500, 2, 1, 0xbeef, 7777]),
    ("readDirectGrid", [11, 23])
  ] == some (true, none, [0, 0, 0, 0, 0, 0])

-- Storage pointer binding freezes slot even when k1/k2 are mutated, updates without clobbering siblings.
#guard runSeq [
    ("writeDirectGrid", [3, 9, 100, 10, 1, 0, 0xcafe, 888]),
    ("updateViaPointer", [3, 9, 55, 20, 1]),
    ("readDirectGrid", [3, 9])
  ] == some (true, none, [155, 20, 1, 1, 0xcafe, 888])

-- Address-keyed 2D struct mapping whole-struct assignment, memory copy, and raw double-Keccak words.
#guard runSeq [
    ("writeAndReadAccount", [0x1234, 7, 900, 2, 0x5678, 321]),
    ("rawAccountWords", [0x1234, 7])
  ] == some (true, none, [entryWord0 900 42 2 1, entryWord1 0x5678 321])

-- Delete clears both packed words at the derived double-Keccak slot.
#guard runSeq [
    ("writeDirectGrid", [5, 6, 42, 7, 1, 1, 0xabcd, 99]),
    ("deleteGridEntry", [5, 6]),
    ("rawGridWords", [5, 6])
  ] == some (true, none, [0, 0])

-- Out-of-range enum ordinal (tierRaw = 3 >= 3) panics with Panic(0x21).
#guard runSeq [
    ("writeDirectGrid", [1, 2, 10, 20, 3, 0, 0x1, 1])
  ] == some (false, some (panicBytes 0x21), [])

end SolidityImportSmoke.RawSlotTwoDimStructMappingChecks
