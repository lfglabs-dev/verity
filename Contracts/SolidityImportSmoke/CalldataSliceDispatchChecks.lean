import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.CalldataSliceDispatchChecks
open Compiler.CompilationModel Denote

/-! Calldata-slice batch dispatch: a root `bytes[] calldata` parameter, a loop over the
items, the 4-byte selector extracted with `bytes4(items[i][:4])` or via a `bytes calldata`
local `bytes calldata item = items[i]; bytes4(item[:4])`, and the arguments decoded with
`abi.decode(item[4:], (...))`, dispatched with `if` / `else if` to internal handlers and a
revert on unknown selectors. Both via-IR and legacy pipelines are checked under Cancun. -/

solidity_profile irProfile where
  evmVersion := "cancun"
  viaIR := true
  optimizerRuns := some 10
  bytecodeHash := "none"

solidity_profile legacyProfile where
  evmVersion := "cancun"
  viaIR := false
  optimizerRuns := some 10
  bytecodeHash := "none"

solidity_import ir from "Contracts/SolidityImportSmoke" entry "CalldataSliceDispatchSmoke.sol"
  using irProfile
  contract CalldataSliceDispatchSmoke
  function batch(«bytes[]»)
  function batchLocal(«bytes[]»)
  function batchDirectDecode(«bytes[]»)
  function addPair(uint256,uint256)
  function touchOne(address,uint256)
  function scaleOne(uint256,uint32)

solidity_import legacy from "Contracts/SolidityImportSmoke" entry "CalldataSliceDispatchSmoke.sol"
  using legacyProfile
  contract CalldataSliceDispatchSmoke
  function batch(«bytes[]»)
  function batchLocal(«bytes[]»)
  function batchDirectDecode(«bytes[]»)
  function addPair(uint256,uint256)
  function touchOne(address,uint256)
  function scaleOne(uint256,uint32)

private def oracle := SolidityImport.Differential.oracle

/-- Success, return words or revert bytes, `total` (slot 0) and `lastWho` (slot 1) after
one call from a world with both slots seeded. -/
private def observe (model : CompilationModel) (name : String) (args : List Nat)
    (seedTotal seedWho : Nat) :
    Option (Bool × List Nat × Option (List UInt8) × Nat × Nat) := do
  let fn ← model.functions.find? (·.name == name)
  let world := (Verity.defaultState.writePhysicalSlot 0 (.ofNat seedTotal)).writePhysicalSlot 1
    (.ofNat seedWho)
  let r := denoteFunction oracle model fn { sender := 0, functionSelector := 0, args } world
  return (r.success, r.returnWords, r.revertData, r.finalStorage 0, r.finalStorage 1)

/-- The 32 big-endian bytes of one ABI word. -/
private def wordBytes (x : Nat) : List Nat :=
  (List.range 32).map fun k => (x / 2 ^ (8 * (31 - k))) % 256

/-- The big-endian words of a byte string padded to a word boundary. -/
private def toWords (bytes : List Nat) : List Nat :=
  let padded := bytes ++ List.replicate ((32 - bytes.length % 32) % 32) 0
  (List.range (padded.length / 32)).map fun k =>
    (List.range 32).foldl (fun acc j => acc * 256 + padded.getD (32 * k + j) 0) 0

/-- One `bytes` item: the 4 selector bytes followed by the encoded argument words. -/
private def itemBytes (selector : Nat) (argWords : List Nat) : List Nat :=
  ((List.range 4).map fun k => (selector / 2 ^ (8 * (3 - k))) % 256) ++ argWords.flatMap wordBytes

/-- The raw calldata words (after the selector) of `batch(bytes[])`: one head offset
word, the array length, the relative element offsets, and each element's length word
followed by its padded data words. -/
private def batchArgs (items : List (List Nat)) : List Nat :=
  let encoded := items.map (fun item => item.length :: toWords item)
  let sizes := encoded.map (·.length)
  let n := items.length
  [32, n] ++ ((List.range n).map fun k =>
    32 * n + 32 * ((sizes.take k).foldl (· + ·) 0)) ++ encoded.foldl (· ++ ·) []

private def sel (name : String) : Nat := (KeccakEngine.keccak256_selector name).toNat

private def addPairItem (a b : Nat) : List Nat :=
  itemBytes (sel "addPair(uint256,uint256)") [a, b]
private def touchOneItem (who amount : Nat) : List Nat :=
  itemBytes (sel "touchOne(address,uint256)") [who, amount]
private def scaleOneItem (x factor : Nat) : List Nat :=
  itemBytes (sel "scaleOne(uint256,uint32)") [x, factor]
private def unknownItem : List Nat := itemBytes 0xdeadbeef [0, 0]

private def errorUnknownSelector : List UInt8 :=
  [0x08, 0xc3, 0x79, 0xa0] ++ (List.replicate 31 0 ++ [0x20]) ++ (List.replicate 31 0 ++ [16]) ++
    "unknown selector".toUTF8.toList ++ List.replicate 16 0
private def errorShort : List UInt8 :=
  [0x08, 0xc3, 0x79, 0xa0] ++ (List.replicate 31 0 ++ [0x20]) ++ (List.replicate 31 0 ++ [5]) ++
    "short".toUTF8.toList ++ List.replicate 27 0

private def bothModels (check : CompilationModel → Bool) : Bool :=
  check ir.model && check legacy.model

private def bothBatchForms (args : List Nat) (seedTotal seedWho : Nat)
    (expected : Option (Bool × List Nat × Option (List UInt8) × Nat × Nat)) : Bool :=
  bothModels fun m =>
    observe m "batch" args seedTotal seedWho == expected &&
    observe m "batchLocal" args seedTotal seedWho == expected

-- Each handler called directly: the sum lands in `total`, the address in `lastWho`
-- and the pure multiply returns without touching storage.
#guard bothModels fun m => observe m "addPair" [3, 4] 100 7 ==
  some (true, [7], none, 107, 7)
#guard bothModels fun m => observe m "touchOne" [0xabc, 5] 100 7 ==
  some (true, [5], none, 105, 0xabc)
#guard bothModels fun m => observe m "scaleOne" [6, 10] 100 7 ==
  some (true, [60], none, 100, 7)

-- Both `batch` (direct `items[i][:4]`) and `batchLocal` (`bytes calldata item = items[i]`)
-- dispatch each item's 4-byte selector, sum the handler results and apply storage writes.
#guard bothBatchForms (batchArgs [addPairItem 3 4, touchOneItem 0xabc 5, scaleOneItem 6 10])
  100 7 (some (true, [72], none, 112, 0xabc))
#guard bothBatchForms (batchArgs [addPairItem 3 4])
  0 0 (some (true, [7], none, 7, 0))

-- An empty batch succeeds with a zero sum and leaves the storage untouched.
#guard bothBatchForms (batchArgs []) 100 7 (some (true, [0], none, 100, 7))

-- An unknown selector reverts after earlier writes roll back, and a short item fails
-- the length check before dispatch (rolling back any preceding items).
#guard bothBatchForms (batchArgs [addPairItem 3 4, unknownItem])
  100 7 (some (false, [], some errorUnknownSelector, 100, 7))
#guard bothBatchForms (batchArgs [[0xde, 0xad, 0xbe]])
  100 7 (some (false, [], some errorShort, 100, 7))
#guard bothBatchForms (batchArgs [addPairItem 3 4, [0x12, 0x34]])
  100 7 (some (false, [], some errorShort, 100, 7))

-- Unaligned item payloads keep subsequent element offsets on the padded word boundary.
#guard bothBatchForms (batchArgs [scaleOneItem 2 8, touchOneItem 0xabc 1, scaleOneItem 100 3])
  0 0 (some (true, [317], none, 1, 0xabc))

-- Direct `abi.decode(items[i], (...))` on `bytes[] calldata` elements.
#guard bothModels fun m =>
  observe m "batchDirectDecode"
    (batchArgs [wordBytes 3 ++ wordBytes 4, wordBytes 10 ++ wordBytes 20])
    100 7 == some (true, [37], none, 137, 7)

-- Reassigning a `bytes calldata` local stays rejected (fail closed).
/--
error: CalldataSliceDispatchSmoke.sol:90:9: VariableDeclaration: [solidity-import:unsupported] reassigned calldata bytes locals are outside this slice
closure: CalldataSliceDispatchUnsupported.reassignLocal
bytes calldata item
-/
#guard_msgs in
solidity_import unsupportedReassign from "Contracts/SolidityImportSmoke" entry "CalldataSliceDispatchSmoke.sol"
  using irProfile
  contract CalldataSliceDispatchUnsupported
  function reassignLocal(«bytes[]»)

-- Both imported models compile cleanly for Cancun and Osaka.
#guard (Compiler.CompilationModel.compile ir.model [1, 2, 3, 4, 5, 6] .cancun).isOk
#guard (Compiler.CompilationModel.compile legacy.model [1, 2, 3, 4, 5, 6] .osaka).isOk

end SolidityImportSmoke.CalldataSliceDispatchChecks
