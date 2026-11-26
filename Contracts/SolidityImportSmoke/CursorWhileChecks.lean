import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.Transactions

/-!
Synthetic smoke checks for bounded `while` loops over a memory struct cursor:
- `while (ScanIterLib.hasMore(iter))` with pure library boolean helper condition over a memory struct cursor
- By-reference cursor mutation via `ScanIterLib.next(arr, iter)` across >8 packed 32-bit items
  (exercising multi-slot rollover `c.idx % 8 == 0` across `uint256[64] storage arr`)
- `using ScanIterLib for ScanIter` syntax (`iter.hasMore()`)
- Struct-member fixed storage array (`bucket.words`)
- External staticcall per cursor item (`IItemOracle(oracle).score(item)`) with value + boolean flag accumulation.
-/
namespace SolidityImportSmoke.CursorWhileChecks
open Compiler.CompilationModel Denote ByteExternalCall
open Compiler.CompilationModel.SolidityImport.Transactions

solidity_profile cursorWhileProfile where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import imported from "Contracts/SolidityImportSmoke" entry "CursorWhileFixture.sol"
  using cursorWhileProfile
  contract CursorWhileFixture
  function pushItem(uint32)
  function pushBucketItem(uint32)
  function resetItems()
  function sumPackedLocal()
  function sumPackedUsingFor()
  function sumBucketLocal()
  function scanPackedWithOracle(address)
  function scanNestedNamedArgs(uint256,address)

#guard imported.report.functions.length == 8
#guard imported.report.functions.all (·.denoteCovered)

private def selfAddr : Nat := 0xc0de
private def oddOracle : Nat := 0xa1
private def evenOnBigOracle : Nat := 0xa2

private def calldataArg0 (calldata : List UInt8) : Nat :=
  (List.range 32).foldl (fun acc lane => acc * 256 + (calldata.getD (4 + lane) 0).toNat) 0

private def respond (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if request.kind != .staticcall || request.value != 0 then .revert [] []
  else if request.target == oddOracle then
    let item := calldataArg0 request.calldata
    -- Always odd: `2 * item + 1`
    .success world (wordBytes (2 * item + 1)) []
  else if request.target == evenOnBigOracle then
    let item := calldataArg0 request.calldata
    -- Even when item >= 100 (hit after slot rollover!), odd otherwise
    let score := if item ≥ 100 then 2 * item else 2 * item + 1
    .success world (wordBytes score) []
  else .success world [] []

private def env : ByteCallEnvironment :=
  { gas := some 1000000
    adversary := some
      { respond
        valid := by
          intro request world
          unfold respond
          by_cases h1 : (request.kind != .staticcall || request.value != 0) = true
          · simp [h1, Response.valid]
          · simp only [h1, Bool.false_eq_true, ↓reduceIte]
            by_cases h2 : (request.target == oddOracle) = true
            · simp [h2, Response.valid]
            · simp only [h2, Bool.false_eq_true, ↓reduceIte]
              by_cases h3 : (request.target == evenOnBigOracle) = true <;>
                simp [h3, Response.valid] } }

private def step (world : Verity.ContractState) (name : String) (args : List Nat) :
    Option (Bool × List UInt8 × Verity.ContractState) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let tx : DenoteTransaction := { sender := 0x5e, thisAddress := selfAddr, functionSelector := 0, args }
  let prepared := withTransactionContext world tx
  let bindings ← bindExternalParams 0 fn.bindingParams args
  match executeBody SolidityImport.Differential.oracle (effectiveFields imported.model) prepared
      bindings fn.body imported.model.errors env with
  | .ok r => some (r.success, r.data, r.world)
  | .error _ => none

private def pushAll (world : Verity.ContractState) (fnName : String) (items : List Nat) :
    Option Verity.ContractState :=
  items.foldlM (fun w x => do
    let (ok, _, w') ← step w fnName [x]
    if ok then some w' else none) world

-- 0 items: cursor loop executes 0 iterations cleanly.
#guard (do
  let (ok1, d1, _) ← step Verity.defaultState "sumPackedLocal" []
  let (ok2, d2, _) ← step Verity.defaultState "sumPackedUsingFor" []
  let (ok3, d3, _) ← step Verity.defaultState "scanPackedWithOracle" [oddOracle]
  return (ok1, d1 == wordBytes 0, ok2, d2 == wordBytes 0 ++ wordBytes 0,
          ok3, d3 == wordBytes 0 ++ wordBytes 1)) ==
  some (true, true, true, true, true, true)

-- 11 items (crosses slot rollover at idx == 8):
-- items = [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110], sum = 660
-- weighted sum (using-for): sum_{k=1..11} (10*k)*k = 10 * (11*12*23/6) = 5060
-- oddOracle total: sum(2*x + 1) = 2*660 + 11 = 1331, allOdd = true
-- evenOnBigOracle total: items 100 & 110 (indices 9 & 10, AFTER rollover!) are even -> 2*660 + 9 = 1329, allOdd = false
#guard (do
  let items := [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110]
  let w ← pushAll Verity.defaultState "pushItem" items
  let (ok1, d1, _) ← step w "sumPackedLocal" []
  let (ok2, d2, _) ← step w "sumPackedUsingFor" []
  let (ok3, d3, _) ← step w "scanPackedWithOracle" [oddOracle]
  let (ok4, d4, _) ← step w "scanPackedWithOracle" [evenOnBigOracle]
  return (ok1, d1 == wordBytes 660,
          ok2, d2 == wordBytes 5060 ++ wordBytes 11,
          ok3, d3 == wordBytes 1331 ++ wordBytes 1,
          ok4, d4 == wordBytes 1329 ++ wordBytes 0)) ==
  some (true, true, true, true, true, true, true, true)

-- 19 items (crosses TWO slot rollovers at idx == 8 and idx == 16) in struct-member fixed array `bucket.words`:
-- items = [1..19], sum = 190
#guard (do
  let items := (List.range 19).map (· + 1)
  let w ← pushAll Verity.defaultState "pushBucketItem" items
  let (ok, d, _) ← step w "sumBucketLocal" []
  return (ok, d == wordBytes 190)) ==
  some (true, true)

-- Cursor step nested in a named-argument call `ReaderLib.readItem({groupId: gid, itemId: ScanIterLib.next(arr, iter), account: user})`:
-- 0 items: total = 0, allOk = true;
-- 8 items [10..80] (gid=7, user=0x1234 -> tag=0x34=52): total = (360 + 56)*3 + 8*52 = 1664, allOk = true;
-- 11 items [10..110] (crosses rollover at idx == 8; items 100 & 110 >= 100 flip allOk -> false):
-- total = (660 + 77)*3 + 11*52 = 2783, allOk = false.
#guard (do
  let (ok0, d0, _) ← step Verity.defaultState "scanNestedNamedArgs" [7, 0x1234]
  let w8 ← pushAll Verity.defaultState "pushItem" [10, 20, 30, 40, 50, 60, 70, 80]
  let (ok8, d8, _) ← step w8 "scanNestedNamedArgs" [7, 0x1234]
  let w11 ← pushAll w8 "pushItem" [90, 100, 110]
  let (ok11, d11, _) ← step w11 "scanNestedNamedArgs" [7, 0x1234]
  return (ok0, d0 == wordBytes 0 ++ wordBytes 1,
          ok8, d8 == wordBytes 1664 ++ wordBytes 1,
          ok11, d11 == wordBytes 2783 ++ wordBytes 0)) ==
  some (true, true, true, true, true, true)

-- Negative controls for cursor-step soundness: short-circuiting step, sibling cursor read, and double step
-- must all fail closed instead of synthesizing a bounded cursor loop.
/--
error: CursorWhileFixture.sol:197:16: FunctionCall: [solidity-import:unsupported] a while loop condition must compare a loop variable against zero
closure: CursorWhileFixture.badShortCircuitStep
ScanIterLib.hasMore(iter)
-/
#guard_msgs in
solidity_import rejectShortCircuitStep from "Contracts/SolidityImportSmoke" entry "CursorWhileFixture.sol"
  using cursorWhileProfile
  contract CursorWhileFixture
  function badShortCircuitStep(bool)

/--
error: CursorWhileFixture.sol:210:16: FunctionCall: [solidity-import:unsupported] a while loop condition must compare a loop variable against zero
closure: CursorWhileFixture.badSiblingCursorRead
ScanIterLib.hasMore(iter)
-/
#guard_msgs in
solidity_import rejectSiblingCursorRead from "Contracts/SolidityImportSmoke" entry "CursorWhileFixture.sol"
  using cursorWhileProfile
  contract CursorWhileFixture
  function badSiblingCursorRead()

/--
error: CursorWhileFixture.sol:219:16: FunctionCall: [solidity-import:unsupported] a while loop condition must compare a loop variable against zero
closure: CursorWhileFixture.badDoubleStep
ScanIterLib.hasMore(iter)
-/
#guard_msgs in
solidity_import rejectDoubleStep from "Contracts/SolidityImportSmoke" entry "CursorWhileFixture.sol"
  using cursorWhileProfile
  contract CursorWhileFixture
  function badDoubleStep()

-- A cursor step nested in a typed external-call argument is hoisted and admitted cleanly
-- now that effectful helper arguments on typed external calls are supported.
solidity_import nestedExternalCallArg from "Contracts/SolidityImportSmoke" entry "CursorWhileFixture.sol"
  using cursorWhileProfile
  contract CursorWhileFixture
  function scanNestedOracleCall(address)

#guard nestedExternalCallArg.report.functions.length == 1
#guard nestedExternalCallArg.report.functions.all (·.denoteCovered)

end SolidityImportSmoke.CursorWhileChecks
