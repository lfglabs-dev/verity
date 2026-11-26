import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.HelperLoopAndWhileExtChecks
open Compiler.CompilationModel Denote

solidity_profile extLoopProfile where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import imported from "Contracts/SolidityImportSmoke" entry "HelperLoopAndWhileExt.sol"
  using extLoopProfile
  contract HelperLoopAndWhileExt
  function scanWords(«uint256[]»,uint256,uint8,uint256)
  function scanBitmapRange(uint256,uint8,uint8)
  function scanDivisible(uint256,uint8,uint256)
  function voidBoundedScan(uint256,uint8,uint256)
  function whileUncheckedDecNeqZero(uint256)
  function whileUncheckedInc(uint256,uint256)
  function whileBoolHelperUncheckedDec(uint256)
  function whileLibHasBits(uint256)
  function whileRangeIter(uint256,uint256)
  function whileMaskIter(uint256)
  function whileComplexHelperCheckedDec(uint256)
  function whileHelperEarlyReturn(uint8,uint8)

#guard imported.report.functions.length == 12
#guard imported.report.functions.all (·.denoteCovered)

private def oracle := SolidityImport.Differential.oracle

private def run (name : String) (args : List Nat) :
    Option (Bool × Option (List UInt8) × List Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let r := denoteFunction oracle imported.model fn
    { sender := 1, functionSelector := 0, args } Verity.defaultState
  let words := if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords
  return (r.success, r.revertData, words)

-- Helper for-loop early return with uint256 bound & non-zero start over memory array.
-- ABI head: [offset=128, start, bound, target, len, w0, w1, w2, w3, w4]
#guard run "scanWords" [128, 1, 5, 40, 5, 10, 20, 30, 40, 50] == some (true, none, [3])
#guard run "scanWords" [128, 2, 5, 10, 5, 10, 20, 30, 40, 50] == some (true, none, [2^256 - 1])
-- Out-of-bounds index triggers Panic(0x32).
#guard run "scanWords" [128, 1, 6, 99, 5, 10, 20, 30, 40, 50] == some (false, some (panicBytes 0x32), [])

-- Multi-return bitmap scan helper with computed uint8 bound `startBit + count`.
-- bitmap = 0b1010000 (bits 4 and 6 set)
#guard run "scanBitmapRange" [80, 2, 6] == some (true, none, [1, 4])
#guard run "scanBitmapRange" [80, 5, 3] == some (true, none, [1, 6])
#guard run "scanBitmapRange" [80, 7, 4] == some (true, none, [0, 0])
-- Overflow on `uint8(startBit + count)` triggers Panic(0x11).
#guard run "scanBitmapRange" [80, 250, 10] == some (false, some (panicBytes 0x11), [])

-- Helper for-loop with empty loopExpression and `unchecked { ++i; }` body step.
#guard run "scanDivisible" [10, 20, 7] == some (true, none, [14])
#guard run "scanDivisible" [15, 20, 7] == some (true, none, [0])

-- Void helper for-loop with uint8 bound & non-zero start early return.
#guard run "voidBoundedScan" [2, 10, 4] == some (true, none, [9, 0])
#guard run "voidBoundedScan" [2, 6, 99] == some (true, none, [14, 1])

-- `while (remaining != 0) { unchecked { acc += remaining; --remaining; } }`
#guard run "whileUncheckedDecNeqZero" [5] == some (true, none, [15])
#guard run "whileUncheckedDecNeqZero" [0] == some (true, none, [0])

-- `while (i < limit) { ... unchecked { ++i; } }`
#guard run "whileUncheckedInc" [3, 7] == some (true, none, [18])
#guard run "whileUncheckedInc" [7, 3] == some (true, none, [0])

-- Internal boolean helper call in while condition + `unchecked { --remaining; }`
#guard run "whileBoolHelperUncheckedDec" [6] == some (true, none, [21])
#guard run "whileBoolHelperUncheckedDec" [0] == some (true, none, [0])

-- Library boolean helper (`mask.hasBits()`) + bit-clearing step
#guard run "whileLibHasBits" [0b101101] == some (true, none, [4])
#guard run "whileLibHasBits" [0] == some (true, none, [0])

-- Struct iterator `it.hasNextRange()` + `unchecked { ++it.cursor; }`
#guard run "whileRangeIter" [4, 8] == some (true, none, [22])
#guard run "whileRangeIter" [8, 4] == some (true, none, [0])

-- Struct bitmap iterator `it.hasNextMask()` + `it.mask &= it.mask - 1`
#guard run "whileMaskIter" [0x105] == some (true, none, [3])
#guard run "whileMaskIter" [0] == some (true, none, [0])

-- Complex boolean helper (stops at 2 because 2 is even and not > 2) with checked `--remaining`.
-- 5 -> 4 -> 3 -> stops at 2 => 5 + 4 + 3 = 12; for 1: 1 -> stops at 0 => 1.
#guard run "whileComplexHelperCheckedDec" [5] == some (true, none, [12])
#guard run "whileComplexHelperCheckedDec" [1] == some (true, none, [1])
#guard run "whileComplexHelperCheckedDec" [0] == some (true, none, [0])

-- Helper `while (_hasRemaining8(remaining))` with early return + `unchecked { --remaining; }`.
-- remaining=5, want=3: 5 (acc=5), 4 (acc=9), 3 (acc=12 -> return 123).
#guard run "whileHelperEarlyReturn" [5, 3] == some (true, none, [123])
#guard run "whileHelperEarlyReturn" [5, 99] == some (true, none, [15])

-- `Stmt.forEachWhile` (#2916): unbounded uint256 helper `for` early return exits immediately
-- without no-op tail iterations (even at bound = 2^256 - 1).
solidity_import unboundedForEarlyExit from "Contracts/SolidityImportSmoke" entry "HelperLoopAndWhileExt.sol"
  using extLoopProfile
  contract HelperLoopAndWhileExt
  function scanUnboundedForRejected(uint256,uint256,uint256)

#guard
  match unboundedForEarlyExit.model.functions.find? (·.name == "scanUnboundedForRejected") with
  | some fn =>
      let r := denoteFunction oracle unboundedForEarlyExit.model fn
        { sender := 1, functionSelector := 0, args := [0, 2^256 - 1, 1] } Verity.defaultState
      let words := if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords
      r.success && r.revertData == none && words == [0]
  | none => false

-- Fail-closed control: unbounded uint256 helper `while` early return stays rejected.
/--
error: HelperLoopAndWhileExt.sol:150:9: WhileStatement: [solidity-import:unsupported] return in a helper while loop requires a bounded loop of at most 256 iterations
closure: HelperLoopAndWhileExt.whileHelperUnboundedReturnRejected -> HelperLoopAndWhileExt._helperWhileFindUnbounded
while (_hasRemaining(remaining)) {
            acc += remaining;
            if (remaining == want) {
                re
-/
#guard_msgs in
solidity_import unboundedWhileRejected from "Contracts/SolidityImportSmoke" entry "HelperLoopAndWhileExt.sol"
  using extLoopProfile
  contract HelperLoopAndWhileExt
  function whileHelperUnboundedReturnRejected(uint256,uint256)

end SolidityImportSmoke.HelperLoopAndWhileExtChecks
