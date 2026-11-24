import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.LoopBoundsAndHelperReturnChecks
open Compiler.CompilationModel Denote

solidity_profile loopProfile where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import imported from "Contracts/SolidityImportSmoke" entry "LoopBoundsAndHelperReturn.sol"
  using loopProfile
  contract LoopBoundsAndHelperReturn
  function sumRange(uint256,uint256)
  function sumFromConst(uint256)
  function sumFromExpr(uint256,uint256)
  function predeclaredRange(uint256,uint256)
  function narrowStartWrap(uint8,uint256)
  function sumDown(uint256,uint256)
  function helperDecrementReturn(uint8,uint256)
  function helperNonZeroControl(uint8,uint256,uint256,uint256)
  function helperNestedReturn(uint8,uint256)
  function helperWhileReturn(uint256,uint256)
  function helperWhileTrueReturn(uint256,uint256)
  function voidForEarlyReturn(uint8,uint256)
  function voidWhileEarlyReturn(uint256,uint256)

private def oracle := SolidityImport.Differential.oracle

private def run (name : String) (args : List Nat) :
    Option (Bool × Option (List UInt8) × List Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let r := denoteFunction oracle imported.model fn { sender := 1, functionSelector := 0, args }
    Verity.defaultState
  let words := if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords
  return (r.success, r.revertData, words)

-- Non-zero variable, constant, and computed start bounds (including empty start >= end).
#guard run "sumRange" [3, 7] == some (true, none, [18])
#guard run "sumRange" [7, 7] == some (true, none, [0])
#guard run "sumRange" [9, 4] == some (true, none, [0])
#guard run "sumFromConst" [6] == some (true, none, [14])
#guard run "sumFromConst" [2] == some (true, none, [0])
#guard run "sumFromExpr" [2, 6] == some (true, none, [12])

-- Pre-declared counter with non-zero start preserves exact exit counter value.
#guard run "predeclaredRange" [2, 6] == some (true, none, [14, 6])
#guard run "predeclaredRange" [6, 3] == some (true, none, [0, 6])

-- Narrow uint8 counter with non-zero start panics 0x11 when end >= 256, succeeds below.
#guard run "narrowStartWrap" [250, 255] == some (true, none, [1260])
#guard run "narrowStartWrap" [250, 256] == some (false, some (panicBytes 0x11), [])
#guard run "narrowStartWrap" [255, 256] == some (false, some (panicBytes 0x11), [])
#guard run "narrowStartWrap" [250, 200] == some (true, none, [0])

-- Decrementing loop & early return inside decrementing helper loop.
#guard run "sumDown" [5, 2] == some (true, none, [12])
#guard run "sumDown" [2, 5] == some (true, none, [0])
#guard run "helperDecrementReturn" [5, 3] == some (true, none, [30])
#guard run "helperDecrementReturn" [5, 9] == some (true, none, [999])

-- Early return, continue, and break in a non-zero-start helper for loop.
-- limit=7, skip=2, stopAt=5, pick=4: i=1 (acc=1), i=2 (skip), i=3 (acc=4), i=4 (return 4+400=404).
#guard run "helperNonZeroControl" [7, 2, 5, 4] == some (true, none, [404])
-- limit=7, skip=2, stopAt=4, pick=6: i=1 (acc=1), i=2 (skip), i=3 (acc=4), i=4 (break) -> 4.
#guard run "helperNonZeroControl" [7, 2, 4, 6] == some (true, none, [4])
-- limit=5, skip=9, stopAt=9, pick=9: i=1..4 -> acc=10.
#guard run "helperNonZeroControl" [5, 9, 9, 9] == some (true, none, [10])

-- Early return inside nested helper for loops.
-- rows=4 => i in {1,2,3}, j in {0,1,2,3}; want=21 hits at visited=6 -> 6021.
#guard run "helperNestedReturn" [4, 21] == some (true, none, [6021])
#guard run "helperNestedReturn" [4, 99] == some (true, none, [12])

-- Early return inside helper while & while(true) loops.
-- v=0b1101 (13): step1 v=13, step2 v=6 -> hit stopStep=2 -> 206.
#guard run "helperWhileReturn" [13, 2] == some (true, none, [206])
-- stopStep=99 never hits: 4 steps + 10 = 14.
#guard run "helperWhileReturn" [13, 99] == some (true, none, [14])
#guard run "helperWhileTrueReturn" [13, 2] == some (true, none, [106])
#guard run "helperWhileTrueReturn" [13, 99] == some (true, none, [4])

-- Void helper for/while loops with early return skipping tailMarks += 1.
#guard run "voidForEarlyReturn" [6, 3] == some (true, none, [6, 0])
#guard run "voidForEarlyReturn" [6, 99] == some (true, none, [15, 1])
#guard run "voidWhileEarlyReturn" [13, 2] == some (true, none, [3, 0])
#guard run "voidWhileEarlyReturn" [13, 99] == some (true, none, [10, 1])

end SolidityImportSmoke.LoopBoundsAndHelperReturnChecks
