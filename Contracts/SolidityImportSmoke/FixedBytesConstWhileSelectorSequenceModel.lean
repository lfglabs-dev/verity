import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.FixedBytesConstWhileSelectorSequenceModel

open Compiler.CompilationModel
open Compiler.CompilationModel.SolidityImport

solidity_profile microOsaka where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import imported from "Contracts/SolidityImportSmoke"
  entry "FixedBytesConstWhileSelectorSequence.sol"
  using microOsaka
  contract FixedBytesConstWhileSelectorFixture
  function PUBLIC_MASK()
  function maskOps(bytes16,uint256)
  function whileLoops(uint256,uint256,uint256,uint256,uint256)
  function encodeSelectors(bytes4,bytes,address,uint256)
  function read()

def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle

#guard imported.report.functions.length == 5
#guard imported.report.functions.all (·.denoteCovered)

-- Positive & revert Denote checks for `PUBLIC_MASK` and `maskOps` (`bytes16` constants & masks)
private def baseWorld : Verity.ContractState :=
  { Verity.defaultState with
    thisAddress := Verity.Core.Address.ofNat 0x1000
    sender := Verity.Core.Address.ofNat 0x2000
    chainId := Verity.Core.Uint256.ofNat 1 }

#guard runFunction oracle model "PUBLIC_MASK" baseWorld [] ==
  some [0x0102030405060708090a0b0c0d0e0f10 * 2 ^ 128]

-- Zero mask reverts (`ZeroMask()`).
#guard (runFunction oracle model "maskOps" baseWorld
  [("input", 0), ("shiftAmt", 4)]).isNone

-- Non-zero `bytes16` succeeds and returns a left-aligned `bytes16` word (low 128 bits zero).
#guard
  match runFunction oracle model "maskOps" baseWorld
      [("input", 0x0102030405060708090a0b0c0d0e0f10 * 2 ^ 128), ("shiftAmt", 4)] with
  | some [res] => res != 0 && res % (2 ^ 128) == 0
  | _ => false

-- Positive Denote check for `whileLoops` (`>`, `>=`, `<`, `<=`, unchecked `--`, helper `break`):
-- For x=16, start=1, stop=5, idx=6, limit=3:
--   s > 1 (>>=1): 4 steps -> +4
--   d >= 2 (/=2): 4 steps -> +40
--   b > 1 (&=b-1): 16 has 1 bit, 16>1 runs 1 iter -> b=0 -> +100
--   a < bound (1..4): 1+2+3+4 = 10 -> +10
--   p <= bound (1,3,5): 3 steps -> +3
--   cur >= limit (6,5,4,3): 6+5+4+3 = 18 -> +18
--   down > limit (6,5,4): 3 steps -> +3
--   _helperWhileBreak(16, 4): 4 steps -> +4
--   Total = 4 + 40 + 100 + 10 + 3 + 18 + 3 + 4 = 182
#guard
  runFunction oracle model "whileLoops" baseWorld
    [("x", 16), ("start", 1), ("endVal", 5), ("idx", 6), ("limit", 3)] == some [182]

-- Revert edge case: `while (cur >= limit)` with `limit = 0` panics with 0x11 on `cur -= 1`.
#guard (runFunction oracle model "whileLoops" baseWorld
  [("x", 16), ("start", 1), ("endVal", 5), ("idx", 2), ("limit", 0)]).isNone

end SolidityImportSmoke.FixedBytesConstWhileSelectorSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.FixedBytesConstWhileSelectorSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.FixedBytesConstWhileSelectorSequenceModel.model
        SolidityImportSmoke.FixedBytesConstWhileSelectorSequenceModel.oracle args
