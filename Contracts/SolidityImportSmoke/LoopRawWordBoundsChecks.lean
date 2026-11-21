import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-! Loop trip counts and counters observed through raw narrow stack words, in both solc
pipelines. Expected values were executed with solc 0.8.34 (Osaka, optimizer runs 466) on
Anvil, legacy and via-IR alike. -/

namespace SolidityImportSmoke.LoopRawWordBoundsChecks
open Compiler.CompilationModel

solidity_import legacy from "Contracts/SolidityImportSmoke" entry "LoopRawWordBounds.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract LoopRawWordBounds
  function signedWidenedBound(uint256)
  function narrowDecrementRawRead(uint256)
  function tailWindowNarrowBreak(uint256)

solidity_import ir from "Contracts/SolidityImportSmoke" entry "LoopRawWordBounds.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract LoopRawWordBounds
  function signedWidenedBound(uint256)
  function narrowDecrementRawRead(uint256)
  function tailWindowNarrowBreak(uint256)

private def run (model : CompilationModel) (name : String) (args : List Nat) :
    Option (Bool × List Nat) :=
  (model.functions.find? (·.name == name)).map fun f =>
    let r := Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args } Verity.defaultState
    (r.success, r.returnWords)

private def observes (name : String) (args : List Nat) (n : Nat) : Bool :=
  [legacy.model, ir.model].all fun m => run m name args == some (true, [n])

private def reverts (name : String) (args : List Nat) : Bool :=
  [legacy.model, ir.model].all fun m => (run m name args).map (·.1) == some false

-- `int8` raw 257 sign-extends to 1, raw 258 to 2: the pre-declared counter exits there.
#guard observes "signedWidenedBound" [0] 0
#guard observes "signedWidenedBound" [3] 3
#guard observes "signedWidenedBound" [257] 1
#guard observes "signedWidenedBound" [258] 2
-- The range uses the cleaned start, but Yul reads the counter's raw first-iteration word.
#guard observes "narrowDecrementRawRead" [0] 0
#guard observes "narrowDecrementRawRead" [3] 1
#guard observes "narrowDecrementRawRead" [257] 257
#guard observes "narrowDecrementRawRead" [258] 1
-- `n - 1` underflows for a clean zero; raw 257 is the bound 1, so the window is `[0, 1)`.
#guard reverts "tailWindowNarrowBreak" [0]
#guard observes "tailWindowNarrowBreak" [1] 10
#guard observes "tailWindowNarrowBreak" [3] 20
#guard observes "tailWindowNarrowBreak" [257] 10
#guard observes "tailWindowNarrowBreak" [258] 20

end SolidityImportSmoke.LoopRawWordBoundsChecks
