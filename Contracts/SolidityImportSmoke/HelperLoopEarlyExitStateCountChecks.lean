import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.HelperLoopEarlyExitStateCountChecks
open Compiler.CompilationModel

/-! State-count invariance and positive Denote value checks for early `return` and
`break` in increasing helper `for` loops lowered onto `Stmt.forEachWhile` (#2916):
one-slot and two-slot contracts under both `viaIR := false` (legacy) and
`viaIR := true`, covering the five removed ≤256-cap shapes (`unconditionalReturn`,
`conditionalReturn`, `uint16BoundReturn`, `literal257Return`, `unboundedBreak`),
pre-declared counters, and the `#2916` `_contains(packed, n, id)` shape on `n = 0`,
first/middle/last matches, no match, and `uint256`-large bounds (`2^200`,
`2^256 - 1`) that exit early without running tail iterations. -/

solidity_import oneLegacy from "Contracts/SolidityImportSmoke"
  entry "HelperLoopEarlyExitOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract HelperLoopEarlyExitOneSlot
  function runContains(uint256,uint256,uint32)
  function runUnconditionalReturn(uint256)
  function runConditionalReturn(uint256)
  function runUint16BoundReturn(uint256)
  function runLiteral257Return(uint256)
  function runUnboundedBreak(uint256,uint256)
  function runPredeclaredReturn(uint256,uint256)

solidity_import oneIr from "Contracts/SolidityImportSmoke"
  entry "HelperLoopEarlyExitOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract HelperLoopEarlyExitOneSlot
  function runContains(uint256,uint256,uint32)
  function runUnconditionalReturn(uint256)
  function runConditionalReturn(uint256)
  function runUint16BoundReturn(uint256)
  function runLiteral257Return(uint256)
  function runUnboundedBreak(uint256,uint256)
  function runPredeclaredReturn(uint256,uint256)

solidity_import twoLegacy from "Contracts/SolidityImportSmoke"
  entry "HelperLoopEarlyExitTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract HelperLoopEarlyExitTwoSlots
  function runContains(uint256,uint256,uint32)
  function runUnconditionalReturn(uint256)
  function runConditionalReturn(uint256)
  function runUint16BoundReturn(uint256)
  function runLiteral257Return(uint256)
  function runUnboundedBreak(uint256,uint256)
  function runPredeclaredReturn(uint256,uint256)

solidity_import twoIr from "Contracts/SolidityImportSmoke"
  entry "HelperLoopEarlyExitTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract HelperLoopEarlyExitTwoSlots
  function runContains(uint256,uint256,uint32)
  function runUnconditionalReturn(uint256)
  function runConditionalReturn(uint256)
  function runUint16BoundReturn(uint256)
  function runLiteral257Return(uint256)
  function runUnboundedBreak(uint256,uint256)
  function runPredeclaredReturn(uint256,uint256)

private def body (model : CompilationModel) (name : String) : String :=
  match model.functions.find? (·.name == name) with
  | some f => (repr f.body).pretty 100000
  | none => ""

private def sameBody (one two : CompilationModel) (name : String) : Bool :=
  body one name != "" && body one name == body two name

private def returnsAll (name : String) (args : List Nat) (expected : Nat) : Bool :=
  [oneLegacy.model, oneIr.model, twoLegacy.model, twoIr.model].all fun model =>
    match model.functions.find? (·.name == name) with
    | some f =>
        let r := Denote.denoteFunction SolidityImport.Differential.oracle model f
          { sender := 1, functionSelector := 0, args } Verity.defaultState
        r.success && (r.returnWords == [expected] ||
          (r.returnWords.isEmpty && r.returnValue == some expected))
    | none => false

-- State-count invariance (1 state variable vs 2 state variables, legacy and via-IR).
#guard sameBody oneLegacy.model twoLegacy.model "runContains"
#guard sameBody oneLegacy.model twoLegacy.model "runUnconditionalReturn"
#guard sameBody oneLegacy.model twoLegacy.model "runConditionalReturn"
#guard sameBody oneLegacy.model twoLegacy.model "runUint16BoundReturn"
#guard sameBody oneLegacy.model twoLegacy.model "runLiteral257Return"
#guard sameBody oneLegacy.model twoLegacy.model "runUnboundedBreak"
#guard sameBody oneLegacy.model twoLegacy.model "runPredeclaredReturn"
#guard sameBody oneIr.model twoIr.model "runContains"
#guard sameBody oneIr.model twoIr.model "runUnconditionalReturn"
#guard sameBody oneIr.model twoIr.model "runConditionalReturn"
#guard sameBody oneIr.model twoIr.model "runUint16BoundReturn"
#guard sameBody oneIr.model twoIr.model "runLiteral257Return"
#guard sameBody oneIr.model twoIr.model "runUnboundedBreak"
#guard sameBody oneIr.model twoIr.model "runPredeclaredReturn"

-- Positive value checks for the five removed ≤256-cap shapes.
#guard returnsAll "runUnconditionalReturn" [0] 0
#guard returnsAll "runUnconditionalReturn" [1] 7
#guard returnsAll "runUnconditionalReturn" [2 ^ 200] 7

#guard returnsAll "runConditionalReturn" [0] 0
#guard returnsAll "runConditionalReturn" [1] 0
#guard returnsAll "runConditionalReturn" [2] 11
#guard returnsAll "runConditionalReturn" [2 ^ 200] 11

#guard returnsAll "runUint16BoundReturn" [260] 0
#guard returnsAll "runUint16BoundReturn" [261] 260
#guard returnsAll "runUint16BoundReturn" [65535] 260

#guard returnsAll "runLiteral257Return" [0] 1
#guard returnsAll "runLiteral257Return" [256] 257
#guard returnsAll "runLiteral257Return" [257] 0

#guard returnsAll "runUnboundedBreak" [0, 5] 0
#guard returnsAll "runUnboundedBreak" [300, 299] (299 * 1000 + 299)
#guard returnsAll "runUnboundedBreak" [300, 500] (300 * 1000 + 300)
#guard returnsAll "runUnboundedBreak" [2 ^ 200, 4] (4 * 1000 + 4)

#guard returnsAll "runPredeclaredReturn" [0, 5] 1000
#guard returnsAll "runPredeclaredReturn" [300, 299] 349
#guard returnsAll "runPredeclaredReturn" [300, 500] 1300
#guard returnsAll "runPredeclaredReturn" [2 ^ 200, 3] 53

-- #2916 `_contains(packed, n, id)` with side effects (`hits += 1`):
-- packed = [11, 22, 33, 44] in 32-bit lanes.
private def samplePacked : Nat := 11 + (22 <<< 32) + (33 <<< 64) + (44 <<< 96)

#guard returnsAll "runContains" [samplePacked, 0, 11] 0
#guard returnsAll "runContains" [samplePacked, 4, 11] 1001
#guard returnsAll "runContains" [samplePacked, 4, 33] 1003
#guard returnsAll "runContains" [samplePacked, 4, 44] 1004
#guard returnsAll "runContains" [samplePacked, 4, 99] 4
#guard returnsAll "runContains" [samplePacked, 2 ^ 200, 33] 1003
#guard returnsAll "runContains" [2 ^ 256 - 1, 2 ^ 256 - 1, 0] 1009

end SolidityImportSmoke.HelperLoopEarlyExitStateCountChecks
