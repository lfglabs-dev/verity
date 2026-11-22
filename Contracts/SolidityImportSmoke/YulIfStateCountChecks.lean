import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.YulIfStateCountChecks
open Compiler.CompilationModel

solidity_import oneLegacy from "Contracts/SolidityImportSmoke" entry "YulIfOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract YulIfOneSlot
  function clamp(uint256)
  function guarded(uint256)
  function selectorRevert(uint256)
  function nested(uint256)
  function boolCondition(uint256)

solidity_import twoLegacy from "Contracts/SolidityImportSmoke" entry "YulIfTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract YulIfTwoSlots
  function clamp(uint256)
  function guarded(uint256)
  function selectorRevert(uint256)
  function nested(uint256)
  function boolCondition(uint256)

solidity_import oneIr from "Contracts/SolidityImportSmoke" entry "YulIfOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract YulIfOneSlot
  function clamp(uint256)
  function guarded(uint256)
  function selectorRevert(uint256)
  function nested(uint256)
  function boolCondition(uint256)

solidity_import twoIr from "Contracts/SolidityImportSmoke" entry "YulIfTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract YulIfTwoSlots
  function clamp(uint256)
  function guarded(uint256)
  function selectorRevert(uint256)
  function nested(uint256)
  function boolCondition(uint256)

private def body (model : CompilationModel) (name : String) : String :=
  match model.functions.find? (·.name == name) with
  | some f => (repr f.body).pretty 100000
  | none => ""

/-- The function imports and its body does not depend on the unrelated slot. -/
private def sameBody (one two : CompilationModel) (name : String) : Bool :=
  body one name != "" && body one name == body two name

private def run (model : CompilationModel) (name : String) (x : Nat) : Option Denote.DenoteResult :=
  (model.functions.find? (·.name == name)).map fun f =>
    Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args := [x] } Verity.defaultState

/-- solc 0.8.34 on Anvil (osaka, runs 466), both pipelines and both contracts:
clamp(5) = 5, clamp(50) = 10, guarded(100) = 101, selectorRevert(8) = 8, nested(0) = 0,
nested(4) = 0, nested(5) = 6, boolCondition(5) = 7. -/
private def returns (model : CompilationModel) (name : String) (x n : Nat) : Bool :=
  match run model name x with
  | some r => r.success && (r.returnWords == [n] || (r.returnWords.isEmpty && r.returnValue == some n))
  | none => false

/-- solc 0.8.34 on Anvil: guarded(101) reverts with empty data, selectorRevert(7) with 0xdeadbeef. -/
private def reverts (model : CompilationModel) (name : String) (x : Nat) (data : List UInt8) : Bool :=
  match run model name x with
  | some r => !r.success && r.revertData == some data
  | none => false

#guard sameBody oneLegacy.model twoLegacy.model "clamp"
#guard sameBody oneLegacy.model twoLegacy.model "guarded"
#guard sameBody oneLegacy.model twoLegacy.model "selectorRevert"
#guard sameBody oneLegacy.model twoLegacy.model "nested"
#guard sameBody oneLegacy.model twoLegacy.model "boolCondition"
#guard sameBody oneIr.model twoIr.model "clamp"
#guard sameBody oneIr.model twoIr.model "guarded"
#guard sameBody oneIr.model twoIr.model "selectorRevert"
#guard sameBody oneIr.model twoIr.model "nested"
#guard sameBody oneIr.model twoIr.model "boolCondition"
#guard returns oneLegacy.model "clamp" 5 5
#guard returns oneLegacy.model "clamp" 50 10
#guard returns oneLegacy.model "guarded" 100 101
#guard returns oneLegacy.model "selectorRevert" 8 8
#guard returns oneLegacy.model "nested" 0 0
#guard returns oneLegacy.model "nested" 4 0
#guard returns oneLegacy.model "nested" 5 6
#guard returns oneLegacy.model "boolCondition" 5 7
#guard reverts oneLegacy.model "guarded" 101 []
#guard reverts oneLegacy.model "selectorRevert" 7 [0xde, 0xad, 0xbe, 0xef]
#guard returns twoLegacy.model "clamp" 5 5
#guard returns twoLegacy.model "clamp" 50 10
#guard returns twoLegacy.model "guarded" 100 101
#guard returns twoLegacy.model "selectorRevert" 8 8
#guard returns twoLegacy.model "nested" 0 0
#guard returns twoLegacy.model "nested" 4 0
#guard returns twoLegacy.model "nested" 5 6
#guard returns twoLegacy.model "boolCondition" 5 7
#guard reverts twoLegacy.model "guarded" 101 []
#guard reverts twoLegacy.model "selectorRevert" 7 [0xde, 0xad, 0xbe, 0xef]
#guard returns oneIr.model "clamp" 5 5
#guard returns oneIr.model "clamp" 50 10
#guard returns oneIr.model "guarded" 100 101
#guard returns oneIr.model "selectorRevert" 8 8
#guard returns oneIr.model "nested" 0 0
#guard returns oneIr.model "nested" 4 0
#guard returns oneIr.model "nested" 5 6
#guard returns oneIr.model "boolCondition" 5 7
#guard reverts oneIr.model "guarded" 101 []
#guard reverts oneIr.model "selectorRevert" 7 [0xde, 0xad, 0xbe, 0xef]
#guard returns twoIr.model "clamp" 5 5
#guard returns twoIr.model "clamp" 50 10
#guard returns twoIr.model "guarded" 100 101
#guard returns twoIr.model "selectorRevert" 8 8
#guard returns twoIr.model "nested" 0 0
#guard returns twoIr.model "nested" 4 0
#guard returns twoIr.model "nested" 5 6
#guard returns twoIr.model "boolCondition" 5 7
#guard reverts twoIr.model "guarded" 101 []
#guard reverts twoIr.model "selectorRevert" 7 [0xde, 0xad, 0xbe, 0xef]

end SolidityImportSmoke.YulIfStateCountChecks
