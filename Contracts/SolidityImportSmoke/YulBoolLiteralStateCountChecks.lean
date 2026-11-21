import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.YulBoolLiteralStateCountChecks
open Compiler.CompilationModel

solidity_import oneLegacy from "Contracts/SolidityImportSmoke" entry "YulBoolLiteralOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract YulBoolLiteralOneSlot
  function flag(uint256)
  function cleared(uint256)
  function plusTrue(uint256)
  function timesFalse(uint256)
  function boundTrue(uint256)

solidity_import twoLegacy from "Contracts/SolidityImportSmoke" entry "YulBoolLiteralTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract YulBoolLiteralTwoSlots
  function flag(uint256)
  function cleared(uint256)
  function plusTrue(uint256)
  function timesFalse(uint256)
  function boundTrue(uint256)

solidity_import oneIr from "Contracts/SolidityImportSmoke" entry "YulBoolLiteralOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract YulBoolLiteralOneSlot
  function flag(uint256)
  function cleared(uint256)
  function plusTrue(uint256)
  function timesFalse(uint256)
  function boundTrue(uint256)

solidity_import twoIr from "Contracts/SolidityImportSmoke" entry "YulBoolLiteralTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract YulBoolLiteralTwoSlots
  function flag(uint256)
  function cleared(uint256)
  function plusTrue(uint256)
  function timesFalse(uint256)
  function boundTrue(uint256)

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

/-- solc 0.8.34 on Anvil, both pipelines and both contracts: flag(41) = 1, cleared(41) = 0,
plusTrue(41) = 42, timesFalse(41) = 0, boundTrue(6) = 7. -/
private def returns (model : CompilationModel) (name : String) (x n : Nat) : Bool :=
  match run model name x with
  | some r => r.success && (r.returnWords == [n] || (r.returnWords.isEmpty && r.returnValue == some n))
  | none => false

#guard sameBody oneLegacy.model twoLegacy.model "flag"
#guard sameBody oneLegacy.model twoLegacy.model "cleared"
#guard sameBody oneLegacy.model twoLegacy.model "plusTrue"
#guard sameBody oneLegacy.model twoLegacy.model "timesFalse"
#guard sameBody oneLegacy.model twoLegacy.model "boundTrue"
#guard sameBody oneIr.model twoIr.model "flag"
#guard sameBody oneIr.model twoIr.model "cleared"
#guard sameBody oneIr.model twoIr.model "plusTrue"
#guard sameBody oneIr.model twoIr.model "timesFalse"
#guard sameBody oneIr.model twoIr.model "boundTrue"
#guard returns oneLegacy.model "flag" 41 1
#guard returns oneLegacy.model "cleared" 41 0
#guard returns oneLegacy.model "plusTrue" 41 42
#guard returns oneLegacy.model "timesFalse" 41 0
#guard returns oneLegacy.model "boundTrue" 6 7
#guard returns twoLegacy.model "flag" 41 1
#guard returns twoLegacy.model "cleared" 41 0
#guard returns twoLegacy.model "plusTrue" 41 42
#guard returns twoLegacy.model "timesFalse" 41 0
#guard returns twoLegacy.model "boundTrue" 6 7
#guard returns oneIr.model "flag" 41 1
#guard returns oneIr.model "cleared" 41 0
#guard returns oneIr.model "plusTrue" 41 42
#guard returns oneIr.model "timesFalse" 41 0
#guard returns oneIr.model "boundTrue" 6 7
#guard returns twoIr.model "flag" 41 1
#guard returns twoIr.model "cleared" 41 0
#guard returns twoIr.model "plusTrue" 41 42
#guard returns twoIr.model "timesFalse" 41 0
#guard returns twoIr.model "boundTrue" 6 7

end SolidityImportSmoke.YulBoolLiteralStateCountChecks
