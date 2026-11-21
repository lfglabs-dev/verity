import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.BareRequireStateCountChecks
open Compiler.CompilationModel

solidity_import oneLegacy from "Contracts/SolidityImportSmoke" entry "BareRequireStateCount.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract BareRequireOneSlot
  function rootGuard(uint256)
  function helperGuard(uint256)
  function namedHelperGuard(uint256)

solidity_import twoLegacy from "Contracts/SolidityImportSmoke" entry "BareRequireStateCount.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract BareRequireTwoSlots
  function rootGuard(uint256)
  function helperGuard(uint256)
  function namedHelperGuard(uint256)

solidity_import oneIr from "Contracts/SolidityImportSmoke" entry "BareRequireStateCount.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract BareRequireOneSlot
  function rootGuard(uint256)
  function helperGuard(uint256)
  function namedHelperGuard(uint256)

solidity_import twoIr from "Contracts/SolidityImportSmoke" entry "BareRequireStateCount.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract BareRequireTwoSlots
  function rootGuard(uint256)
  function helperGuard(uint256)
  function namedHelperGuard(uint256)

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

private def returns (model : CompilationModel) (name : String) (x n : Nat) : Bool :=
  match run model name x with
  | some r => r.success && (r.returnWords == [n] || (r.returnWords.isEmpty && r.returnValue == some n))
  | none => false

/-- solc 0.8.34 (both pipelines, Anvil): a failed bare `require` reverts with empty data. -/
private def revertsEmpty (model : CompilationModel) (name : String) (x : Nat) : Bool :=
  match run model name x with
  | some r => !r.success && r.revertData == some []
  | none => false

#guard sameBody oneLegacy.model twoLegacy.model "rootGuard"
#guard sameBody oneLegacy.model twoLegacy.model "helperGuard"
#guard sameBody oneLegacy.model twoLegacy.model "namedHelperGuard"
#guard sameBody oneIr.model twoIr.model "rootGuard"
#guard sameBody oneIr.model twoIr.model "helperGuard"
#guard sameBody oneIr.model twoIr.model "namedHelperGuard"
#guard returns oneLegacy.model "rootGuard" 21 21
#guard revertsEmpty oneLegacy.model "rootGuard" 20
#guard returns oneLegacy.model "helperGuard" 21 21
#guard revertsEmpty oneLegacy.model "helperGuard" 20
#guard returns oneLegacy.model "namedHelperGuard" 20 21
#guard revertsEmpty oneLegacy.model "namedHelperGuard" 30
#guard returns twoLegacy.model "rootGuard" 21 21
#guard revertsEmpty twoLegacy.model "rootGuard" 20
#guard returns twoLegacy.model "helperGuard" 21 21
#guard revertsEmpty twoLegacy.model "helperGuard" 20
#guard returns twoLegacy.model "namedHelperGuard" 20 21
#guard revertsEmpty twoLegacy.model "namedHelperGuard" 30
#guard returns oneIr.model "rootGuard" 21 21
#guard revertsEmpty oneIr.model "rootGuard" 20
#guard returns oneIr.model "helperGuard" 21 21
#guard revertsEmpty oneIr.model "helperGuard" 20
#guard returns oneIr.model "namedHelperGuard" 20 21
#guard revertsEmpty oneIr.model "namedHelperGuard" 30
#guard returns twoIr.model "rootGuard" 21 21
#guard revertsEmpty twoIr.model "rootGuard" 20
#guard returns twoIr.model "helperGuard" 21 21
#guard revertsEmpty twoIr.model "helperGuard" 20
#guard returns twoIr.model "namedHelperGuard" 20 21
#guard revertsEmpty twoIr.model "namedHelperGuard" 30

end SolidityImportSmoke.BareRequireStateCountChecks
