import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.HelperBranchScopeStateCountChecks
open Compiler.CompilationModel

/-! A declaration in an `if` branch that falls through, in an inlined helper whose other branch
returns, is out of scope after the `if`: inline assembly there reads the outer variable or
constant of the same name. The importer lowers the continuation inside that branch, and string
and array helpers flatten a plain block into their continuation; the end of the branch or block
restores the name-keyed Yul scope (`helperBlockScopes`). On `main` before this change the
assembly read the branch's declaration (7 or 9 instead of 5, 7 instead of 11) and the string
helper's block declaration (`"other"`, length 5, instead of `"five"`), in one- and two-slot
contracts alike. `runAssignsOuter`, `runUncheckedBranch` and `runBlockDeclaresArray` are
controls that were already exact. Expected values: solc 0.8.34 on Anvil, legacy and via-IR,
both contracts (all four columns identical). -/

solidity_import oneLegacy from "Contracts/SolidityImportSmoke" entry "HelperBranchScopeOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract HelperBranchScopeOneSlot
  function runThenDeclares(uint256)
  function runElseDeclares(uint256)
  function runNestedDeclares(uint256)
  function runOuterBranchDeclares(uint256)
  function runShadowsConstant(uint256)
  function runAssignsOuter(uint256)
  function runUncheckedBranch(uint256)
  function runBlockDeclaresString(uint256)
  function runBlockDeclaresArray(uint256)

solidity_import oneIr from "Contracts/SolidityImportSmoke" entry "HelperBranchScopeOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract HelperBranchScopeOneSlot
  function runThenDeclares(uint256)
  function runElseDeclares(uint256)
  function runNestedDeclares(uint256)
  function runOuterBranchDeclares(uint256)
  function runShadowsConstant(uint256)
  function runAssignsOuter(uint256)
  function runUncheckedBranch(uint256)
  function runBlockDeclaresString(uint256)
  function runBlockDeclaresArray(uint256)

solidity_import twoLegacy from "Contracts/SolidityImportSmoke" entry "HelperBranchScopeTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract HelperBranchScopeTwoSlots
  function runThenDeclares(uint256)
  function runElseDeclares(uint256)
  function runNestedDeclares(uint256)
  function runOuterBranchDeclares(uint256)
  function runShadowsConstant(uint256)
  function runAssignsOuter(uint256)
  function runUncheckedBranch(uint256)
  function runBlockDeclaresString(uint256)
  function runBlockDeclaresArray(uint256)

solidity_import twoIr from "Contracts/SolidityImportSmoke" entry "HelperBranchScopeTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract HelperBranchScopeTwoSlots
  function runThenDeclares(uint256)
  function runElseDeclares(uint256)
  function runNestedDeclares(uint256)
  function runOuterBranchDeclares(uint256)
  function runShadowsConstant(uint256)
  function runAssignsOuter(uint256)
  function runUncheckedBranch(uint256)
  function runBlockDeclaresString(uint256)
  function runBlockDeclaresArray(uint256)

private def body (model : CompilationModel) (name : String) : String :=
  match model.functions.find? (·.name == name) with
  | some f => (repr f.body).pretty 100000
  | none => ""

/-- The function imports and its body does not depend on the unrelated slot. -/
private def sameBody (one two : CompilationModel) (name : String) : Bool :=
  body one name != "" && body one name == body two name

private def returns (model : CompilationModel) (name : String) (x n : Nat) : Bool :=
  match model.functions.find? (·.name == name) with
  | some f =>
    let r := Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args := [x] } Verity.defaultState
    r.success && (r.returnWords == [n] || (r.returnWords.isEmpty && r.returnValue == some n))
  | none => false

#guard sameBody oneLegacy.model twoLegacy.model "runThenDeclares"
#guard sameBody oneLegacy.model twoLegacy.model "runElseDeclares"
#guard sameBody oneLegacy.model twoLegacy.model "runNestedDeclares"
#guard sameBody oneLegacy.model twoLegacy.model "runOuterBranchDeclares"
#guard sameBody oneLegacy.model twoLegacy.model "runShadowsConstant"
#guard sameBody oneLegacy.model twoLegacy.model "runAssignsOuter"
#guard sameBody oneLegacy.model twoLegacy.model "runUncheckedBranch"
#guard sameBody oneLegacy.model twoLegacy.model "runBlockDeclaresString"
#guard sameBody oneLegacy.model twoLegacy.model "runBlockDeclaresArray"
#guard sameBody oneIr.model twoIr.model "runThenDeclares"
#guard sameBody oneIr.model twoIr.model "runElseDeclares"
#guard sameBody oneIr.model twoIr.model "runNestedDeclares"
#guard sameBody oneIr.model twoIr.model "runOuterBranchDeclares"
#guard sameBody oneIr.model twoIr.model "runShadowsConstant"
#guard sameBody oneIr.model twoIr.model "runAssignsOuter"
#guard sameBody oneIr.model twoIr.model "runUncheckedBranch"
#guard sameBody oneIr.model twoIr.model "runBlockDeclaresString"
#guard sameBody oneIr.model twoIr.model "runBlockDeclaresArray"

#guard returns oneLegacy.model "runThenDeclares" 0 1
#guard returns oneLegacy.model "runThenDeclares" 1 5
#guard returns oneLegacy.model "runThenDeclares" 2 5
#guard returns oneLegacy.model "runThenDeclares" 7 5
#guard returns oneLegacy.model "runElseDeclares" 0 1
#guard returns oneLegacy.model "runElseDeclares" 1 5
#guard returns oneLegacy.model "runElseDeclares" 2 5
#guard returns oneLegacy.model "runElseDeclares" 7 5
#guard returns oneLegacy.model "runNestedDeclares" 0 1
#guard returns oneLegacy.model "runNestedDeclares" 1 2
#guard returns oneLegacy.model "runNestedDeclares" 2 5
#guard returns oneLegacy.model "runNestedDeclares" 7 5
#guard returns oneLegacy.model "runOuterBranchDeclares" 0 1
#guard returns oneLegacy.model "runOuterBranchDeclares" 1 2
#guard returns oneLegacy.model "runOuterBranchDeclares" 2 5
#guard returns oneLegacy.model "runOuterBranchDeclares" 7 5
#guard returns oneLegacy.model "runShadowsConstant" 0 1
#guard returns oneLegacy.model "runShadowsConstant" 1 11
#guard returns oneLegacy.model "runShadowsConstant" 2 11
#guard returns oneLegacy.model "runShadowsConstant" 7 11
#guard returns oneLegacy.model "runAssignsOuter" 0 1
#guard returns oneLegacy.model "runAssignsOuter" 1 21
#guard returns oneLegacy.model "runAssignsOuter" 2 22
#guard returns oneLegacy.model "runAssignsOuter" 7 27
#guard returns oneLegacy.model "runUncheckedBranch" 0 1
#guard returns oneLegacy.model "runUncheckedBranch" 1 5
#guard returns oneLegacy.model "runUncheckedBranch" 2 5
#guard returns oneLegacy.model "runUncheckedBranch" 7 5
#guard returns oneLegacy.model "runBlockDeclaresString" 0 4
#guard returns oneLegacy.model "runBlockDeclaresString" 1 4
#guard returns oneLegacy.model "runBlockDeclaresString" 2 4
#guard returns oneLegacy.model "runBlockDeclaresString" 7 4
#guard returns oneLegacy.model "runBlockDeclaresArray" 0 1
#guard returns oneLegacy.model "runBlockDeclaresArray" 1 1
#guard returns oneLegacy.model "runBlockDeclaresArray" 2 1
#guard returns oneLegacy.model "runBlockDeclaresArray" 7 1
#guard returns twoLegacy.model "runThenDeclares" 0 1
#guard returns twoLegacy.model "runThenDeclares" 1 5
#guard returns twoLegacy.model "runThenDeclares" 2 5
#guard returns twoLegacy.model "runThenDeclares" 7 5
#guard returns twoLegacy.model "runElseDeclares" 0 1
#guard returns twoLegacy.model "runElseDeclares" 1 5
#guard returns twoLegacy.model "runElseDeclares" 2 5
#guard returns twoLegacy.model "runElseDeclares" 7 5
#guard returns twoLegacy.model "runNestedDeclares" 0 1
#guard returns twoLegacy.model "runNestedDeclares" 1 2
#guard returns twoLegacy.model "runNestedDeclares" 2 5
#guard returns twoLegacy.model "runNestedDeclares" 7 5
#guard returns twoLegacy.model "runOuterBranchDeclares" 0 1
#guard returns twoLegacy.model "runOuterBranchDeclares" 1 2
#guard returns twoLegacy.model "runOuterBranchDeclares" 2 5
#guard returns twoLegacy.model "runOuterBranchDeclares" 7 5
#guard returns twoLegacy.model "runShadowsConstant" 0 1
#guard returns twoLegacy.model "runShadowsConstant" 1 11
#guard returns twoLegacy.model "runShadowsConstant" 2 11
#guard returns twoLegacy.model "runShadowsConstant" 7 11
#guard returns twoLegacy.model "runAssignsOuter" 0 1
#guard returns twoLegacy.model "runAssignsOuter" 1 21
#guard returns twoLegacy.model "runAssignsOuter" 2 22
#guard returns twoLegacy.model "runAssignsOuter" 7 27
#guard returns twoLegacy.model "runUncheckedBranch" 0 1
#guard returns twoLegacy.model "runUncheckedBranch" 1 5
#guard returns twoLegacy.model "runUncheckedBranch" 2 5
#guard returns twoLegacy.model "runUncheckedBranch" 7 5
#guard returns twoLegacy.model "runBlockDeclaresString" 0 4
#guard returns twoLegacy.model "runBlockDeclaresString" 1 4
#guard returns twoLegacy.model "runBlockDeclaresString" 2 4
#guard returns twoLegacy.model "runBlockDeclaresString" 7 4
#guard returns twoLegacy.model "runBlockDeclaresArray" 0 1
#guard returns twoLegacy.model "runBlockDeclaresArray" 1 1
#guard returns twoLegacy.model "runBlockDeclaresArray" 2 1
#guard returns twoLegacy.model "runBlockDeclaresArray" 7 1
#guard returns oneIr.model "runThenDeclares" 0 1
#guard returns oneIr.model "runThenDeclares" 1 5
#guard returns oneIr.model "runThenDeclares" 2 5
#guard returns oneIr.model "runThenDeclares" 7 5
#guard returns oneIr.model "runElseDeclares" 0 1
#guard returns oneIr.model "runElseDeclares" 1 5
#guard returns oneIr.model "runElseDeclares" 2 5
#guard returns oneIr.model "runElseDeclares" 7 5
#guard returns oneIr.model "runNestedDeclares" 0 1
#guard returns oneIr.model "runNestedDeclares" 1 2
#guard returns oneIr.model "runNestedDeclares" 2 5
#guard returns oneIr.model "runNestedDeclares" 7 5
#guard returns oneIr.model "runOuterBranchDeclares" 0 1
#guard returns oneIr.model "runOuterBranchDeclares" 1 2
#guard returns oneIr.model "runOuterBranchDeclares" 2 5
#guard returns oneIr.model "runOuterBranchDeclares" 7 5
#guard returns oneIr.model "runShadowsConstant" 0 1
#guard returns oneIr.model "runShadowsConstant" 1 11
#guard returns oneIr.model "runShadowsConstant" 2 11
#guard returns oneIr.model "runShadowsConstant" 7 11
#guard returns oneIr.model "runAssignsOuter" 0 1
#guard returns oneIr.model "runAssignsOuter" 1 21
#guard returns oneIr.model "runAssignsOuter" 2 22
#guard returns oneIr.model "runAssignsOuter" 7 27
#guard returns oneIr.model "runUncheckedBranch" 0 1
#guard returns oneIr.model "runUncheckedBranch" 1 5
#guard returns oneIr.model "runUncheckedBranch" 2 5
#guard returns oneIr.model "runUncheckedBranch" 7 5
#guard returns oneIr.model "runBlockDeclaresString" 0 4
#guard returns oneIr.model "runBlockDeclaresString" 1 4
#guard returns oneIr.model "runBlockDeclaresString" 2 4
#guard returns oneIr.model "runBlockDeclaresString" 7 4
#guard returns oneIr.model "runBlockDeclaresArray" 0 1
#guard returns oneIr.model "runBlockDeclaresArray" 1 1
#guard returns oneIr.model "runBlockDeclaresArray" 2 1
#guard returns oneIr.model "runBlockDeclaresArray" 7 1
#guard returns twoIr.model "runThenDeclares" 0 1
#guard returns twoIr.model "runThenDeclares" 1 5
#guard returns twoIr.model "runThenDeclares" 2 5
#guard returns twoIr.model "runThenDeclares" 7 5
#guard returns twoIr.model "runElseDeclares" 0 1
#guard returns twoIr.model "runElseDeclares" 1 5
#guard returns twoIr.model "runElseDeclares" 2 5
#guard returns twoIr.model "runElseDeclares" 7 5
#guard returns twoIr.model "runNestedDeclares" 0 1
#guard returns twoIr.model "runNestedDeclares" 1 2
#guard returns twoIr.model "runNestedDeclares" 2 5
#guard returns twoIr.model "runNestedDeclares" 7 5
#guard returns twoIr.model "runOuterBranchDeclares" 0 1
#guard returns twoIr.model "runOuterBranchDeclares" 1 2
#guard returns twoIr.model "runOuterBranchDeclares" 2 5
#guard returns twoIr.model "runOuterBranchDeclares" 7 5
#guard returns twoIr.model "runShadowsConstant" 0 1
#guard returns twoIr.model "runShadowsConstant" 1 11
#guard returns twoIr.model "runShadowsConstant" 2 11
#guard returns twoIr.model "runShadowsConstant" 7 11
#guard returns twoIr.model "runAssignsOuter" 0 1
#guard returns twoIr.model "runAssignsOuter" 1 21
#guard returns twoIr.model "runAssignsOuter" 2 22
#guard returns twoIr.model "runAssignsOuter" 7 27
#guard returns twoIr.model "runUncheckedBranch" 0 1
#guard returns twoIr.model "runUncheckedBranch" 1 5
#guard returns twoIr.model "runUncheckedBranch" 2 5
#guard returns twoIr.model "runUncheckedBranch" 7 5
#guard returns twoIr.model "runBlockDeclaresString" 0 4
#guard returns twoIr.model "runBlockDeclaresString" 1 4
#guard returns twoIr.model "runBlockDeclaresString" 2 4
#guard returns twoIr.model "runBlockDeclaresString" 7 4
#guard returns twoIr.model "runBlockDeclaresArray" 0 1
#guard returns twoIr.model "runBlockDeclaresArray" 1 1
#guard returns twoIr.model "runBlockDeclaresArray" 2 1
#guard returns twoIr.model "runBlockDeclaresArray" 7 1

end SolidityImportSmoke.HelperBranchScopeStateCountChecks
