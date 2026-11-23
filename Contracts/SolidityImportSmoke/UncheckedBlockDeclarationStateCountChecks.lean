import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
Helpers whose `unchecked` block declares locals and returns on some paths only lower the same
way whatever the state-variable count (#2830). `UncheckedBlockDeclarationOneSlot.sol` declares
one state variable (a constant) and `UncheckedBlockDeclarationTwoSlots.sol` the same contract
plus one unrelated state variable and one unused function.

Such a block is flattened into the helper continuation, so a returning `if` inside it carries
the end of the block into each copied continuation. Its declarations used to be rejected with
one state variable and admitted with more, where they stayed visible to inline assembly after
the block: `shadowedLocal` returned the block's `v` instead of the outer one (5 -> 4, 0 -> 2^256-1).
The block end now restores the name-keyed scope of the block's start (`yulNames`,
`yulMemoryArrays`, `yulMemoryStructs`), as a nested block does, and the declarations are
admitted whatever the count. Their ids are out of Solidity scope after the block. A shadowed
memory array read by `mload` after the block is not covered here: the importer rejects that
`mload` in both contracts (`unsupported Yul builtin mload`).

Values: solc 0.8.34 on Anvil (osaka, runs 466), both contracts and both pipelines.
-/
namespace SolidityImportSmoke.UncheckedBlockDeclarationStateCountChecks
open Compiler.CompilationModel

solidity_import oneLegacy from "Contracts/SolidityImportSmoke" entry "UncheckedBlockDeclarationOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract UncheckedBlockDeclarationOneSlot
  function runBumped(uint256)
  function runCheckedAfter(uint256,uint256)
  function runTwoDeclarations(uint256)
  function runRedeclared(uint256)
  function runShadowedLocal(uint256)
  function runShadowedConstant(uint256)

solidity_import oneIr from "Contracts/SolidityImportSmoke" entry "UncheckedBlockDeclarationOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract UncheckedBlockDeclarationOneSlot
  function runBumped(uint256)
  function runCheckedAfter(uint256,uint256)
  function runTwoDeclarations(uint256)
  function runRedeclared(uint256)
  function runShadowedLocal(uint256)
  function runShadowedConstant(uint256)

solidity_import twoLegacy from "Contracts/SolidityImportSmoke" entry "UncheckedBlockDeclarationTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract UncheckedBlockDeclarationTwoSlots
  function runBumped(uint256)
  function runCheckedAfter(uint256,uint256)
  function runTwoDeclarations(uint256)
  function runRedeclared(uint256)
  function runShadowedLocal(uint256)
  function runShadowedConstant(uint256)

solidity_import twoIr from "Contracts/SolidityImportSmoke" entry "UncheckedBlockDeclarationTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract UncheckedBlockDeclarationTwoSlots
  function runBumped(uint256)
  function runCheckedAfter(uint256,uint256)
  function runTwoDeclarations(uint256)
  function runRedeclared(uint256)
  function runShadowedLocal(uint256)
  function runShadowedConstant(uint256)

private def body (model : CompilationModel) (name : String) : String :=
  match model.functions.find? (·.name == name) with
  | some f => (repr f.body).pretty 100000
  | none => ""

/-- The function imports and its body does not depend on the unrelated slot. -/
private def sameBody (one two : CompilationModel) (name : String) : Bool :=
  body one name != "" && body one name == body two name

private def run (model : CompilationModel) (name : String) (args : List Nat) :
    Option Denote.DenoteResult :=
  (model.functions.find? (·.name == name)).map fun f =>
    Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args } Verity.defaultState

private def returns (model : CompilationModel) (name : String) (args : List Nat) (n : Nat) : Bool :=
  match run model name args with
  | some r =>
    r.success && (r.returnWords == [n] || (r.returnWords.isEmpty && r.returnValue == some n))
  | none => false

/-- Reverts with `Panic(0x11)` (checked arithmetic overflow). -/
private def panicsOverflow (model : CompilationModel) (name : String) (args : List Nat) : Bool :=
  match run model name args with
  | some r =>
    !r.success && r.revertData == some ([0x4e, 0x48, 0x7b, 0x71] ++ List.replicate 31 0 ++ [0x11])
  | none => false

private def maxWord : Nat := 2 ^ 256 - 1

#guard sameBody oneLegacy.model twoLegacy.model "runBumped"
#guard sameBody oneLegacy.model twoLegacy.model "runCheckedAfter"
#guard sameBody oneLegacy.model twoLegacy.model "runTwoDeclarations"
#guard sameBody oneLegacy.model twoLegacy.model "runRedeclared"
#guard sameBody oneLegacy.model twoLegacy.model "runShadowedLocal"
#guard sameBody oneLegacy.model twoLegacy.model "runShadowedConstant"
#guard sameBody oneIr.model twoIr.model "runBumped"
#guard sameBody oneIr.model twoIr.model "runCheckedAfter"
#guard sameBody oneIr.model twoIr.model "runTwoDeclarations"
#guard sameBody oneIr.model twoIr.model "runRedeclared"
#guard sameBody oneIr.model twoIr.model "runShadowedLocal"
#guard sameBody oneIr.model twoIr.model "runShadowedConstant"

#guard returns oneLegacy.model "runBumped" [5] 6
#guard returns oneLegacy.model "runBumped" [maxWord] 7
#guard returns oneLegacy.model "runCheckedAfter" [0, 9] 0
#guard returns oneLegacy.model "runCheckedAfter" [3, 4] 7
#guard returns oneLegacy.model "runTwoDeclarations" [0] maxWord
#guard returns oneLegacy.model "runTwoDeclarations" [50] 99
#guard returns oneLegacy.model "runTwoDeclarations" [10] 10
#guard returns oneLegacy.model "runRedeclared" [0] maxWord
#guard returns oneLegacy.model "runRedeclared" [4] 12
#guard returns oneLegacy.model "runShadowedLocal" [5] 5
#guard returns oneLegacy.model "runShadowedLocal" [1] 100
#guard returns oneLegacy.model "runShadowedLocal" [0] 0
#guard returns oneLegacy.model "runShadowedConstant" [5] 11
#guard returns oneLegacy.model "runShadowedConstant" [maxWord] 3
#guard panicsOverflow oneLegacy.model "runCheckedAfter" [maxWord, 1]

#guard returns oneIr.model "runBumped" [5] 6
#guard returns oneIr.model "runBumped" [maxWord] 7
#guard returns oneIr.model "runCheckedAfter" [0, 9] 0
#guard returns oneIr.model "runCheckedAfter" [3, 4] 7
#guard returns oneIr.model "runTwoDeclarations" [0] maxWord
#guard returns oneIr.model "runTwoDeclarations" [50] 99
#guard returns oneIr.model "runTwoDeclarations" [10] 10
#guard returns oneIr.model "runRedeclared" [0] maxWord
#guard returns oneIr.model "runRedeclared" [4] 12
#guard returns oneIr.model "runShadowedLocal" [5] 5
#guard returns oneIr.model "runShadowedLocal" [1] 100
#guard returns oneIr.model "runShadowedLocal" [0] 0
#guard returns oneIr.model "runShadowedConstant" [5] 11
#guard returns oneIr.model "runShadowedConstant" [maxWord] 3
#guard panicsOverflow oneIr.model "runCheckedAfter" [maxWord, 1]

#guard returns twoLegacy.model "runBumped" [5] 6
#guard returns twoLegacy.model "runBumped" [maxWord] 7
#guard returns twoLegacy.model "runCheckedAfter" [0, 9] 0
#guard returns twoLegacy.model "runCheckedAfter" [3, 4] 7
#guard returns twoLegacy.model "runTwoDeclarations" [0] maxWord
#guard returns twoLegacy.model "runTwoDeclarations" [50] 99
#guard returns twoLegacy.model "runTwoDeclarations" [10] 10
#guard returns twoLegacy.model "runRedeclared" [0] maxWord
#guard returns twoLegacy.model "runRedeclared" [4] 12
#guard returns twoLegacy.model "runShadowedLocal" [5] 5
#guard returns twoLegacy.model "runShadowedLocal" [1] 100
#guard returns twoLegacy.model "runShadowedLocal" [0] 0
#guard returns twoLegacy.model "runShadowedConstant" [5] 11
#guard returns twoLegacy.model "runShadowedConstant" [maxWord] 3
#guard panicsOverflow twoLegacy.model "runCheckedAfter" [maxWord, 1]

#guard returns twoIr.model "runBumped" [5] 6
#guard returns twoIr.model "runBumped" [maxWord] 7
#guard returns twoIr.model "runCheckedAfter" [0, 9] 0
#guard returns twoIr.model "runCheckedAfter" [3, 4] 7
#guard returns twoIr.model "runTwoDeclarations" [0] maxWord
#guard returns twoIr.model "runTwoDeclarations" [50] 99
#guard returns twoIr.model "runTwoDeclarations" [10] 10
#guard returns twoIr.model "runRedeclared" [0] maxWord
#guard returns twoIr.model "runRedeclared" [4] 12
#guard returns twoIr.model "runShadowedLocal" [5] 5
#guard returns twoIr.model "runShadowedLocal" [1] 100
#guard returns twoIr.model "runShadowedLocal" [0] 0
#guard returns twoIr.model "runShadowedConstant" [5] 11
#guard returns twoIr.model "runShadowedConstant" [maxWord] 3
#guard panicsOverflow twoIr.model "runCheckedAfter" [maxWord, 1]

end SolidityImportSmoke.UncheckedBlockDeclarationStateCountChecks

