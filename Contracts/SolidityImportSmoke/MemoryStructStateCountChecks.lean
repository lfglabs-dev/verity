import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.MemoryStructStateCountChecks
open Compiler.CompilationModel

solidity_import oneLegacy from "Contracts/SolidityImportSmoke" entry "MemoryStructOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract MemoryStructOneSlot
  function named(uint256)
  function tupled(uint256)
  function zeroed(uint256)
  function ordered(uint256)

solidity_import twoLegacy from "Contracts/SolidityImportSmoke" entry "MemoryStructTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract MemoryStructTwoSlots
  function named(uint256)
  function tupled(uint256)
  function zeroed(uint256)
  function ordered(uint256)

solidity_import oneIr from "Contracts/SolidityImportSmoke" entry "MemoryStructOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract MemoryStructOneSlot
  function named(uint256)
  function tupled(uint256)
  function zeroed(uint256)
  function ordered(uint256)

solidity_import twoIr from "Contracts/SolidityImportSmoke" entry "MemoryStructTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract MemoryStructTwoSlots
  function named(uint256)
  function tupled(uint256)
  function zeroed(uint256)
  function ordered(uint256)

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
named(0) = 100, named(4) = 508, named(5) = 16, tupled(0) = 3, tupled(2) = 25,
tupled(9) = 1003, zeroed(0) = 77, zeroed(3) = 77, zeroed(4) = 4, ordered(1) = 54321,
ordered(2) = 65432. -/
private def returns (model : CompilationModel) (name : String) (x n : Nat) : Bool :=
  match run model name x with
  | some r => r.success && (r.returnWords == [n] || (r.returnWords.isEmpty && r.returnValue == some n))
  | none => false

private def maxWord : Nat := 2 ^ 256 - 1
private def half : Nat := 2 ^ 255

/-- solc 0.8.34 on Anvil: named(2^256 - 1), named(2^255) and tupled(2^255) revert with
`Panic(0x11)` (checked `x + 1`, `x * 2`, `x * 10`). -/
private def panics (model : CompilationModel) (name : String) (x : Nat) : Bool :=
  match run model name x with
  | some r => !r.success && r.revertData == some ([0x4e, 0x48, 0x7b, 0x71] ++ List.replicate 31 0 ++ [0x11])
  | none => false

#guard sameBody oneLegacy.model twoLegacy.model "named"
#guard sameBody oneLegacy.model twoLegacy.model "tupled"
#guard sameBody oneLegacy.model twoLegacy.model "zeroed"
#guard sameBody oneLegacy.model twoLegacy.model "ordered"
#guard sameBody oneIr.model twoIr.model "named"
#guard sameBody oneIr.model twoIr.model "tupled"
#guard sameBody oneIr.model twoIr.model "zeroed"
#guard sameBody oneIr.model twoIr.model "ordered"
#guard returns oneLegacy.model "named" 0 100
#guard returns oneLegacy.model "named" 4 508
#guard returns oneLegacy.model "named" 5 16
#guard returns oneLegacy.model "tupled" 0 3
#guard returns oneLegacy.model "tupled" 2 25
#guard returns oneLegacy.model "tupled" 9 1003
#guard returns oneLegacy.model "zeroed" 0 77
#guard returns oneLegacy.model "zeroed" 3 77
#guard returns oneLegacy.model "zeroed" 4 4
#guard returns oneLegacy.model "ordered" 1 54321
#guard returns oneLegacy.model "ordered" 2 65432
#guard panics oneLegacy.model "named" maxWord
#guard panics oneLegacy.model "named" half
#guard panics oneLegacy.model "tupled" half
#guard returns twoLegacy.model "named" 0 100
#guard returns twoLegacy.model "named" 4 508
#guard returns twoLegacy.model "named" 5 16
#guard returns twoLegacy.model "tupled" 0 3
#guard returns twoLegacy.model "tupled" 2 25
#guard returns twoLegacy.model "tupled" 9 1003
#guard returns twoLegacy.model "zeroed" 0 77
#guard returns twoLegacy.model "zeroed" 3 77
#guard returns twoLegacy.model "zeroed" 4 4
#guard returns twoLegacy.model "ordered" 1 54321
#guard returns twoLegacy.model "ordered" 2 65432
#guard panics twoLegacy.model "named" maxWord
#guard panics twoLegacy.model "named" half
#guard panics twoLegacy.model "tupled" half
#guard returns oneIr.model "named" 0 100
#guard returns oneIr.model "named" 4 508
#guard returns oneIr.model "named" 5 16
#guard returns oneIr.model "tupled" 0 3
#guard returns oneIr.model "tupled" 2 25
#guard returns oneIr.model "tupled" 9 1003
#guard returns oneIr.model "zeroed" 0 77
#guard returns oneIr.model "zeroed" 3 77
#guard returns oneIr.model "zeroed" 4 4
#guard returns oneIr.model "ordered" 1 54321
#guard returns oneIr.model "ordered" 2 65432
#guard panics oneIr.model "named" maxWord
#guard panics oneIr.model "named" half
#guard panics oneIr.model "tupled" half
#guard returns twoIr.model "named" 0 100
#guard returns twoIr.model "named" 4 508
#guard returns twoIr.model "named" 5 16
#guard returns twoIr.model "tupled" 0 3
#guard returns twoIr.model "tupled" 2 25
#guard returns twoIr.model "tupled" 9 1003
#guard returns twoIr.model "zeroed" 0 77
#guard returns twoIr.model "zeroed" 3 77
#guard returns twoIr.model "zeroed" 4 4
#guard returns twoIr.model "ordered" 1 54321
#guard returns twoIr.model "ordered" 2 65432
#guard panics twoIr.model "named" maxWord
#guard panics twoIr.model "named" half
#guard panics twoIr.model "tupled" half

end SolidityImportSmoke.MemoryStructStateCountChecks
