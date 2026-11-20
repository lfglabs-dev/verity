import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.NarrowStackWordsChecks
open Compiler.CompilationModel

solidity_import legacy from "Contracts/SolidityImportSmoke" entry "NarrowStackWords.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract NarrowStackWords
  function checkedValue(uint256,uint256)
  function shiftedCopy(uint256,uint256)
  function overwrite(uint256,bool)
  function carried(uint256)

solidity_import ir from "Contracts/SolidityImportSmoke" entry "NarrowStackWords.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract NarrowStackWords
  function checkedValue(uint256,uint256)
  function shiftedCopy(uint256,uint256)
  function overwrite(uint256,bool)
  function carried(uint256)

private def observes (model : CompilationModel) (name : String) (args : List Nat) (n : Nat) : Bool :=
  match model.functions.find? (·.name == name) with
  | none => false
  | some f =>
    let r := Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args } Verity.defaultState
    r.success && r.returnWords == [n]

#guard observes legacy.model "checkedValue" [384, 263] 2
#guard observes ir.model "checkedValue" [384, 263] 2
#guard observes legacy.model "shiftedCopy" [384, 257] 256
#guard observes ir.model "shiftedCopy" [384, 257] 0
#guard observes legacy.model "overwrite" [257, 0] 259
#guard observes ir.model "overwrite" [257, 0] 3
#guard observes legacy.model "overwrite" [257, 1] 7
#guard observes ir.model "overwrite" [257, 1] 7
#guard observes legacy.model "carried" [257] 259
#guard observes ir.model "carried" [257] 3

end SolidityImportSmoke.NarrowStackWordsChecks
