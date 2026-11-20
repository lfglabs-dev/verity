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
  function boundaries(uint256)
  function signedCast(uint256)
  function literalArray(uint256)
  function signaturePayload(uint256)
  function errorValue(uint256)

solidity_import ir from "Contracts/SolidityImportSmoke" entry "NarrowStackWords.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract NarrowStackWords
  function checkedValue(uint256,uint256)
  function shiftedCopy(uint256,uint256)
  function overwrite(uint256,bool)
  function carried(uint256)
  function boundaries(uint256)
  function signedCast(uint256)
  function literalArray(uint256)
  function signaturePayload(uint256)
  function errorValue(uint256)

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
#guard observes legacy.model "literalArray" [257] 1
#guard observes ir.model "literalArray" [257] 1
private def payloadHash := 0xda4212981b0d0350403585a221f7da4c34d6c3cb29918f45cf5fb21cd8f1eb37
#guard observes legacy.model "signaturePayload" [257] payloadHash
#guard observes ir.model "signaturePayload" [257] payloadHash
#guard observes legacy.model "signedCast" [511] 511
#guard observes ir.model "signedCast" [511] (2 ^ 256 - 1)

private def observesWords (model : CompilationModel) (name : String) (args words : List Nat) : Bool :=
  match model.functions.find? (·.name == name) with
  | none => false
  | some f =>
    let r := Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args } Verity.defaultState
    r.success && r.returnWords == words

#guard observesWords legacy.model "boundaries" [511] [255, 255, 255]
#guard observesWords ir.model "boundaries" [511] [255, 255, 255]
#guard match ir.model.functions.find? (·.name == "errorValue") with
  | none => false
  | some f =>
    let r := Denote.denoteFunction SolidityImport.Differential.oracle ir.model f
      { sender := 1, functionSelector := 0, args := [511] } Verity.defaultState
    !r.success && r.revertData == some
      ([0xc2, 0x76, 0x39, 0x44] ++ List.replicate 31 (0 : UInt8) ++ [255])

end SolidityImportSmoke.NarrowStackWordsChecks
