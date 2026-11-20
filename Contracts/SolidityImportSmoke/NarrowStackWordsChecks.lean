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
  function returnedLiteral(uint256)
  function logSigned(uint256)
  function copiedResult(uint256)
  function addressCast(uint256)
  function square(uint8)
  function storeAndCopy(uint256)
  function quotient(uint256,uint256)
  function literalKey()
  function narrowCount(uint256)
  function narrowSlice(bytes,uint256)
  function descending(uint256)
  function descendingWords(uint256)

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
  function returnedLiteral(uint256)
  function logSigned(uint256)
  function copiedResult(uint256)
  function addressCast(uint256)
  function square(uint8)
  function storeAndCopy(uint256)
  function quotient(uint256,uint256)
  function literalKey()
  function narrowCount(uint256)
  function narrowSlice(bytes,uint256)
  function descending(uint256)
  function descendingWords(uint256)

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
#guard observes legacy.model "returnedLiteral" [257] 1
#guard observes ir.model "returnedLiteral" [257] 1
#guard observes legacy.model "copiedResult" [257] 257
#guard observes ir.model "copiedResult" [257] 257
#guard observes legacy.model "addressCast" [2 ^ 160 + 257] (2 ^ 160 + 257)
#guard observes ir.model "addressCast" [2 ^ 160 + 257] 257
#guard observes legacy.model "square" [13] 169
#guard observes ir.model "square" [13] 169
#guard [legacy.model, ir.model].all fun m =>
  match m.functions.find? (·.name == "logSigned") with
  | none => false
  | some f =>
    let r := Denote.denoteFunction SolidityImport.Differential.oracle m f
      { sender := 1, functionSelector := 0, args := [511] } Verity.defaultState
    r.success && r.events == [[2 ^ 256 - 1]]
#guard observes legacy.model "signedCast" [511] 511
#guard observes ir.model "signedCast" [511] (2 ^ 256 - 1)

private def observesWords (model : CompilationModel) (name : String) (args words : List Nat) : Bool :=
  match model.functions.find? (·.name == name) with
  | none => false
  | some f =>
    let r := Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args } Verity.defaultState
    r.success && r.returnWords == words

#guard observes legacy.model "descending" [256] 0
#guard observes ir.model "descending" [256] 0
#guard observes legacy.model "descending" [257] 1
#guard observes ir.model "descending" [257] 1
#guard observesWords legacy.model "descendingWords" [258] [258, 257, 2]
#guard observesWords ir.model "descendingWords" [258] [258, 1, 2]
#guard observesWords legacy.model "storeAndCopy" [257] [257, 1]
#guard observesWords ir.model "storeAndCopy" [257] [257, 1]
private def sliceArgs := [64, 257, 2, 0xaabb * 2 ^ 240]
private def sliceHash := 0x9f1a1ebcae59b0879e9fb23ad9f90461016010b02c4a57af0fab0ee41025b4aa
#guard observes legacy.model "literalKey" [] 11
#guard observes ir.model "literalKey" [] 11
#guard observes legacy.model "narrowCount" [257] 1
#guard observes ir.model "narrowCount" [257] 1
#guard observes legacy.model "narrowSlice" sliceArgs sliceHash
#guard observes ir.model "narrowSlice" sliceArgs sliceHash
#guard observes legacy.model "quotient" [128, 255] 128
#guard observes ir.model "quotient" [128, 255] 128
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
