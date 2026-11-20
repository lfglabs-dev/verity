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
  function narrowConstant()
  function constantCopy()
  function addressChoice(uint256,bool)
  function payableCasts(uint256)
  function bytesArrayOr(uint256)
  function returnedBytesLiteral()
  function returnedBytesTuple()
  function signedWidening(uint256)
  function bytesCast(bytes32)
  function bytesLocal(uint256)
  function bytesChoice(uint256)
  function payableCopy(uint256)
  function invertedBytes(uint256)
  function shiftUntilZero(uint8)
  function widenedError(uint8)
  function explicitWideError(uint8)
  function constantError()
  function tryBytesLiteral()
  function prefixInc(uint8)
  function prefixDec(uint8)

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
  function narrowConstant()
  function constantCopy()
  function addressChoice(uint256,bool)
  function payableCasts(uint256)
  function bytesArrayOr(uint256)
  function returnedBytesLiteral()
  function returnedBytesTuple()
  function signedWidening(uint256)
  function bytesCast(bytes32)
  function bytesLocal(uint256)
  function bytesChoice(uint256)
  function payableCopy(uint256)
  function invertedBytes(uint256)
  function shiftUntilZero(uint8)
  function widenedError(uint8)
  function explicitWideError(uint8)
  function constantError()
  function tryBytesLiteral()
  function prefixInc(uint8)
  function prefixDec(uint8)

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

#guard observes legacy.model "payableCopy" [2 ^ 160 + 257] (2 ^ 160 + 257)
#guard observes ir.model "payableCopy" [2 ^ 160 + 257] 257
#guard observesWords legacy.model "payableCasts" [2 ^ 160 + 257] [2 ^ 160 + 257, 2 ^ 160 + 257]
#guard observesWords ir.model "payableCasts" [2 ^ 160 + 257] [257, 2 ^ 160 + 257]
#guard observes legacy.model "addressChoice" [2 ^ 160 + 257, 1] (2 ^ 160 + 257)
#guard observes ir.model "addressChoice" [2 ^ 160 + 257, 1] 257
#guard observesWords legacy.model "bytesArrayOr" [257] [0, 2 ^ 224 + 257]
#guard observesWords ir.model "bytesArrayOr" [257] [0, 2 ^ 224 + 257]
#guard observes legacy.model "returnedBytesLiteral" [] (0x11223344 * 2 ^ 224)
#guard observes ir.model "returnedBytesLiteral" [] (0x11223344 * 2 ^ 224)
#guard observesWords legacy.model "returnedBytesTuple" [] [0x11223344 * 2 ^ 224, 1]
#guard observesWords ir.model "returnedBytesTuple" [] [0x11223344 * 2 ^ 224, 1]
#guard observesWords legacy.model "signedWidening" [257] [1, 257]
#guard observesWords ir.model "signedWidening" [257] [1, 257]
#guard observesWords legacy.model "signedWidening" [511] [2 ^ 256 - 1, 511]
#guard observesWords ir.model "signedWidening" [511] [2 ^ 256 - 1, 511]
#guard observes legacy.model "bytesChoice" [0] (0xffffffff * 2 ^ 224)
#guard observes ir.model "bytesChoice" [0] (0xffffffff * 2 ^ 224)
#guard observes legacy.model "bytesCast" [1] 1
#guard observes ir.model "bytesCast" [1] 0
#guard observes legacy.model "bytesLocal" [1] (2 ^ 256 - 2)
#guard observes ir.model "bytesLocal" [1] (0xffffffff * 2 ^ 224)
#guard observes legacy.model "invertedBytes" [1] (2 ^ 256 - 2)
#guard observes ir.model "invertedBytes" [1] (0xffffffff * 2 ^ 224)
#guard observes legacy.model "shiftUntilZero" [5] 3
#guard observes ir.model "shiftUntilZero" [5] 3
private def revertsWith (m : CompilationModel) (name : String) (args : List Nat)
    (payload : List UInt8) : Bool :=
  match m.functions.find? (·.name == name) with
  | none => false
  | some f =>
    let r := Denote.denoteFunction SolidityImport.Differential.oracle m f
      { sender := 1, functionSelector := 0, args } Verity.defaultState
    !r.success && r.revertData == some payload

private def isSelfCallWithWord (expected : Nat) : Stmt → Bool
  | .ecm _ [.contractAddress, .literal word] => word == expected
  | _ => false

#guard [legacy.model, ir.model].all fun m =>
  match m.functions.find? (·.name == "tryBytesLiteral") with
  | none => false
  | some f => f.body.any (isSelfCallWithWord (0x11223344 * 2 ^ 224))

#guard [legacy.model, ir.model].all fun m => revertsWith m "widenedError" [17]
  ([0x40, 0x61, 0x3a, 0x9f] ++ List.replicate 31 0 ++ [17])
#guard [legacy.model, ir.model].all fun m => revertsWith m "explicitWideError" [17]
  ([0x40, 0x61, 0x3a, 0x9f] ++ List.replicate 31 0 ++ [17])
#guard [legacy.model, ir.model].all fun m => revertsWith m "constantError" []
  ([0xc2, 0x76, 0x39, 0x44] ++ List.replicate 31 0 ++ [1])
#guard observes legacy.model "narrowConstant" [] 1
#guard observes ir.model "narrowConstant" [] 1
#guard observes legacy.model "constantCopy" [] 257
#guard observes ir.model "constantCopy" [] 1
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

/--
error: NarrowStackWords.sol:271:59: Identifier: [solidity-import:unsupported] event direct parameter type differs from its declaration
closure: NarrowStackWords.badEmit
x
-/
#guard_msgs in
solidity_import badEmitLegacy from "Contracts/SolidityImportSmoke" entry "NarrowStackWords.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract NarrowStackWords
  function badEmit(uint8)

/--
error: NarrowStackWords.sol:271:59: Identifier: [solidity-import:unsupported] event direct parameter type differs from its declaration
closure: NarrowStackWords.badEmit
x
-/
#guard_msgs in
solidity_import badEmitIr from "Contracts/SolidityImportSmoke" entry "NarrowStackWords.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract NarrowStackWords
  function badEmit(uint8)

#guard observesWords legacy.model "prefixInc" [255] [256, 0]
#guard observesWords ir.model "prefixInc" [255] [0, 0]
#guard observesWords legacy.model "prefixDec" [0] [2 ^ 256 - 1, 255]
#guard observesWords ir.model "prefixDec" [0] [255, 255]

/--
error: NarrowStackWords.sol:296:13: FunctionCall: [solidity-import:unsupported] named arguments in a try self-call are unsupported
closure: NarrowStackWords.namedTry
this.receivePair({second: 2, first: 1})
-/
#guard_msgs in
solidity_import namedTryLegacy from "Contracts/SolidityImportSmoke" entry "NarrowStackWords.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract NarrowStackWords
  function namedTry()

/--
error: NarrowStackWords.sol:296:13: FunctionCall: [solidity-import:unsupported] named arguments in a try self-call are unsupported
closure: NarrowStackWords.namedTry
this.receivePair({second: 2, first: 1})
-/
#guard_msgs in
solidity_import namedTryIr from "Contracts/SolidityImportSmoke" entry "NarrowStackWords.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract NarrowStackWords
  function namedTry()

end SolidityImportSmoke.NarrowStackWordsChecks
