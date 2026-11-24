import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.YulNarrowResultStateCountChecks
open Compiler.CompilationModel

solidity_import oneLegacy from "Contracts/SolidityImportSmoke" entry "YulNarrowResultOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract YulNarrowResultOneSlot
  function pairWords(uint256,uint256)
  function pairRaw(uint256,uint256)
  function pairUse(uint256,uint256)
  function mulSat(uint256,uint256)
  function mulTry(uint256,uint256)
  function readBackRaw(uint256)
  function localWord(uint256)
  function localUses(uint256)
  function localKey(uint256)
  function squareRaw(uint8)
  function clampedRaw(uint256,uint256)
  function packedFlag(uint256)
  function encodedFlag(uint256)
  function arrayFlag(uint256)
  function sameFlag(uint256,uint256)
  function queryPair(address)
  function sendFlag(address,uint256)
  function transferChecked(address,address,uint256)
  function emitFlag(uint256)

solidity_import twoLegacy from "Contracts/SolidityImportSmoke" entry "YulNarrowResultTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract YulNarrowResultTwoSlots
  function pairWords(uint256,uint256)
  function pairRaw(uint256,uint256)
  function pairUse(uint256,uint256)
  function mulSat(uint256,uint256)
  function mulTry(uint256,uint256)
  function readBackRaw(uint256)
  function localWord(uint256)
  function localUses(uint256)
  function localKey(uint256)
  function squareRaw(uint8)
  function clampedRaw(uint256,uint256)
  function packedFlag(uint256)
  function encodedFlag(uint256)
  function arrayFlag(uint256)
  function sameFlag(uint256,uint256)
  function queryPair(address)
  function sendFlag(address,uint256)
  function transferChecked(address,address,uint256)
  function emitFlag(uint256)

solidity_import oneIr from "Contracts/SolidityImportSmoke" entry "YulNarrowResultOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract YulNarrowResultOneSlot
  function pairWords(uint256,uint256)
  function pairRaw(uint256,uint256)
  function pairUse(uint256,uint256)
  function mulSat(uint256,uint256)
  function mulTry(uint256,uint256)
  function readBackRaw(uint256)
  function localWord(uint256)
  function localUses(uint256)
  function localKey(uint256)
  function squareRaw(uint8)
  function clampedRaw(uint256,uint256)
  function packedFlag(uint256)
  function encodedFlag(uint256)
  function arrayFlag(uint256)
  function sameFlag(uint256,uint256)
  function queryPair(address)
  function sendFlag(address,uint256)
  function transferChecked(address,address,uint256)
  function emitFlag(uint256)

solidity_import twoIr from "Contracts/SolidityImportSmoke" entry "YulNarrowResultTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract YulNarrowResultTwoSlots
  function pairWords(uint256,uint256)
  function pairRaw(uint256,uint256)
  function pairUse(uint256,uint256)
  function mulSat(uint256,uint256)
  function mulTry(uint256,uint256)
  function readBackRaw(uint256)
  function localWord(uint256)
  function localUses(uint256)
  function localKey(uint256)
  function squareRaw(uint8)
  function clampedRaw(uint256,uint256)
  function packedFlag(uint256)
  function encodedFlag(uint256)
  function arrayFlag(uint256)
  function sameFlag(uint256,uint256)
  function queryPair(address)
  function sendFlag(address,uint256)
  function transferChecked(address,address,uint256)
  function emitFlag(uint256)

private def body (model : CompilationModel) (name : String) : String :=
  match model.functions.find? (·.name == name) with
  | some f => (repr f.body).pretty 100000
  | none => ""

/-- The function imports and its body does not depend on the unrelated slot. -/
private def sameBody (one two : CompilationModel) (name : String) : Bool :=
  body one name != "" && body one name == body two name

private def run (model : CompilationModel) (name : String) (args : List Nat) : Option Denote.DenoteResult :=
  (model.functions.find? (·.name == name)).map fun f =>
    Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args } Verity.defaultState

/-- The function succeeds from the default state and returns exactly `words`. -/
private def returns (model : CompilationModel) (name : String) (args words : List Nat) : Bool :=
  match run model name args with
  | some r => r.success && r.returnWords == words
  | none => false

/-- `Panic(uint256)` with `code`. -/
private def panicData (code : Nat) : List UInt8 :=
  [0x4e, 0x48, 0x7b, 0x71] ++ List.replicate 31 0 ++ [UInt8.ofNat code]

private def panics (model : CompilationModel) (name : String) (args : List Nat) (code : Nat) : Bool :=
  match run model name args with
  | some r => !r.success && r.revertData == some (panicData code)
  | none => false

private def max : Nat := 2 ^ 256 - 1

/-! Every root imports, the `staticcall` (`queryPair`) and `call` (`sendFlag`, `transferChecked`) helpers
included, with a body that does not depend on the unrelated slot. -/
#guard sameBody oneLegacy.model twoLegacy.model "pairWords" && sameBody oneIr.model twoIr.model "pairWords" &&
  sameBody oneLegacy.model twoLegacy.model "pairRaw" && sameBody oneIr.model twoIr.model "pairRaw" &&
  sameBody oneLegacy.model twoLegacy.model "pairUse" && sameBody oneIr.model twoIr.model "pairUse" &&
  sameBody oneLegacy.model twoLegacy.model "mulSat" && sameBody oneIr.model twoIr.model "mulSat" &&
  sameBody oneLegacy.model twoLegacy.model "mulTry" && sameBody oneIr.model twoIr.model "mulTry" &&
  sameBody oneLegacy.model twoLegacy.model "readBackRaw" && sameBody oneIr.model twoIr.model "readBackRaw" &&
  sameBody oneLegacy.model twoLegacy.model "localWord" && sameBody oneIr.model twoIr.model "localWord" &&
  sameBody oneLegacy.model twoLegacy.model "localUses" && sameBody oneIr.model twoIr.model "localUses" &&
  sameBody oneLegacy.model twoLegacy.model "localKey" && sameBody oneIr.model twoIr.model "localKey" &&
  sameBody oneLegacy.model twoLegacy.model "squareRaw" && sameBody oneIr.model twoIr.model "squareRaw" &&
  sameBody oneLegacy.model twoLegacy.model "clampedRaw" && sameBody oneIr.model twoIr.model "clampedRaw" &&
  sameBody oneLegacy.model twoLegacy.model "packedFlag" && sameBody oneIr.model twoIr.model "packedFlag" &&
  sameBody oneLegacy.model twoLegacy.model "encodedFlag" && sameBody oneIr.model twoIr.model "encodedFlag" &&
  sameBody oneLegacy.model twoLegacy.model "arrayFlag" && sameBody oneIr.model twoIr.model "arrayFlag" &&
  sameBody oneLegacy.model twoLegacy.model "sameFlag" && sameBody oneIr.model twoIr.model "sameFlag" &&
  sameBody oneLegacy.model twoLegacy.model "queryPair" && sameBody oneIr.model twoIr.model "queryPair" &&
  sameBody oneLegacy.model twoLegacy.model "sendFlag" && sameBody oneIr.model twoIr.model "sendFlag" &&
  sameBody oneLegacy.model twoLegacy.model "transferChecked" && sameBody oneIr.model twoIr.model "transferChecked" &&
  sameBody oneLegacy.model twoLegacy.model "emitFlag" && sameBody oneIr.model twoIr.model "emitFlag"

/-! Expected results: solc 0.8.34 on the EVM (osaka), legacy and via-IR, optimizer off and at
466 runs (identical), both contracts. A Yul write keeps the raw word: Yul reads and copies see
it (`pairRaw`, `clampedRaw`, `readBackRaw`, `localWord` raw/copied, `true && b` in `localUses`,
whose raw word overflows the checked product at `max`), while `==`, `!`, conditions, mapping
keys and ABI encoding clean it; `clampedRaw` clears a width that does not fit 32 bits; a packed storage member, `abi.encode`,
a memory array element and `==` between two dirty words see the cleaned word. Legacy
keeps the unchecked `uint8` product on the stack (`squareRaw`); via-IR cleans it. -/
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [0, 0] [0, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [0, 0] [0, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [0, 0] [0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [0, 5] [0, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [0, 5] [0, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [0, 5] [0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [0, 4294967301] [0, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [0, 4294967301] [0, 4294967301])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [0, 4294967301] [0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [0, max] [0, 4294967295])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [0, max] [0, max])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [0, max] [0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [1, 0] [1, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [1, 0] [1, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [1, 0] [0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [1, 5] [1, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [1, 5] [1, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [1, 5] [6])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [1, 4294967301] [1, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [1, 4294967301] [1, 4294967301])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [1, 4294967301] [6])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [1, max] [1, 4294967295])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [1, max] [1, max])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [1, max] [4294967296])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [2, 0] [1, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [2, 0] [2, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [2, 0] [0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [2, 5] [1, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [2, 5] [2, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [2, 5] [6])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [2, 4294967301] [1, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [2, 4294967301] [2, 4294967301])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [2, 4294967301] [6])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [2, max] [1, 4294967295])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [2, max] [2, max])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [2, max] [4294967296])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [256, 0] [1, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [256, 0] [256, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [256, 0] [0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [256, 5] [1, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [256, 5] [256, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [256, 5] [6])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [256, 4294967301] [1, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [256, 4294967301] [256, 4294967301])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [256, 4294967301] [6])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [256, max] [1, 4294967295])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [256, max] [256, max])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [256, max] [4294967296])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [max, 0] [1, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [max, 0] [max, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [max, 0] [0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [max, 5] [1, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [max, 5] [max, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [max, 5] [6])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [max, 4294967301] [1, 5])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [max, 4294967301] [max, 4294967301])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [max, 4294967301] [6])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairWords" [max, max] [1, 4294967295])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairRaw" [max, max] [max, max])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "pairUse" [max, max] [4294967296])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "mulSat" [0, max] [0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "mulTry" [0, max] [1, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "mulSat" [3, 5] [15])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "mulTry" [3, 5] [1, 15])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "mulSat" [2 ^ 128, 2 ^ 128] [max])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "mulTry" [2 ^ 128, 2 ^ 128] [0, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "mulSat" [2 ^ 255, 2] [max])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "mulTry" [2 ^ 255, 2] [0, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "mulSat" [max, max] [max])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "mulTry" [max, max] [0, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "mulSat" [2 ^ 127, 3] [0x180000000000000000000000000000000])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "mulTry" [2 ^ 127, 3] [1, 0x180000000000000000000000000000000])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "readBackRaw" [0] [1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localWord" [0] [0, 0, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localUses" [0] [100])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localKey" [0] [0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "readBackRaw" [1] [1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localWord" [1] [1, 1, 1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localUses" [1] [1011])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localKey" [1] [7])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "readBackRaw" [2] [1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localWord" [2] [1, 2, 2])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localUses" [2] [2011])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localKey" [2] [7])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "readBackRaw" [256] [1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localWord" [256] [1, 256, 256])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localUses" [256] [256011])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localKey" [256] [7])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "readBackRaw" [max] [1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localWord" [max] [1, max, max])
#guard [oneLegacy.model, twoLegacy.model].all (panics · "localUses" [max] 0x11)
#guard [oneLegacy.model, twoLegacy.model].all (returns · "localKey" [max] [7])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "squareRaw" [3] [9])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "squareRaw" [200] [40000])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "squareRaw" [255] [65025])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "clampedRaw" [2, 7] [1, 7, 2, 7])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "clampedRaw" [1, 4294967295] [1, 4294967295, 1, 4294967295])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "clampedRaw" [1, 4294967296] [1, 0, 1, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "clampedRaw" [max, 4294967301] [1, 0, max, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "clampedRaw" [0, max] [0, 0, 0, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "packedFlag" [0] [5, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "encodedFlag" [0] [0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "arrayFlag" [0] [32, 1, 0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "packedFlag" [1] [5, 1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "encodedFlag" [1] [0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "arrayFlag" [1] [32, 1, 1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "packedFlag" [2] [5, 1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "encodedFlag" [2] [0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "arrayFlag" [2] [32, 1, 1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "packedFlag" [256] [5, 1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "encodedFlag" [256] [0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "arrayFlag" [256] [32, 1, 1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "packedFlag" [max] [5, 1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "encodedFlag" [max] [0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "arrayFlag" [max] [32, 1, 1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "sameFlag" [2, 1] [1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "sameFlag" [256, max] [1])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "sameFlag" [0, 2] [0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "sameFlag" [1, 0] [0])
#guard [oneLegacy.model, twoLegacy.model].all (returns · "sameFlag" [0, 0] [1])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [0, 0] [0, 0])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [0, 0] [0, 0])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [0, 0] [0])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [0, 5] [0, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [0, 5] [0, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [0, 5] [0])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [0, 4294967301] [0, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [0, 4294967301] [0, 4294967301])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [0, 4294967301] [0])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [0, max] [0, 4294967295])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [0, max] [0, max])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [0, max] [0])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [1, 0] [1, 0])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [1, 0] [1, 0])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [1, 0] [0])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [1, 5] [1, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [1, 5] [1, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [1, 5] [6])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [1, 4294967301] [1, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [1, 4294967301] [1, 4294967301])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [1, 4294967301] [6])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [1, max] [1, 4294967295])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [1, max] [1, max])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [1, max] [4294967296])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [2, 0] [1, 0])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [2, 0] [2, 0])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [2, 0] [0])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [2, 5] [1, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [2, 5] [2, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [2, 5] [6])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [2, 4294967301] [1, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [2, 4294967301] [2, 4294967301])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [2, 4294967301] [6])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [2, max] [1, 4294967295])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [2, max] [2, max])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [2, max] [4294967296])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [256, 0] [1, 0])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [256, 0] [256, 0])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [256, 0] [0])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [256, 5] [1, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [256, 5] [256, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [256, 5] [6])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [256, 4294967301] [1, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [256, 4294967301] [256, 4294967301])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [256, 4294967301] [6])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [256, max] [1, 4294967295])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [256, max] [256, max])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [256, max] [4294967296])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [max, 0] [1, 0])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [max, 0] [max, 0])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [max, 0] [0])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [max, 5] [1, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [max, 5] [max, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [max, 5] [6])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [max, 4294967301] [1, 5])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [max, 4294967301] [max, 4294967301])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [max, 4294967301] [6])
#guard [oneIr.model, twoIr.model].all (returns · "pairWords" [max, max] [1, 4294967295])
#guard [oneIr.model, twoIr.model].all (returns · "pairRaw" [max, max] [max, max])
#guard [oneIr.model, twoIr.model].all (returns · "pairUse" [max, max] [4294967296])
#guard [oneIr.model, twoIr.model].all (returns · "mulSat" [0, max] [0])
#guard [oneIr.model, twoIr.model].all (returns · "mulTry" [0, max] [1, 0])
#guard [oneIr.model, twoIr.model].all (returns · "mulSat" [3, 5] [15])
#guard [oneIr.model, twoIr.model].all (returns · "mulTry" [3, 5] [1, 15])
#guard [oneIr.model, twoIr.model].all (returns · "mulSat" [2 ^ 128, 2 ^ 128] [max])
#guard [oneIr.model, twoIr.model].all (returns · "mulTry" [2 ^ 128, 2 ^ 128] [0, 0])
#guard [oneIr.model, twoIr.model].all (returns · "mulSat" [2 ^ 255, 2] [max])
#guard [oneIr.model, twoIr.model].all (returns · "mulTry" [2 ^ 255, 2] [0, 0])
#guard [oneIr.model, twoIr.model].all (returns · "mulSat" [max, max] [max])
#guard [oneIr.model, twoIr.model].all (returns · "mulTry" [max, max] [0, 0])
#guard [oneIr.model, twoIr.model].all (returns · "mulSat" [2 ^ 127, 3] [0x180000000000000000000000000000000])
#guard [oneIr.model, twoIr.model].all (returns · "mulTry" [2 ^ 127, 3] [1, 0x180000000000000000000000000000000])
#guard [oneIr.model, twoIr.model].all (returns · "readBackRaw" [0] [1])
#guard [oneIr.model, twoIr.model].all (returns · "localWord" [0] [0, 0, 0])
#guard [oneIr.model, twoIr.model].all (returns · "localUses" [0] [100])
#guard [oneIr.model, twoIr.model].all (returns · "localKey" [0] [0])
#guard [oneIr.model, twoIr.model].all (returns · "readBackRaw" [1] [1])
#guard [oneIr.model, twoIr.model].all (returns · "localWord" [1] [1, 1, 1])
#guard [oneIr.model, twoIr.model].all (returns · "localUses" [1] [1011])
#guard [oneIr.model, twoIr.model].all (returns · "localKey" [1] [7])
#guard [oneIr.model, twoIr.model].all (returns · "readBackRaw" [2] [1])
#guard [oneIr.model, twoIr.model].all (returns · "localWord" [2] [1, 2, 2])
#guard [oneIr.model, twoIr.model].all (returns · "localUses" [2] [2011])
#guard [oneIr.model, twoIr.model].all (returns · "localKey" [2] [7])
#guard [oneIr.model, twoIr.model].all (returns · "readBackRaw" [256] [1])
#guard [oneIr.model, twoIr.model].all (returns · "localWord" [256] [1, 256, 256])
#guard [oneIr.model, twoIr.model].all (returns · "localUses" [256] [256011])
#guard [oneIr.model, twoIr.model].all (returns · "localKey" [256] [7])
#guard [oneIr.model, twoIr.model].all (returns · "readBackRaw" [max] [1])
#guard [oneIr.model, twoIr.model].all (returns · "localWord" [max] [1, max, max])
#guard [oneIr.model, twoIr.model].all (panics · "localUses" [max] 0x11)
#guard [oneIr.model, twoIr.model].all (returns · "localKey" [max] [7])
#guard [oneIr.model, twoIr.model].all (returns · "squareRaw" [3] [9])
#guard [oneIr.model, twoIr.model].all (returns · "squareRaw" [200] [64])
#guard [oneIr.model, twoIr.model].all (returns · "squareRaw" [255] [1])
#guard [oneIr.model, twoIr.model].all (returns · "clampedRaw" [2, 7] [1, 7, 2, 7])
#guard [oneIr.model, twoIr.model].all (returns · "clampedRaw" [1, 4294967295] [1, 4294967295, 1, 4294967295])
#guard [oneIr.model, twoIr.model].all (returns · "clampedRaw" [1, 4294967296] [1, 0, 1, 0])
#guard [oneIr.model, twoIr.model].all (returns · "clampedRaw" [max, 4294967301] [1, 0, max, 0])
#guard [oneIr.model, twoIr.model].all (returns · "clampedRaw" [0, max] [0, 0, 0, 0])
#guard [oneIr.model, twoIr.model].all (returns · "packedFlag" [0] [5, 0])
#guard [oneIr.model, twoIr.model].all (returns · "encodedFlag" [0] [0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563])
#guard [oneIr.model, twoIr.model].all (returns · "arrayFlag" [0] [32, 1, 0])
#guard [oneIr.model, twoIr.model].all (returns · "packedFlag" [1] [5, 1])
#guard [oneIr.model, twoIr.model].all (returns · "encodedFlag" [1] [0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6])
#guard [oneIr.model, twoIr.model].all (returns · "arrayFlag" [1] [32, 1, 1])
#guard [oneIr.model, twoIr.model].all (returns · "packedFlag" [2] [5, 1])
#guard [oneIr.model, twoIr.model].all (returns · "encodedFlag" [2] [0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6])
#guard [oneIr.model, twoIr.model].all (returns · "arrayFlag" [2] [32, 1, 1])
#guard [oneIr.model, twoIr.model].all (returns · "packedFlag" [256] [5, 1])
#guard [oneIr.model, twoIr.model].all (returns · "encodedFlag" [256] [0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6])
#guard [oneIr.model, twoIr.model].all (returns · "arrayFlag" [256] [32, 1, 1])
#guard [oneIr.model, twoIr.model].all (returns · "packedFlag" [max] [5, 1])
#guard [oneIr.model, twoIr.model].all (returns · "encodedFlag" [max] [0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6])
#guard [oneIr.model, twoIr.model].all (returns · "arrayFlag" [max] [32, 1, 1])
#guard [oneIr.model, twoIr.model].all (returns · "sameFlag" [2, 1] [1])
#guard [oneIr.model, twoIr.model].all (returns · "sameFlag" [256, max] [1])
#guard [oneIr.model, twoIr.model].all (returns · "sameFlag" [0, 2] [0])
#guard [oneIr.model, twoIr.model].all (returns · "sameFlag" [1, 0] [0])
#guard [oneIr.model, twoIr.model].all (returns · "sameFlag" [0, 0] [1])

/-- The events of one successful call from the default state. -/
private def events (model : CompilationModel) (name : String) (args : List Nat) : Option (List (List Nat)) :=
  (run model name args).bind fun r => if r.success then some r.events else none

/-! solc emits `Flag(true, true)` for every nonzero word and `Flag(false, false)` for zero. -/
#guard [oneLegacy.model, twoLegacy.model, oneIr.model, twoIr.model].all fun m =>
  (events m "emitFlag" [0]).isSome && events m "emitFlag" [1] != events m "emitFlag" [0] &&
  [2, 256, max].all fun w => (events m "emitFlag" [w]).isSome && events m "emitFlag" [w] == events m "emitFlag" [1]

end SolidityImportSmoke.YulNarrowResultStateCountChecks
