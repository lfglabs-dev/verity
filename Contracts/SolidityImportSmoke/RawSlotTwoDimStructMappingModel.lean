import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.RawSlotTwoDimStructMappingModel
open Compiler.CompilationModel

solidity_import imported from "Contracts/SolidityImportSmoke" entry "RawSlotTwoDimStructMapping.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract RawSlotTwoDimStructMapping
  function writeDirectGrid(uint256,uint256,uint128,uint64,uint8,bool,address,uint96)
  function readDirectGrid(uint256,uint256)
  function updateViaPointer(uint256,uint256,uint128,uint64,bool)
  function writeAndReadAccount(address,uint256,uint128,uint8,address,uint96)
  function readRowHelper(uint256,uint256)
  function deleteGridEntry(uint256,uint256)
  function rawGridWords(uint256,uint256)
  function rawAccountWords(address,uint256)

def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle

end SolidityImportSmoke.RawSlotTwoDimStructMappingModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.RawSlotTwoDimStructMappingModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.RawSlotTwoDimStructMappingModel.model
        SolidityImportSmoke.RawSlotTwoDimStructMappingModel.oracle args
