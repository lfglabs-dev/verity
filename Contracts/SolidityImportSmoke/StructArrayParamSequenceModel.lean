import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.StructArrayParamSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "StructArrayParamSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()
  function processBatch(«Item[]»)
  function sumCalldata(«Item[]»)
  function sumMemory(«Item[]»)
  function targetAt(«Item[]»,uint256)
  function targetAtMemory(«Item[]»,uint256)
  function afterHead(uint256,bytes,«uint256[2]»,«Packed[]»)
  function afterHeadMemory(uint256,«Packed[]»,uint256)
  function pairSum(«Item[]»,«Item[]»)
  function elementCalldata(«Item[]»,uint256)
  function elementMemory(«Item[]»,uint256)
  function elementCopied(«Item[]»,uint256)
  function elementHelper(«Item[]»,uint256)
def model : CompilationModel := imported.model
-- Mapping slots use the actual Keccak oracle shared with differential execution.
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.StructArrayParamSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.StructArrayParamSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.StructArrayParamSequenceModel.model SolidityImportSmoke.StructArrayParamSequenceModel.oracle args
