import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.StoragePointerGuardSequenceModel
open Compiler.CompilationModel

solidity_import imported from "Contracts/SolidityImportSmoke" entry "StoragePointerGuardSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract StoragePointerGuardFixture
  function add(uint256,uint256)
  function addChecked(uint256,uint256)
  function addRaw(uint256,uint256)
  function store(uint256,bool,uint256)
  function storeRaw(uint256,bool,uint256)
  function read(uint256)
  function readRaw(uint256)

def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle

end SolidityImportSmoke.StoragePointerGuardSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.StoragePointerGuardSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.StoragePointerGuardSequenceModel.model
        SolidityImportSmoke.StoragePointerGuardSequenceModel.oracle args
