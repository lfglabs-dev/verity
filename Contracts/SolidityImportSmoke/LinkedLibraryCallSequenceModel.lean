import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LinkedLibraryCallSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LinkedLibraryCallSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none",
          linkedLibrariesMatchSource := true }
  contract LinkedLibraryCallFixture
  function setConfig(bytes32,address,Mode)
  function setConfigLogged(bytes32,address,Mode)
  function word(bytes32)
  function bump(bytes32,uint256)
  function bumpMain(uint256)
  function bumpPacked(bytes32,uint256,address)
  function reset(bytes32)
  function addExternal(bytes32,uint256)
  function cleanNarrow(uint256,uint256,uint256,uint256)
  function share(bytes32,uint256)
  function total(bytes32)
  function last(bytes32)
  function calls(bytes32)
  function mainState()
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.LinkedLibraryCallSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LinkedLibraryCallSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LinkedLibraryCallSequenceModel.model
        SolidityImportSmoke.LinkedLibraryCallSequenceModel.oracle args
