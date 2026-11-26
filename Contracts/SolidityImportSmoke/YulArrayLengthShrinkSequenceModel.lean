import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.YulArrayLengthShrinkSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke"
  entry "YulArrayLengthShrinkSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract YulArrayLengthShrinkFixture
  function initList()
  function addItem(address)
  function fail()
  function readState()
  function paginate(address,uint256)
  function paginateThenAllocate(address,uint256,uint256)
  function returnedShrunkArray(uint256,uint256,uint256)
  function inspectPostShrink(uint256,uint256,uint256)
  function filterCompact(uint256,uint256,uint256,uint256)
  function helperShrinkSub(uint256,uint256)
  function helperConstShadow(uint256,uint256)
  function shrinkNarrowAndZero(uint256,uint256,bool)
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.YulArrayLengthShrinkSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.YulArrayLengthShrinkSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.YulArrayLengthShrinkSequenceModel.model
        SolidityImportSmoke.YulArrayLengthShrinkSequenceModel.oracle args
