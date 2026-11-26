import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LoopBoundsAndHelperReturnModel
open Compiler.CompilationModel

solidity_import imported from "Contracts/SolidityImportSmoke" entry "LoopBoundsAndHelperReturn.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract LoopBoundsAndHelperReturn
  function sumRange(uint256,uint256)
  function sumFromConst(uint256)
  function sumFromExpr(uint256,uint256)
  function predeclaredRange(uint256,uint256)
  function narrowStartWrap(uint8,uint256)
  function sumDown(uint256,uint256)
  function helperDecrementReturn(uint8,uint256)
  function helperNonZeroControl(uint8,uint256,uint256,uint256)
  function helperNestedReturn(uint8,uint256)
  function helperWhileReturn(uint256,uint256)
  function helperWhileTrueReturn(uint256,uint256)
  function voidForEarlyReturn(uint8,uint256)
  function voidWhileEarlyReturn(uint256,uint256)

def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle

end SolidityImportSmoke.LoopBoundsAndHelperReturnModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LoopBoundsAndHelperReturnModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LoopBoundsAndHelperReturnModel.model
        SolidityImportSmoke.LoopBoundsAndHelperReturnModel.oracle args
