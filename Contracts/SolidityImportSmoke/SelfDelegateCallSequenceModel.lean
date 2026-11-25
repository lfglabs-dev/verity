import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.ModelResponders
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.SelfDelegateCallSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "SelfDelegateCallSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfDelegateCallFixture
  function addAmount(uint256)
  function failEmpty()
  function multicall(«bytes[]»)
  function selfDispatchSingle(bytes)
  function read()
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.SelfDelegateCallSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.SelfDelegateCallSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.SelfDelegateCallSequenceModel.model
        SolidityImportSmoke.SelfDelegateCallSequenceModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.ModelResponders.configureSelfDelegate
          SolidityImportSmoke.SelfDelegateCallSequenceModel.oracle
          SolidityImportSmoke.SelfDelegateCallSequenceModel.model)
