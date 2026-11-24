import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.ReentrantCallResponderMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.ReentrantCallbackSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "ReentrantCallbackSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ReentrantCallbackFixture
  function poke(address,uint256)
  function emitPoke(address,uint256)
  function tryPoke(address,uint256)
  function enter()
  function enterSmall(uint8)
  function enterThenFail()
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.ReentrantCallbackSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.ReentrantCallbackSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.ReentrantCallbackSequenceModel.model
        SolidityImportSmoke.ReentrantCallbackSequenceModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.ReentrantCallResponderMocks.configure
          SolidityImportSmoke.ReentrantCallbackSequenceModel.model
          SolidityImportSmoke.ReentrantCallbackSequenceModel.oracle)
