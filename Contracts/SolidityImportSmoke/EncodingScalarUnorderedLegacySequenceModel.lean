import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.EncodingScalarUnorderedLegacySequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke"
  entry "EncodingScalarUnorderedSequence.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.EncodingScalarUnorderedLegacySequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.EncodingScalarUnorderedLegacySequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.EncodingScalarUnorderedLegacySequenceModel.model
        SolidityImportSmoke.EncodingScalarUnorderedLegacySequenceModel.oracle args
