import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.CallResponderMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.ExternalCodeAndLowLevelCallSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "ExternalCodeAndLowLevelCallSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ExternalCodeAndLowLevelCallFixture
  function codeSize(address)
  function hasCode(address)
  function deposit(address,uint256)
  function withdraw(address,address,uint256)
  function pay(address,address,uint256)
  function stored(address)
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.ExternalCodeAndLowLevelCallSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.ExternalCodeAndLowLevelCallSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.ExternalCodeAndLowLevelCallSequenceModel.model
        SolidityImportSmoke.ExternalCodeAndLowLevelCallSequenceModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.CallResponderMocks.configure)
