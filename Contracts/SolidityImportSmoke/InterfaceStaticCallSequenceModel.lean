import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.StaticOracleMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.InterfaceStaticCallSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "InterfaceStaticCallSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract InterfaceStaticCallFixture
  function read(address)
  function record(address,uint256)
  function ping(address,uint256)
  function probe(address,uint256)
  function sum(address,address)
  function stored()
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
end SolidityImportSmoke.InterfaceStaticCallSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.InterfaceStaticCallSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.InterfaceStaticCallSequenceModel.model
        SolidityImportSmoke.InterfaceStaticCallSequenceModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.StaticOracleMocks.configure)
