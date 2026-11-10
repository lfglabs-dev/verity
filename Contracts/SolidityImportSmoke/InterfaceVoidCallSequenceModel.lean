import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.CallResponderMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.InterfaceVoidCallSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "InterfaceVoidCallSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract InterfaceVoidCallFixture
  function ping(address,uint256)
  function relay(address)
  function relayData(address,bytes)
  function poke(address)
  function fund(address,uint128)
  function read()
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.InterfaceVoidCallSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.InterfaceVoidCallSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.InterfaceVoidCallSequenceModel.model
        SolidityImportSmoke.InterfaceVoidCallSequenceModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.CallResponderMocks.configure)
