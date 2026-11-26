import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.StaticOracleMocks
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.InterfaceMultiReturnAndReceiverModel
open Compiler.CompilationModel

solidity_import imported from "Contracts/SolidityImportSmoke" entry "InterfaceMultiReturnAndReceiver.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract InterfaceMultiReturnAndReceiver
  function configure(address,uint256,address,address)
  function readStatusDecl(address)
  function readStatusAssign(address)
  function readStatusDirect(address)
  function readStatusElided(address)
  function readStatusDiscarded(address)
  function readQuote(address,uint256)
  function probeViaHelper(uint256,uint256)
  function probeViaFactory(address,uint256,uint256)
  function probeViaState(uint256)
  function probeViaConditional(bool,uint256,uint256)
  function statusViaHelper(uint256)

def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle

end SolidityImportSmoke.InterfaceMultiReturnAndReceiverModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.InterfaceMultiReturnAndReceiverModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.InterfaceMultiReturnAndReceiverModel.model
        SolidityImportSmoke.InterfaceMultiReturnAndReceiverModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.StaticOracleMocks.configure)
