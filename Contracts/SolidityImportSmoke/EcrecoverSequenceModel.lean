import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.PrecompileResponderMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.EcrecoverSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "EcrecoverSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EcrecoverFixture
  function PERMIT_TYPEHASH()
  function nonces(address)
  function allowance(address,address)
  function storedDigest()
  function lastRecovered()
  function recoveries()
  function domainSeparator()
  function recover(bytes32,uint8,bytes32,bytes32)
  function verify(bytes32,uint8,bytes32,bytes32,address)
  function recoverWide(bytes32,uint256,bytes32,bytes32)
  function setDigest(bytes32)
  function recoverOrdered(uint8,bytes32,bytes32)
  function recoverReassigned(bytes32,uint8,bytes32,bytes32)
  function permit(address,address,uint256,uint256,uint8,bytes32,bytes32)
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.EcrecoverSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.EcrecoverSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.EcrecoverSequenceModel.model
        SolidityImportSmoke.EcrecoverSequenceModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.PrecompileResponderMocks.configure)
