import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.PrecompileResponderMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.Eip712PermitRecoverySequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "Eip712PermitRecoverySequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract PermitRecoveryFixture
  function DOMAIN_TYPEHASH()
  function PERMIT_TYPEHASH()
  function nonces(address)
  function allowance(address,address)
  function lastSigner()
  function recoveries()
  function domainSeparator()
  function hashPermit(address,address,uint256,uint256,uint256)
  function hashTypedData(bytes32)
  function tryRecover(bytes32,uint8,bytes32,bytes32)
  function permit(address,address,uint256,uint256,uint8,bytes32,bytes32)
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.Eip712PermitRecoverySequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.Eip712PermitRecoverySequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.Eip712PermitRecoverySequenceModel.model
        SolidityImportSmoke.Eip712PermitRecoverySequenceModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.PrecompileResponderMocks.configure)
