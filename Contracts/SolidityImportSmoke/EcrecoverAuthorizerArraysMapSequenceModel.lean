import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.EcrecoverAuthorizerArraysMapSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "EcrecoverAuthorizerArraysMapSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()
  function DOMAIN_TYPEHASH()
  function AUTHORIZATION_TYPEHASH()
  function domainSeparator()
  function hashAuthorization(Authorization)
  function hashTypedData(Authorization)
  function isAuthorized(address, address)
  function nonces(address)
  function latestAuthorization()
  function lastAuthorizationOf(address)
  function authorizationHistory(uint256)
  function verifyAndRecord(Authorization, Signature)
  function batchCheckAndSum(«address[]», «uint256[]»)
def model : CompilationModel := imported.model
-- Mapping and dynamic storage array slots use the actual Keccak oracle shared with differential execution.
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.EcrecoverAuthorizerArraysMapSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.EcrecoverAuthorizerArraysMapSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.EcrecoverAuthorizerArraysMapSequenceModel.model SolidityImportSmoke.EcrecoverAuthorizerArraysMapSequenceModel.oracle args
