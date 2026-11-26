import Compiler.SolidityImport.Import
import Compiler.CompilationModel

namespace SolidityImportSmoke.SolcVersionProbeSolc0838Model
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "SolcVersionProbe.sol"
  using { solc := "0.8.38+commit.1835d247", evmVersion := "cancun", viaIR := true,
          optimizerRuns := some 10, bytecodeHash := "none" }
  contract SolcVersionProbe
  function DOMAIN_TYPEHASH()
  function counters(address)
  function digest(bytes32)
  function bump(uint256)
def model : CompilationModel := imported.model
end SolidityImportSmoke.SolcVersionProbeSolc0838Model
