import Compiler.SolidityImport.Import
import Compiler.CompilationModel

namespace SolidityImportSmoke.SolcVersionProbeAmsterdamModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "SolcVersionProbe.sol"
  using { solc := "0.8.35+commit.47b9dedd", evmVersion := "amsterdam", viaIR := true,
          optimizerRuns := some 466, bytecodeHash := "none" }
  contract SolcVersionProbe
  function DOMAIN_TYPEHASH()
  function counters(address)
  function digest(bytes32)
  function bump(uint256)
def model : CompilationModel := imported.model
end SolidityImportSmoke.SolcVersionProbeAmsterdamModel
