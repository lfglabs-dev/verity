import Compiler.SolidityImport.Import
import Compiler.CompilationModel

namespace SolidityImportSmoke.SolcVersionProbeOsakaModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "SolcVersionProbe.sol"
  using { solc := "0.8.34+commit.80d5c536", evmVersion := "osaka", viaIR := true,
          optimizerRuns := some 466, bytecodeHash := "none" }
  contract SolcVersionProbe
  function DOMAIN_TYPEHASH()
  function counters(address)
  function digest(bytes32)
  function bump(uint256)
def model : CompilationModel := imported.model
end SolidityImportSmoke.SolcVersionProbeOsakaModel
