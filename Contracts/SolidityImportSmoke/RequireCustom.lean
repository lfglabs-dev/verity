import Compiler.SolidityImport.Import
open Compiler.CompilationModel
open Compiler.CompilationModel.SolidityImport
solidity_profile requireCustomBuild where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"
solidity_import requireCustomFixture from "Contracts/SolidityImportSmoke" entry "RequireCustom.sol" using requireCustomBuild
  contract RequireCustomFixture
  function checked(uint256, address, bool, bytes32, uint8, uint16, uint128)
