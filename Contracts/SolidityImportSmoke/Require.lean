import Compiler.SolidityImport.Import
open Compiler.CompilationModel
open Compiler.CompilationModel.SolidityImport
solidity_profile requireBuild where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"
solidity_import requireFixture from "Contracts/SolidityImportSmoke" entry "Require.sol" using requireBuild
  contract RequireFixture
  function checked(uint256)
