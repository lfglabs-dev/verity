import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.StructParamsAndBalancesSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "StructParamsAndBalancesSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()
  function feeRecipient()
  function lastReserveId()
  function reserves(Id)
  function holdings(Id, address)
  function computeId(AssetParams)
  function expectedReserveBalances(AssetParams, uint256)
  function expectedTotalSupplyAssets(AssetParams, uint256)
  function expectedSupplyAssets(AssetParams, address, uint256)
  function expectedBorrowAssets(AssetParams, address, uint256)
def model : CompilationModel := imported.model
-- Mapping slots and struct hashes use the actual Keccak oracle shared with differential execution.
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.StructParamsAndBalancesSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.StructParamsAndBalancesSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.StructParamsAndBalancesSequenceModel.model SolidityImportSmoke.StructParamsAndBalancesSequenceModel.oracle args
