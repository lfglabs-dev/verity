import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.MarketParamsBalancesSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "MarketParamsBalancesSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()
  function feeRecipient()
  function lastMarketId()
  function market(Id)
  function position(Id, address)
  function computeId(MarketParams)
  function expectedMarketBalances(MarketParams, uint256)
  function expectedTotalSupplyAssets(MarketParams, uint256)
  function expectedSupplyAssets(MarketParams, address, uint256)
  function expectedBorrowAssets(MarketParams, address, uint256)
def model : CompilationModel := imported.model
-- Mapping slots and struct hashes use the actual Keccak oracle shared with differential execution.
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.MarketParamsBalancesSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.MarketParamsBalancesSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.MarketParamsBalancesSequenceModel.model SolidityImportSmoke.MarketParamsBalancesSequenceModel.oracle args
