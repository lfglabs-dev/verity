import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.UniswapV4TypesAndTransientSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "UniswapV4TypesAndTransientSequence.sol"
  using { solc := "0.8.26+commit.8a97fa7a", evmVersion := "cancun", viaIR := true, optimizerRuns := some 200, bytecodeHash := "none" }
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()
  function supportsInterface(bytes4)
  function extsload(bytes32)
  function exttload(bytes32)
  function setPoolFee(PoolKey, uint24)
  function accountPoolBalanceDelta(PoolKey, int128, int128)
  function recordPositionLiquidity(int24, int24, bytes32, uint256)
def model : CompilationModel := imported.model
-- Mapping slots use the actual Keccak oracle shared with differential execution.
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.UniswapV4TypesAndTransientSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.UniswapV4TypesAndTransientSequenceModel.model selectors .cancun)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.UniswapV4TypesAndTransientSequenceModel.model SolidityImportSmoke.UniswapV4TypesAndTransientSequenceModel.oracle args
