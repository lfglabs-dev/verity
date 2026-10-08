import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.AbiHashingModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "AbiHashing.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract AbiHashing
  function scalar(uint128,address,bytes32,bool)
  function empty()
  function distinct(uint256,uint256)
  function composed(uint256,uint256)
  function marketMemory(Market,uint256)
  function marketCalldata(Market,uint256)
  function staticRoot(HashStatic)
  function arraysMemory(HashArrays)
  function arraysCalldata(HashArrays)
  function packedScalars(uint8,address,uint256,bytes32,bool)
  function idMarket(Market)
  function prefix0(uint256)
  function prefix1(uint256)
  function prefix11(uint256)
  function prefix31(uint256)
  function prefix32(uint256)
  function prefix33(uint256)
  function prefix63(uint256)
  function prefix64(uint256)
  function prefix65(uint256)
  function storeDigest(uint256,uint256)
  function readDigest()
def model : CompilationModel := imported.model
-- Mapping slots use the actual Keccak oracle shared with differential execution.
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.AbiHashingModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.AbiHashingModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.AbiHashingModel.model SolidityImportSmoke.AbiHashingModel.oracle args
