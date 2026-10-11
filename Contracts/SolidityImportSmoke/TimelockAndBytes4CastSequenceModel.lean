import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.TimelockAndBytes4CastSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "TimelockAndBytes4CastSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()
  function supportsInterface(bytes4)
  function hashOperation(address, uint256, bytes, bytes32, bytes32)
  function getTimestamp(bytes32)
  function getOperationState(bytes32)
  function isOperation(bytes32)
  function isOperationPending(bytes32)
  function isOperationReady(bytes32)
  function isOperationDone(bytes32)
  function getMinDelay()
def model : CompilationModel := imported.model
-- Mapping slots use the actual Keccak oracle shared with differential execution.
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.TimelockAndBytes4CastSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.TimelockAndBytes4CastSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.TimelockAndBytes4CastSequenceModel.model SolidityImportSmoke.TimelockAndBytes4CastSequenceModel.oracle args
