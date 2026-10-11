import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.EcdsaMerkleCheckpointsStorageSlotSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "EcdsaMerkleCheckpointsStorageSlotSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()
  function recoverFromBytes(bytes32, bytes)
  function recoverFromCompact(bytes32, bytes32, bytes32)
  function verifyMerkle(«bytes32[]», bytes32, bytes32)
  function rawSlotLabel()
  function rawSlotPayload()
  function checkpointUpperRecent(uint32)
def model : CompilationModel := imported.model
-- Mapping slots use the actual Keccak oracle shared with differential execution.
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.EcdsaMerkleCheckpointsStorageSlotSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.EcdsaMerkleCheckpointsStorageSlotSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.EcdsaMerkleCheckpointsStorageSlotSequenceModel.model SolidityImportSmoke.EcdsaMerkleCheckpointsStorageSlotSequenceModel.oracle args
