import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.AccessManagerTargetRoleSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "AccessManagerTargetRoleSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()
  function getTargetFunctionRole(address, bytes4)
  function setSingleTargetFunctionRole(address, bytes4, uint64)
  function setTargetFunctionRole(address, «bytes4[]», uint64)
  function decodeSelectorsAndRole(bytes)
  function canCall(address, address, bytes4)
  function checkCallPermission(address, address, bytes)
  function configureMemberAndTarget(address, address, uint64, uint32, uint32, bool)
  function parseHexByte(bytes1, bytes)
def model : CompilationModel := imported.model
-- Mapping slots use the actual Keccak oracle shared with differential execution.
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.AccessManagerTargetRoleSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.AccessManagerTargetRoleSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.AccessManagerTargetRoleSequenceModel.model SolidityImportSmoke.AccessManagerTargetRoleSequenceModel.oracle args
