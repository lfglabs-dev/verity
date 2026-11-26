import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.ReentrantCallResponderMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

/-!
Via-IR A/B/C driver for `StatefulComparisonStructMapRhs.sol`
(`check_stateful_comparison_and_struct_map_rhs.py`): stateful external, internal, and linked-library
calls in binary comparisons and storage-struct mapping RHS assignments.
-/
namespace SolidityImportSmoke.StatefulComparisonStructMapRhsSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke"
  entry "StatefulComparisonStructMapRhs.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none",
          linkedLibrariesMatchSource := true }
  contract StatefulComparisonStructMapRhs
  function assertDeployMatch(address,bytes,address)
  function compareCallAndState(address,uint256,uint256,address)
  function setDirectKeyInternal(address,bytes32,bytes32,bytes)
  function setComputedKeyLinked(address,bytes32,address,bytes4,uint256)
  function setSideEffectKeysOrder(address,uint256,bytes32,address,bytes4,uint256)
  function setReentrantStorageKeys(address,bytes4,uint256)
  function reenterMutate(bytes32,address,uint256)
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.StatefulComparisonStructMapRhsSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.StatefulComparisonStructMapRhsSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.StatefulComparisonStructMapRhsSequenceModel.model
        SolidityImportSmoke.StatefulComparisonStructMapRhsSequenceModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.ReentrantCallResponderMocks.configure
          SolidityImportSmoke.StatefulComparisonStructMapRhsSequenceModel.model
          SolidityImportSmoke.StatefulComparisonStructMapRhsSequenceModel.oracle)
