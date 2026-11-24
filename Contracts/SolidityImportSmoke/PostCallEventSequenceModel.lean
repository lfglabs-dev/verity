import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.CallResponderMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

/-!
A/B/C driver for `PostCallStateAccess.sol` (`check_post_call_state_access.py`):
A log after a typed void interface call, and storage writes in the clauses of `try`
(`SyntheticPostCallEvent`).
-/
namespace SolidityImportSmoke.PostCallEventSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "PostCallStateAccess.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticPostCallEvent
  function notify(address,uint256)
  function tryNotify(address,uint256)
  function read()
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.PostCallEventSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.PostCallEventSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.PostCallEventSequenceModel.model
        SolidityImportSmoke.PostCallEventSequenceModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.CallResponderMocks.configure)
