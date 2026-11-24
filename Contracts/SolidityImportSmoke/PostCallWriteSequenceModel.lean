import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.CallResponderMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

/-!
A/B/C driver for `PostCallStateAccess.sol` (`check_post_call_state_access.py`):
Storage reads and writes after a typed void interface call (`SyntheticPostCallWrite`).
-/
namespace SolidityImportSmoke.PostCallWriteSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "PostCallStateAccess.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticPostCallWrite
  function pingThenCount(address,uint256)
  function pingThenRead(address)
  function read()
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.PostCallWriteSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.PostCallWriteSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.PostCallWriteSequenceModel.model
        SolidityImportSmoke.PostCallWriteSequenceModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.CallResponderMocks.configure)
