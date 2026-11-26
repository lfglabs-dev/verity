import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.ReentrantCallResponderMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

/-!
A/B/C driver for `PostCallStateAccess.sol` (`check_post_call_state_access.py` and
`check_reentrant_callback.py`): mapping writes and a checked subtraction after an
optional-bool low-level `CALL` (`SyntheticCallbackTransfer`).
-/
namespace SolidityImportSmoke.CallbackTransferSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "PostCallStateAccess.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticCallbackTransfer
  function deposit(address,uint256)
  function transferOut(address,address,uint256)
  function read(address)
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.CallbackTransferSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.CallbackTransferSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.CallbackTransferSequenceModel.model
        SolidityImportSmoke.CallbackTransferSequenceModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.ReentrantCallResponderMocks.configure
          SolidityImportSmoke.CallbackTransferSequenceModel.model
          SolidityImportSmoke.CallbackTransferSequenceModel.oracle)
