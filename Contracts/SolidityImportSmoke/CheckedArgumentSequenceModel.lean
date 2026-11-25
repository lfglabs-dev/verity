import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.CallResponderMocks
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.CheckedArgumentSequenceModel
open Compiler.CompilationModel

solidity_import imported from "Contracts/SolidityImportSmoke" entry "CheckedArgumentSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract CheckedArgumentFixture
  function callChecked(address,uint256,uint256)
  function callOverflow(address,uint256)
  function callDynamic(address,bytes,uint256)
  function callVoid(address,uint256,uint256)
  function emitMeasured(uint256,uint256)
  function revertField(uint256)
  function revertNamedField()
  function callEffectfulPost(address,uint256)
  function callEffectfulPre(address,uint256)
  function revertEffectful(uint256)
  function requireEffectful(bool,uint256)
  function seedWeight(uint256)
  function read()

def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle

end SolidityImportSmoke.CheckedArgumentSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.CheckedArgumentSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.CheckedArgumentSequenceModel.model
        SolidityImportSmoke.CheckedArgumentSequenceModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.CallResponderMocks.configure)
