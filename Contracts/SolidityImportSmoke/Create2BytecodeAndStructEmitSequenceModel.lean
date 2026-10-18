import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.Create2BytecodeAndStructEmitSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "Create2BytecodeAndStructEmitSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract Create2BytecodeAndStructEmitSequence
  function create(Spec)
  function storeAt(Spec,bytes32)
  function storeLeg(Leg,uint256)
  function count()
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle

/-- CREATE2 needs only the instrument-supplied parent gas: no adversary is
configured, so any other external interaction fails closed. -/
def configure (input : Lean.Json) : Except String Denote.ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  let some gas := (← config.getObjValAs? String "gas").toNat? | throw "decimal CREATE2 gas required"
  return { gas := some gas }
end SolidityImportSmoke.Create2BytecodeAndStructEmitSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.Create2BytecodeAndStructEmitSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.Create2BytecodeAndStructEmitSequenceModel.model
        SolidityImportSmoke.Create2BytecodeAndStructEmitSequenceModel.oracle args
        (configure := SolidityImportSmoke.Create2BytecodeAndStructEmitSequenceModel.configure)
