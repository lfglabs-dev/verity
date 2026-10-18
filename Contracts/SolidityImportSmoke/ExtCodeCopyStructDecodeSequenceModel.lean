import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.ExtCodeCopyStructDecodeSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "ExtCodeCopyStructDecodeSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ExtCodeCopyStructDecodeSequence
  function store(Spec)
  function storeRaw(bytes,bytes32)
  function load(bytes32)
  function summary(address)
  function echo(Spec)
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle

/-- CREATE2 needs only the instrument-supplied parent gas; code reads use the
account world. No adversary is configured, so any other external interaction
fails closed. -/
def configure (input : Lean.Json) : Except String Denote.ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  let some gas := (← config.getObjValAs? String "gas").toNat? | throw "decimal CREATE2 gas required"
  return { gas := some gas }
end SolidityImportSmoke.ExtCodeCopyStructDecodeSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.ExtCodeCopyStructDecodeSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.ExtCodeCopyStructDecodeSequenceModel.model
        SolidityImportSmoke.ExtCodeCopyStructDecodeSequenceModel.oracle args
        (configure := SolidityImportSmoke.ExtCodeCopyStructDecodeSequenceModel.configure)
