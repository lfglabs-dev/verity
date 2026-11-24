import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.StaticOracleMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.CursorWhileModel
open Compiler.CompilationModel

solidity_import imported from "Contracts/SolidityImportSmoke" entry "CursorWhileFixture.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract CursorWhileFixture
  function pushItem(uint32)
  function pushBucketItem(uint32)
  function resetItems()
  function sumPackedLocal()
  function sumPackedUsingFor()
  function sumBucketLocal()
  function scanPackedWithOracle(address)

def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle

end SolidityImportSmoke.CursorWhileModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.CursorWhileModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.CursorWhileModel.model
        SolidityImportSmoke.CursorWhileModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.StaticOracleMocks.configure)
