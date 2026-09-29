import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

/-! Handwritten model fixture for testing the sequence instrument. This is not
an imported Solidity fixture and makes no importer-coverage claim. -/
namespace SolidityImportSmoke.ErrorSequenceModel
open Compiler.CompilationModel

def model : CompilationModel :=
  { name := "SequenceFixture"
    fields := [{ name := "stored", ty := .uint256 }]
    errors := [{ name := "BadValue", params := [.uint256] }]
    constructor := none
    functions := [
      { name := "change", params := [{ name := "value", ty := .uint256 }]
        returnType := some .uint256
        body := [.letVar "old" (.storage "stored"),
          .requireError (.param "value") "BadValue" [.localVar "old"], .setStorage "stored" (.param "value"),
          .returnValues [.localVar "old"]] },
      { name := "fail", params := [], returnType := none
        body := [.setStorage "stored" (.literal 99), .require (.literal 0) "échec"] },
      { name := "read", params := [], returnType := some .uint256
        body := [.returnValues [.storage "stored"]] } ] }

def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.ErrorSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.ErrorSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.ErrorSequenceModel.model SolidityImportSmoke.ErrorSequenceModel.oracle args
