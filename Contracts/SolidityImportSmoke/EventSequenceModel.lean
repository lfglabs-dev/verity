import Compiler.SolidityImport.SequenceRunner
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

/-! Handwritten model fixture for testing the sequence instrument. This is not
an imported Solidity fixture and makes no importer-coverage claim. -/
namespace SolidityImportSmoke.EventSequenceModel
open Compiler.CompilationModel

def model : CompilationModel :=
  { name := "SequenceFixture"
    fields := [{ name := "stored", ty := .uint256 }]
    events := [{ name := "Changed", params := [
      { name := "previous", ty := .uint256, kind := .indexed },
      { name := "next", ty := .uint256, kind := .unindexed }] }]
    constructor := none
    functions := [
      { name := "change", params := [{ name := "value", ty := .uint256 }]
        returnType := some .uint256
        body := [.letVar "old" (.storage "stored"), .setStorage "stored" (.param "value"),
          .emit "Changed" [.localVar "old", .param "value"],
          .returnValues [.localVar "old"]] },
      { name := "fail", params := [], returnType := none
        body := [.setStorage "stored" (.literal 99),
          .emit "Changed" [.literal 99, .literal 100], .panicCode (.literal 1)] },
      { name := "read", params := [], returnType := some .uint256
        body := [.returnValues [.storage "stored"]] } ] }

-- Scalar fixture bodies never reach either hash oracle.
def oracle : Denote.DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
end SolidityImportSmoke.EventSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.EventSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.EventSequenceModel.model SolidityImportSmoke.EventSequenceModel.oracle args
