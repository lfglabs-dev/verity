import Compiler.SolidityImport.SequenceRunner
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

/-! Handwritten measuring fixture for selector-adjacent calldata windows. It does not
claim Solidity importer admission or discharge the local low-level obligation. -/
namespace SolidityImportSmoke.CalldataWindowSequenceModel
open Compiler.CompilationModel

def model : CompilationModel :=
  { name := "SequenceFixture"
    fields := [{ name := "observed", ty := .uint256 }]
    constructor := none
    functions := [
      { name := "change", params := [{ name := "value", ty := .uint256 }]
        returnType := some .uint256
        body := [
          .letVar "result" (.calldataload (.mod (.param "value") (.literal 4))),
          .setStorage "observed" (.localVar "result"),
          .return (.localVar "result")]
        localObligations := [{
          name := "calldata_window_instrument"
          obligation := "Offsets value % 4 in CalldataWindowSequence.sol; exact selector/ABI boundary windows are measured against the real EVM."
          proofStatus := .unchecked }] },
      { name := "fail", params := [], returnType := none
        body := [.setStorage "observed" (.literal 99), .panicCode (.literal 1)] },
      { name := "read", params := [], returnType := some .uint256
        body := [.return (.storage "observed")] } ] }

def oracle : Denote.DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
end SolidityImportSmoke.CalldataWindowSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.CalldataWindowSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.CalldataWindowSequenceModel.model SolidityImportSmoke.CalldataWindowSequenceModel.oracle args
