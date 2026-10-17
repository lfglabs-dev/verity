import Compiler.SolidityImport.SequenceRunner
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

/-! Handwritten measuring fixture for actual byte-copy composition. It does not
claim Solidity importer admission or discharge the local low-level obligation. -/
namespace SolidityImportSmoke.PhysicalCopySequenceModel
open Compiler.CompilationModel

def model : CompilationModel :=
  { name := "SequenceFixture"
    fields := [{ name := "observed", ty := .uint256 }]
    constructor := none
    functions := [
      { name := "change", params := [{ name := "value", ty := .uint256 }]
        returnType := some .uint256
        body := [
          .mstore (.literal 0) (.param "value"),
          .calldatacopy (.literal 3) (.literal 4) (.literal 17),
          .mstore (.literal 128) (.literal 99),
          .letVar "result" (.mload (.literal 0)),
          .setStorage "observed" (.localVar "result"),
          .return (.localVar "result")]
        localObligations := [{
          name := "physical_copy_instrument"
          obligation := "Fixed offsets and extents in PhysicalCopySequence.sol; exact byte-copy composition is measured against the real EVM."
          proofStatus := .unchecked }] },
      { name := "fail", params := [], returnType := none
        body := [.setStorage "observed" (.literal 99), .panicCode (.literal 1)] },
      { name := "read", params := [], returnType := some .uint256
        body := [.return (.storage "observed")] } ] }

def oracle : Denote.DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
end SolidityImportSmoke.PhysicalCopySequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.PhysicalCopySequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.PhysicalCopySequenceModel.model SolidityImportSmoke.PhysicalCopySequenceModel.oracle args
