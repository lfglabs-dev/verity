import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.StaticOracleMocks

open Compiler.CompilationModel

-- Manual integration fixture: source importer admission is still pending.
def oracleSequenceModel : CompilationModel :=
  { name := "OracleSequenceCaller"
    fields := [{ name := "saved", ty := .uint256 }]
    constructor := none
    functions := [
      { name := "read"
        params := [{ name := "target", ty := .address }, { name := "next", ty := .uint256 }]
        returnType := some .uint256
        localObligations := [
          { name := "manual_abi_memory_preamble"
            obligation := "mstore(64,128) matches source Solidity entry preamble; differential fixture only"
            proofStatus := .unchecked }]
        body := [.mstore (.literal 64) (.literal 128),
                 .setStorage "saved" (.param "next"),
                 .ecm (Compiler.ECM.SolidityStaticCall.uint256Module "result" 0xa035b1fe 0)
                   [.param "target"],
                 .return (.localVar "result")] },
      { name := "readAndReject"
        params := [{ name := "target", ty := .address }, { name := "next", ty := .uint256 },
                   { name := "reject", ty := .uint256 }]
        returnType := some .uint256
        localObligations := [
          { name := "manual_abi_memory_preamble"
            obligation := "mstore(64,128) matches source Solidity entry preamble; differential fixture only"
            proofStatus := .unchecked }]
        body := [.mstore (.literal 64) (.literal 128),
                 .setStorage "saved" (.param "next"),
                 .ecm (Compiler.ECM.SolidityStaticCall.uint256Module "result" 0xa035b1fe 0)
                   [.param "target"],
                 .ite (.param "reject") [.revertEmpty] [],
                 .return (.localVar "result")] }] }

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        oracleSequenceModel selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      SolidityImport.SequenceRunner.run oracleSequenceModel
        { mappingSlot := fun _ _ => 0, keccakMemorySlice := fun _ _ _ => 0 } args
        (configure := SolidityImport.StaticOracleMocks.configure)
