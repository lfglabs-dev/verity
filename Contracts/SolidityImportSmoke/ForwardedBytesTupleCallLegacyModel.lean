import Contracts.SolidityImportSmoke.ForwardedBytesTupleCallMocks
import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

/-!
Legacy-pipeline A/B/C driver and trust-surface checks for `ForwardedBytesTupleCall.sol`
(Refs #2803, Refs #2842).
-/
namespace SolidityImportSmoke.ForwardedBytesTupleCallLegacyModel

open Compiler.CompilationModel Compiler.CompilationModel.Denote

solidity_import importedLegacy from "Contracts/SolidityImportSmoke" entry "ForwardedBytesTupleCall.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ForwardedBytesTupleCall
  function setTarget(address)
  function pingCallback()
  function guardedPing()
  function state()
  function exec(address,uint256,bytes,Operation,bool)
  function execUnlocked(address,uint256,bytes,Operation,bool)
  function execEnum(uint256)

def model : CompilationModel := importedLegacy.model
def oracle : DenoteOracle := SolidityImport.Differential.oracle

private def trustFlags (m : CompilationModel) (name : String) :
    Option (Bool × Bool × Bool × List String) :=
  (m.functions.find? (·.name == name)).map fun f =>
    (f.allowPostInteractionWrites, f.reentrancyTrusted, f.reentrancyAdversarial,
      f.localObligations.map (·.name))

#guard trustFlags model "exec" ==
  some (true, false, true, ["solidity_explicit_abi", "solidity_post_call_state_access"])
#guard trustFlags model "execUnlocked" ==
  some (true, false, true, ["solidity_explicit_abi", "solidity_post_call_state_access"])
#guard trustFlags model "execEnum" ==
  some (true, false, true, ["solidity_scalar_abi_entry", "solidity_post_call_state_access"])

end SolidityImportSmoke.ForwardedBytesTupleCallLegacyModel

def main (args : List String) : IO UInt32 := do
  let m := SolidityImportSmoke.ForwardedBytesTupleCallLegacyModel.model
  let o := SolidityImportSmoke.ForwardedBytesTupleCallLegacyModel.oracle
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile m selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run m o args
        (configure := SolidityImportSmoke.ForwardedBytesTupleCallMocks.configure m o)
