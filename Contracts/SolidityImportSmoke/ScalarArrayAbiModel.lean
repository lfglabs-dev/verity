import Compiler.SolidityImport.Import
import Compiler.CompilationModel
import Compiler.SolidityImport.TransactionAccess
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.ScalarArrayAbiModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "ScalarArrayAbi.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ScalarArrayAbi
  function memoryUnused(Box,uint256)
  function memoryElement(Box,uint256)
  function memorySecond(Box,uint256)
  function calldataUnused(Box,uint256)
  function calldataElement(Box,uint256)
  function calldataSecond(Box,uint256)
def model : CompilationModel := imported.model
end SolidityImportSmoke.ScalarArrayAbiModel

open Lean Compiler.CompilationModel SolidityImportSmoke.ScalarArrayAbiModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept ((← IO.ofExcept parsed.getArr?).toList.mapM Json.getNat?)
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | ["observe", input, output] =>
      let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
      let rows ← IO.ofExcept parsed.getArr?
      let mut results : Array Json := #[]
      for row in rows do
        let name ← IO.ofExcept (row.getObjValAs? String "function")
        let selector ← IO.ofExcept (row.getObjValAs? Nat "selector")
        let raw ← IO.ofExcept (row.getObjValAs? (List String) "words")
        let values ← raw.mapM fun word => do
          let some value := word.toNat? | throw (IO.userError "invalid raw word")
          pure value
        let some fn := model.functions.find? (·.name == name) | throw (IO.userError "unknown ABI probe")
        let oracle : Denote.DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
        let tx : Denote.DenoteTransaction :=
          { sender := 1, functionSelector := selector, args := values }
        let result := Denote.denoteFunction oracle model fn tx Verity.defaultState
        let world := Denote.withTransactionContext Verity.defaultState tx
        unless imported.report.projections.isEmpty && fn.abiDecoding == .explicitPrelude &&
            fn.params == [{ name := "box", ty := .tuple [.array (.uintN 128)] },
              { name := "flag", ty := .uint256 }] do
          throw (IO.userError "complete scalar-array ABI signature/policy mismatch")
        let some bindings := Denote.bindExternalParams selector fn.bindingParams values
          | throw (IO.userError "complete scalar ABI fixture unexpectedly failed parameter binding")
        let traced ← IO.ofExcept (SolidityImport.Transactions.traceStraightLine oracle
          (Denote.effectiveFields model) { world, bindings, selector, errors := model.errors }
          fn.body model.events)
        unless traced.touched.isEmpty do
          throw (IO.userError "pure scalar-array fixture accessed storage")
        let frame ← IO.ofExcept (SolidityImport.Transactions.finishFrame world traced.outcome)
        unless frame.world.events.isEmpty do
          throw (IO.userError "pure scalar-array fixture emitted an event")
        unless frame.success == result.success do
          throw (IO.userError "public Denote and observed frame statuses disagree")
        if frame.success then
          unless frame.data == result.returnWords.flatMap Denote.wordBytes do
            throw (IO.userError "public Denote and observed return bytes disagree")
        results := results.push (Json.mkObj [("success", toJson result.success),
          ("words", toJson (result.returnWords.map toString)),
          ("data", toJson (frame.data.map UInt8.toNat)), ("events", toJson result.events)])
      IO.FS.writeFile output (Json.arr results).pretty
      return 0
  | _ => throw (IO.userError "expected compile or observe arguments")
