import Compiler.SolidityImport.Import
import Compiler.CompilationModel
import Compiler.SolidityImport.Transactions
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.StructValidationOrderModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "StructValidationOrder.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract StructValidationOrder
  function memoryUnused(Pair)
  function calldataUnused(Pair)
  function memoryLate(Pair,uint256)
  function calldataLate(Pair,uint256)
  function memoryKindsUnused(Kinds)
  function calldataKindsUnused(Kinds)
  function memoryKindsLate(Kinds,uint256)
  function calldataKindsLate(Kinds,uint256)
def model : CompilationModel := imported.model
end SolidityImportSmoke.StructValidationOrderModel

open Lean Compiler.CompilationModel SolidityImportSmoke.StructValidationOrderModel

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
        let some bindings := Denote.bindExternalParams selector fn.params values
          | throw (IO.userError "complete scalar ABI fixture unexpectedly failed parameter binding")
        let outcome := Denote.execStmtList oracle (Denote.effectiveFields model)
          { world, bindings, selector, errors := model.errors } fn.body
        let frame ← IO.ofExcept (SolidityImport.Transactions.finishFrame world outcome)
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
