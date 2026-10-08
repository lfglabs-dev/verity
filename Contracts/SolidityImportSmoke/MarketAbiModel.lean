import Compiler.SolidityImport.Import
import Compiler.CompilationModel
import Compiler.SolidityImport.TransactionAccess
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.MarketAbiModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "MarketAbi.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract MarketAbi
  function memoryUnused(Market,uint256)
  function memoryMaturity(Market,uint256)
  function memoryTokenLate(Market,uint256)
  function memoryTokenSecond(Market,uint256)
  function memoryMidnight(Market,uint256)
  function calldataUnused(Market,uint256)
  function calldataMaturity(Market,uint256)
  function calldataTokenLate(Market,uint256)
  function calldataTokenSecond(Market,uint256)
  function calldataMidnight(Market,uint256)
  function memoryLength(Market,uint256)
  function calldataLength(Market,uint256)
def model : CompilationModel := imported.model
end SolidityImportSmoke.MarketAbiModel

open Lean Compiler.CompilationModel SolidityImportSmoke.MarketAbiModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile selectorsFile))
      let rows ← IO.ofExcept parsed.getArr?
      let named ← rows.toList.mapM fun row => do
        let name ← IO.ofExcept (row.getObjValAs? String "name")
        let selector ← IO.ofExcept (row.getObjValAs? Nat "selector")
        pure (name, selector)
      unless named.length == model.functions.length &&
          (named.map Prod.fst).eraseDups.length == named.length &&
          (named.map Prod.snd).eraseDups.length == named.length do
        throw (IO.userError "ABI selector manifest is incomplete or duplicated")
      let selectors ← model.functions.mapM fun fn => do
        let some entry := named.find? (fun entry => entry.1 == fn.name)
          | throw (IO.userError s!"ABI selector manifest lacks {fn.name}")
        pure entry.2
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
            fn.params == [{ name := "market", ty := .tuple [.uint256, .address, .address,
              .array (.tuple [.address, .uint256, .uint256, .address]),
              .uint256, .uint256, .address, .address] },
              { name := "flag", ty := .uint256 }] do
          throw (IO.userError "complete full-Market ABI signature/policy mismatch")
        let some bindings := Denote.bindExternalParams selector fn.bindingParams values
          | throw (IO.userError "complete scalar ABI fixture unexpectedly failed parameter binding")
        let traced ← IO.ofExcept (SolidityImport.Transactions.traceStraightLine oracle
          (Denote.effectiveFields model) { world, bindings, selector, errors := model.errors }
          fn.body model.events)
        unless traced.touched.isEmpty do
          throw (IO.userError "pure full-Market fixture accessed storage")
        let frame ← IO.ofExcept (SolidityImport.Transactions.finishFrame world traced.outcome)
        unless frame.world.events.isEmpty do
          throw (IO.userError "pure full-Market fixture emitted an event")
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
