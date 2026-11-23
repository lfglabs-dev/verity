import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
Event arguments whose inlined helper reassigns its own result, parameter or local lower the same
way whatever the state-variable count (#2830). `EventHelperPreludeOneSlot.sol` declares one state
variable and `EventHelperPreludeTwoSlots.sol` the same contract plus one unrelated state variable
and one unused function.

Such an argument's prelude holds `assignVar` statements. They used to be admitted only with more
than one state variable; with one, every function below was rejected with `event arguments
currently require total scalar expressions`. Now an `assignVar` is admitted when it writes a
binding the same argument's prelude declared earlier (always a fresh binding), so no other
argument reads it and the write commutes with the other arguments in either pipeline's order
(legacy evaluates indexed arguments last to first, via-IR left to right). Guards keep the
existing rules (one revert payload across arguments).

Values: solc 0.8.34 on Anvil (osaka, runs 466), both contracts and both pipelines, after
`seed(3, 1000)` (`nested[3][1] = 1000`). Each event is its indexed topics after topic 0, then
its data words.
-/
namespace SolidityImportSmoke.EventHelperPreludeStateCountChecks
open Compiler.CompilationModel Denote Verity.Core

solidity_import oneLegacy from "Contracts/SolidityImportSmoke" entry "EventHelperPreludeOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EventHelperPreludeOneSlot
  function helperTwice(uint256,uint256)
  function helperAndLocal(uint256)
  function storedPair(uint256,uint256)
  function guardedPair(uint256,uint256)
  function assembledMixed(uint256,uint256)

solidity_import oneIr from "Contracts/SolidityImportSmoke" entry "EventHelperPreludeOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EventHelperPreludeOneSlot
  function helperTwice(uint256,uint256)
  function helperAndLocal(uint256)
  function storedPair(uint256,uint256)
  function guardedPair(uint256,uint256)
  function assembledMixed(uint256,uint256)

solidity_import twoLegacy from "Contracts/SolidityImportSmoke" entry "EventHelperPreludeTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EventHelperPreludeTwoSlots
  function helperTwice(uint256,uint256)
  function helperAndLocal(uint256)
  function storedPair(uint256,uint256)
  function guardedPair(uint256,uint256)
  function assembledMixed(uint256,uint256)

solidity_import twoIr from "Contracts/SolidityImportSmoke" entry "EventHelperPreludeTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EventHelperPreludeTwoSlots
  function helperTwice(uint256,uint256)
  function helperAndLocal(uint256)
  function storedPair(uint256,uint256)
  function guardedPair(uint256,uint256)
  function assembledMixed(uint256,uint256)

private def body (model : CompilationModel) (name : String) : String :=
  match model.functions.find? (·.name == name) with
  | some f => (repr f.body).pretty 100000
  | none => ""

/-- The function imports and its body does not depend on the unrelated slot. -/
private def sameBody (one two : CompilationModel) (name : String) : Bool :=
  body one name != "" && body one name == body two name

/-- `nested[3][1]`: `keccak256(1 ++ keccak256(3 ++ 0))` (the mapping is slot 0 in both). -/
private def seededSlot : Nat :=
  96881385098724982336199523897110808670594804956223524465732136215137800375929

/-- Storage after `seed(3, 1000)`. -/
private def seeded : Verity.ContractState :=
  Verity.defaultState.writePhysicalSlot seededSlot (Uint256.ofNat 1000)

/-- Status, logged events and revert bytes of `name` on ABI argument words `args`. -/
private def observe (model : CompilationModel) (name : String) (args : List Nat) :
    Option (Bool × List (List Nat) × Option (List UInt8)) := do
  let fn ← model.functions.find? (·.name == name)
  let r := denoteFunction SolidityImport.Differential.oracle model fn
    { sender := 1, functionSelector := 0, args } seeded
  return (r.success, r.events, r.revertData)

/-- `name` logs exactly `event` on `args`. -/
private def logs (model : CompilationModel) (name : String) (args : List Nat)
    (event : List Nat) : Bool :=
  match observe model name args with
  | some (true, [e], _) => e == event
  | _ => false

/-- `name` reverts with empty data on `args` and logs nothing. -/
private def revertsEmpty (model : CompilationModel) (name : String) (args : List Nat) : Bool :=
  observe model name args == some (false, [], some [])

private def maxWord : Nat := 2 ^ 256 - 1

/-- Event declarations, so topic 0 (the signature hash) is the same on both contracts. -/
private def events (model : CompilationModel) : String := (repr model.events).pretty 100000

#guard sameBody oneLegacy.model twoLegacy.model "helperTwice"
#guard sameBody oneLegacy.model twoLegacy.model "helperAndLocal"
#guard sameBody oneLegacy.model twoLegacy.model "storedPair"
#guard sameBody oneLegacy.model twoLegacy.model "guardedPair"
#guard sameBody oneLegacy.model twoLegacy.model "assembledMixed"
#guard events oneLegacy.model == events twoLegacy.model
#guard sameBody oneIr.model twoIr.model "helperTwice"
#guard sameBody oneIr.model twoIr.model "helperAndLocal"
#guard sameBody oneIr.model twoIr.model "storedPair"
#guard sameBody oneIr.model twoIr.model "guardedPair"
#guard sameBody oneIr.model twoIr.model "assembledMixed"
#guard events oneIr.model == events twoIr.model

#guard logs oneLegacy.model "helperTwice" [1, 2] [84, 87]
#guard logs oneLegacy.model "helperTwice" [maxWord, 0] [maxWord - 0x55, 0x55]
#guard logs oneLegacy.model "helperAndLocal" [5] [5, 261]
#guard logs oneLegacy.model "helperAndLocal" [256] [256, 256]
#guard logs oneLegacy.model "storedPair" [3, 4] [1003, 4]
#guard logs oneLegacy.model "storedPair" [4, 3] [4, 1003]
#guard logs oneLegacy.model "guardedPair" [1, 2] [0, 3]
#guard revertsEmpty oneLegacy.model "guardedPair" [0, 2]
#guard revertsEmpty oneLegacy.model "guardedPair" [1, 0]
#guard revertsEmpty oneLegacy.model "guardedPair" [0, 0]
#guard logs oneLegacy.model "assembledMixed" [9, 10] [14, 95, 265]

#guard logs oneIr.model "helperTwice" [1, 2] [84, 87]
#guard logs oneIr.model "helperTwice" [maxWord, 0] [maxWord - 0x55, 0x55]
#guard logs oneIr.model "helperAndLocal" [5] [5, 261]
#guard logs oneIr.model "helperAndLocal" [256] [256, 256]
#guard logs oneIr.model "storedPair" [3, 4] [1003, 4]
#guard logs oneIr.model "storedPair" [4, 3] [4, 1003]
#guard logs oneIr.model "guardedPair" [1, 2] [0, 3]
#guard revertsEmpty oneIr.model "guardedPair" [0, 2]
#guard revertsEmpty oneIr.model "guardedPair" [1, 0]
#guard revertsEmpty oneIr.model "guardedPair" [0, 0]
#guard logs oneIr.model "assembledMixed" [9, 10] [14, 95, 265]

#guard logs twoLegacy.model "helperTwice" [1, 2] [84, 87]
#guard logs twoLegacy.model "helperTwice" [maxWord, 0] [maxWord - 0x55, 0x55]
#guard logs twoLegacy.model "helperAndLocal" [5] [5, 261]
#guard logs twoLegacy.model "helperAndLocal" [256] [256, 256]
#guard logs twoLegacy.model "storedPair" [3, 4] [1003, 4]
#guard logs twoLegacy.model "storedPair" [4, 3] [4, 1003]
#guard logs twoLegacy.model "guardedPair" [1, 2] [0, 3]
#guard revertsEmpty twoLegacy.model "guardedPair" [0, 2]
#guard revertsEmpty twoLegacy.model "guardedPair" [1, 0]
#guard revertsEmpty twoLegacy.model "guardedPair" [0, 0]
#guard logs twoLegacy.model "assembledMixed" [9, 10] [14, 95, 265]

#guard logs twoIr.model "helperTwice" [1, 2] [84, 87]
#guard logs twoIr.model "helperTwice" [maxWord, 0] [maxWord - 0x55, 0x55]
#guard logs twoIr.model "helperAndLocal" [5] [5, 261]
#guard logs twoIr.model "helperAndLocal" [256] [256, 256]
#guard logs twoIr.model "storedPair" [3, 4] [1003, 4]
#guard logs twoIr.model "storedPair" [4, 3] [4, 1003]
#guard logs twoIr.model "guardedPair" [1, 2] [0, 3]
#guard revertsEmpty twoIr.model "guardedPair" [0, 2]
#guard revertsEmpty twoIr.model "guardedPair" [1, 0]
#guard revertsEmpty twoIr.model "guardedPair" [0, 0]
#guard logs twoIr.model "assembledMixed" [9, 10] [14, 95, 265]

end SolidityImportSmoke.EventHelperPreludeStateCountChecks
