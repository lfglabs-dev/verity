import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.StoragePointerGuardChecks

open Compiler.CompilationModel

solidity_profile storagePointerGuard where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_profile storagePointerGuardLegacy where
  evmVersion := "osaka"
  viaIR := false
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import fixture from "Contracts/SolidityImportSmoke"
  entry "StoragePointerGuardSequence.sol"
  using storagePointerGuard
  contract StoragePointerGuardFixture
  function add(uint256,uint256)
  function addChecked(uint256,uint256)
  function addRaw(uint256,uint256)
  function store(uint256,bool,uint256)
  function storeRaw(uint256,bool,uint256)
  function read(uint256)
  function readRaw(uint256)

solidity_import fixtureLegacy from "Contracts/SolidityImportSmoke"
  entry "StoragePointerGuardSequence.sol"
  using storagePointerGuardLegacy
  contract StoragePointerGuardFixture
  function add(uint256,uint256)
  function addChecked(uint256,uint256)
  function addRaw(uint256,uint256)
  function store(uint256,bool,uint256)
  function storeRaw(uint256,bool,uint256)
  function read(uint256)
  function readRaw(uint256)

-- Negative control 1: statement after an explicit `return item;` must remain rejected.
/--
error: StoragePointerGuardSequence.sol:117:9: ExpressionStatement: [solidity-import:unsupported] unreachable statement after storage pointer helper return
closure: StoragePointerGuardRejections.readAfterReturn -> StoragePointerGuardRejections._afterReturn
require(item.active)
-/
#guard_msgs in
solidity_import rejectAfterReturn from "Contracts/SolidityImportSmoke"
  entry "StoragePointerGuardSequence.sol"
  using storagePointerGuard
  contract StoragePointerGuardRejections
  function readAfterReturn(uint256)

-- Negative control 2: `return` inside a nested control-flow branch must remain rejected.
/--
error: StoragePointerGuardSequence.sol:121:9: IfStatement: [solidity-import:unsupported] storage pointer helper return from a nested control-flow branch is outside this slice
closure: StoragePointerGuardRejections.readBranchReturn -> StoragePointerGuardRejections._branchReturn
if (id > 0) {
            return items[id];
        }
-/
#guard_msgs in
solidity_import rejectBranchReturn from "Contracts/SolidityImportSmoke"
  entry "StoragePointerGuardSequence.sol"
  using storagePointerGuard
  contract StoragePointerGuardRejections
  function readBranchReturn(uint256)

private def runCall (world : Verity.ContractState) (name : String) (args : List Nat) :
    Option (Bool × List Nat × Option (List UInt8) × List (List Nat) × Verity.ContractState) := do
  let fn ← fixture.model.functions.find? (·.name == name)
  let tx : Denote.DenoteTransaction := { sender := 1, functionSelector := 0, args := args }
  let worldWithTx := Denote.withTransactionContext world tx
  let bindings ← Denote.bindExternalParams tx.functionSelector fn.bindingParams tx.args
  let state : Denote.DenoteState := {
    world := worldWithTx
    bindings := bindings
    selector := tx.functionSelector
    errors := fixture.model.errors
  }
  match Denote.execStmtList SolidityImport.Differential.oracle
      (Denote.effectiveFields fixture.model) state fn.body with
  | .continue st => some (true, [], none, Denote.encodeEvents st.world.events, st.world)
  | .stop st => some (true, st.observedReturnWords.getD [], none, Denote.encodeEvents st.world.events, st.world)
  | .return v st => some (true, [v], none, Denote.encodeEvents st.world.events, st.world)
  | .revert => some (false, [], none, [], world)
  | .revertWithData bytes => some (false, [], some bytes, [], world)

private def customErrorData (name : String) (args : List Nat) : Option (List UInt8) :=
  Denote.customErrorBytes SolidityImport.Differential.oracle fixture.model.errors name args

-- Guarded storage-pointer helpers (`_activeItem`, `_checkedItem`, `_activeRawItem`) revert
-- with `ItemInactive(id)` when inactive, and mutate + return the updated amount when active.
#guard
  match runCall Verity.defaultState "add" [7, 5] with
  | some (false, _, some bytes, _, _) => some bytes == customErrorData "ItemInactive" [7]
  | _ => false

#guard
  match runCall Verity.defaultState "addChecked" [7, 5] with
  | some (false, _, some bytes, _, _) => some bytes == customErrorData "ItemInactive" [7]
  | _ => false

#guard
  match runCall Verity.defaultState "addRaw" [7, 5] with
  | some (false, _, some bytes, _, _) => some bytes == customErrorData "ItemInactive" [7]
  | _ => false

#guard
  match runCall Verity.defaultState "store" [7, 1, 10] with
  | some (true, _, _, _, s1) =>
      match runCall s1 "add" [7, 5] with
      | some (true, [15], _, [[7, 15]], s2) =>
          match runCall s2 "addChecked" [7, 20] with
          | some (true, [35], _, _, _) => true
          | _ => false
      | _ => false
  | _ => false

#guard
  match runCall Verity.defaultState "storeRaw" [9, 1, 100] with
  | some (true, _, _, _, s1) =>
      match runCall s1 "addRaw" [9, 25] with
      | some (true, [125], _, _, _) => true
      | _ => false
  | _ => false

end SolidityImportSmoke.StoragePointerGuardChecks
