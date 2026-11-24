import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.Transactions

namespace SolidityImportSmoke.TransientNeutralAssemblyChecks
open Compiler.CompilationModel Denote
open Compiler.CompilationModel.SolidityImport.Transactions

/-! Transient state variables in closures whose inline assembly is transient-neutral: a
namespaced storage getter (`$.slot := LOCATION`), full-word Yul locals and a full-word Yul
local in a modifier. Every expected value below was observed on solc 0.8.34 (optimizer
runs 10, Cancun) with the legacy and via-IR pipelines, which agree: calls in one
transaction through a Foundry probe, and separate transactions on Anvil. -/

solidity_profile irProfile where
  evmVersion := "cancun"
  viaIR := true
  optimizerRuns := some 10
  bytecodeHash := "none"

solidity_profile legacyProfile where
  evmVersion := "cancun"
  viaIR := false
  optimizerRuns := some 10
  bytecodeHash := "none"

solidity_import ir from "Contracts/SolidityImportSmoke" entry "TransientNeutralAssemblySequence.sol"
  using irProfile
  contract TransientNeutralAssemblySequence
  function enter()
  function act(uint256)
  function close()
  function state()
  function fullWordLocal(uint256)
  function signedAndBytes(int256,bytes32)
  function inModifier()
  function namespacedSlotRead()

solidity_import legacy from "Contracts/SolidityImportSmoke" entry "TransientNeutralAssemblySequence.sol"
  using legacyProfile
  contract TransientNeutralAssemblySequence
  function enter()
  function act(uint256)
  function close()
  function state()
  function fullWordLocal(uint256)
  function signedAndBytes(int256,bytes32)
  function inModifier()
  function namespacedSlotRead()

private def oracle := SolidityImport.Differential.oracle

private def bothModels (check : CompilationModel → Bool) : Bool :=
  check ir.model && check legacy.model

/-- The namespaced storage location of `Main` (`total`, then `checked`). -/
private def mainSlot := 0x9ee206bc124160cd40c828f4614e7d92dc2e9850e42b9bc6bcad127f50b4a500

/-- One call frame inside the current transaction: fresh memory and return data, storage
and transient storage as the previous call of the transaction left them. -/
private def callFrame (model : CompilationModel) (world : Verity.ContractState)
    (name : String) (args : List Nat) : Option FrameResult := do
  let fn ← model.functions.find? (·.name == name)
  let bindings ← bindExternalParams 0 fn.bindingParams args
  let start := { world with memory := fun _ => 0, byteMemory := DenoteMemory.Memory.empty,
                            returndata := [], events := [], calls := [] }
  (finishFrame start (execStmtList oracle (effectiveFields model)
    { world := start, bindings, errors := model.errors } fn.body)).toOption

/-- Calls of one transaction, which starts with `beginTransaction`: success and return
words of each call, then the persistent `Main` words and transient slots 0 to 2. -/
private def runTransaction (model : CompilationModel) (world : Verity.ContractState)
    (calls : List (String × List Nat)) :
    Option (List (Bool × List UInt8) × Verity.ContractState) := do
  let mut current := beginTransaction world
  let mut seen : List (Bool × List UInt8) := []
  for (name, args) in calls do
    let r ← callFrame model current name args
    seen := seen ++ [(r.success, r.data)]
    current := r.world
  return (seen, current)

private def words (ws : List Nat) : List UInt8 := ws.flatMap wordBytes

private def mainWords (world : Verity.ContractState) : List Nat :=
  [(world.readSlot mainSlot).val, (world.readSlot (mainSlot + 1)).val]

private def transientWords (world : Verity.ContractState) : List Nat :=
  [0, 1, 2].map fun slot => (world.readTransient slot).val

-- One transaction: a flag set by one call defers the counter updates of the next calls to
-- a transient queue, and a later call drains it into the namespaced storage.
private def batchInOneTransaction (model : CompilationModel) : Bool :=
  match runTransaction model Verity.defaultState
      [("state", []), ("act", [3]), ("enter", []), ("act", [5]), ("act", [7]),
       ("state", []), ("close", []), ("state", []), ("act", [1]), ("state", [])] with
  | none => false
  | some (results, final) =>
      results == [(true, words [0, 0, 0, 0]), (true, words [0]), (true, []),
        (true, words [1]), (true, words [2]), (true, words [1, 2, 15, 1]),
        (true, words [2]), (true, words [0, 0, 15, 3]), (true, words [0]),
        (true, words [0, 0, 16, 4])] &&
      mainWords final == [16, 4] && transientWords final == [0, 0, 0]

#guard bothModels batchInOneTransaction

-- Separate transactions: the flag and the queue of an unfinished batch are cleared, so the
-- next transaction checks immediately and reads an empty queue.
private def resetBetweenTransactions (model : CompilationModel) : Bool :=
  match runTransaction model Verity.defaultState [("enter", []), ("act", [5])] with
  | none => false
  | some (first, afterFirst) =>
      match runTransaction model afterFirst [("state", []), ("act", [2]), ("state", [])] with
      | none => false
      | some (second, final) =>
          first == [(true, []), (true, words [1])] &&
          transientWords afterFirst == [1, 1, 0] &&
          second == [(true, words [0, 0, 5, 0]), (true, words [0]), (true, words [0, 0, 7, 1])] &&
          mainWords final == [7, 1] && transientWords final == [0, 0, 0]

#guard bothModels resetBetweenTransactions

-- A flag set in its own transaction is gone in the next one: `act` checks immediately.
private def flagInOwnTransaction (model : CompilationModel) : Bool :=
  match runTransaction model Verity.defaultState [("enter", [])] with
  | none => false
  | some (_, afterEnter) =>
      match runTransaction model afterEnter [("act", [5]), ("state", [])] with
      | none => false
      | some (results, final) =>
          results == [(true, words [0]), (true, words [0, 0, 5, 1])] && mainWords final == [5, 1]

#guard bothModels flagInOwnTransaction

-- Full-word Yul locals feed transient writes: a wrapping `add`, a narrowing conversion
-- in Solidity, signed negation and bitwise `not`.
private def fullWords (model : CompilationModel) : Bool :=
  match runTransaction model Verity.defaultState
      [("fullWordLocal", [41]), ("fullWordLocal", [2 ^ 256 - 1]), ("fullWordLocal", [255]),
       ("state", []), ("signedAndBytes", [2 ^ 256 - 5, 0x1234]),
       ("signedAndBytes", [7, 2 ^ 256 - 1])] with
  | none => false
  | some (results, final) =>
      results == [(true, words [84]), (true, words [0]), (true, words [256]),
        (true, words [0, 256, 0, 0]), (true, words [5 ^^^ (2 ^ 256 - 1 - 0x1234)]),
        (true, words [2 ^ 256 - 7])] &&
      transientWords final == [0, 2 ^ 256 - 7, 0]

#guard bothModels fullWords

-- A full-word Yul local in a modifier, and a Yul `sload` of the namespaced slot.
private def modifierAndSlotRead (model : CompilationModel) : Bool :=
  match runTransaction model Verity.defaultState
      [("inModifier", []), ("enter", []), ("inModifier", []), ("namespacedSlotRead", []),
       ("act", [9]), ("namespacedSlotRead", [])] with
  | none => false
  | some (results, _) =>
      results == [(true, words [0]), (true, []), (true, words [1]), (true, words [0, 1]),
        (true, words [1]), (true, words [9, 1])]

#guard bothModels modifierAndSlotRead

-- `Main` stays in persistent storage at the namespaced slot; the flag and queue are
-- transient fields.
#guard bothModels fun m =>
  ["deferred", "queued", "small"].all fun name => m.fields.any fun f => f.name == name && f.isTransient

-- The ordinary Verity compiler accepts the imported model on Cancun.
#guard (Compiler.CompilationModel.compile ir.model [1, 2, 3, 4, 5, 6, 7, 8] .cancun).isOk
#guard (Compiler.CompilationModel.compile legacy.model [1, 2, 3, 4, 5, 6, 7, 8] .cancun).isOk

-- Assembly that exchanges narrow words with Solidity, names a transient variable, touches
-- transient storage or calls out still fails closed at the block.
/--
error: TransientNeutralAssemblySequence.sol:99:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable deferred is unsupported
closure: TransientNeutralAssemblySequence.narrowLocal
assembly { b := x }
-/
#guard_msgs in
solidity_import narrowLocal from "Contracts/SolidityImportSmoke" entry "TransientNeutralAssemblySequence.sol"
  using irProfile
  contract TransientNeutralAssemblySequence
  function narrowLocal(uint256)

/--
error: TransientNeutralAssemblySequence.sol:105:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable small is unsupported
closure: TransientNeutralAssemblySequence.narrowParameter
assembly { word := v }
-/
#guard_msgs in
solidity_import narrowParameter from "Contracts/SolidityImportSmoke" entry "TransientNeutralAssemblySequence.sol"
  using legacyProfile
  contract TransientNeutralAssemblySequence
  function narrowParameter(uint8)

/--
error: TransientNeutralAssemblySequence.sol:30:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable deferred is unsupported
closure: TransientNeutralAssemblySequence.narrowInModifier
assembly { word := 1 }
-/
#guard_msgs in
solidity_import narrowInModifier from "Contracts/SolidityImportSmoke" entry "TransientNeutralAssemblySequence.sol"
  using irProfile
  contract TransientNeutralAssemblySequence
  function narrowInModifier()

/--
error: TransientNeutralAssemblySequence.sol:113:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable queued is unsupported
closure: TransientNeutralAssemblySequence.transientSlot
assembly { s := queued.slot }
-/
#guard_msgs in
solidity_import transientSlot from "Contracts/SolidityImportSmoke" entry "TransientNeutralAssemblySequence.sol"
  using irProfile
  contract TransientNeutralAssemblySequence
  function transientSlot()

/--
error: TransientNeutralAssemblySequence.sol:119:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable queued is unsupported
closure: TransientNeutralAssemblySequence.computedTransientSlot
assembly { tstore(add(base, n), key) }
-/
#guard_msgs in
solidity_import computedTransientSlot from "Contracts/SolidityImportSmoke" entry "TransientNeutralAssemblySequence.sol"
  using irProfile
  contract TransientNeutralAssemblySequence
  function computedTransientSlot(uint256)

/--
error: TransientNeutralAssemblySequence.sol:125:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable deferred is unsupported
closure: TransientNeutralAssemblySequence.callInAssembly
assembly { ok := call(gas(), target, 0, 0, 0, 0, 0) }
-/
#guard_msgs in
solidity_import callInAssembly from "Contracts/SolidityImportSmoke" entry "TransientNeutralAssemblySequence.sol"
  using irProfile
  contract TransientNeutralAssemblySequence
  function callInAssembly(address)

end SolidityImportSmoke.TransientNeutralAssemblyChecks
