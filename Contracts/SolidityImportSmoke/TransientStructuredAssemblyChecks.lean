import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.Transactions

namespace SolidityImportSmoke.TransientStructuredAssemblyChecks
open Compiler.CompilationModel Denote
open Compiler.CompilationModel.SolidityImport.Transactions

/-! Transient state variables in closures whose inline assembly is a structured low-level
call helper (a `staticcall` or value-free `call` over a `bytes memory` local, `returndatasize`,
the free-pointer revert bubble) or a single transient word access at a hashed base of at
least `2^128`: direct, plus a literal, or plus a masked full-word index. The calls run on
Anvil (`check_transient_structured_assembly`); the transient queue runs here. Every expected
value was observed on solc 0.8.34 (optimizer runs 10, Cancun) with both pipelines. -/

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

solidity_import ir from "Contracts/SolidityImportSmoke"
  entry "TransientStructuredAssemblySequence.sol"
  using irProfile
  contract TransientStructuredAssemblySequence
  function lockedProbe(address,bytes)
  function renamedProbe(address,bytes)
  function guardedCall(address,bytes)
  function guardedCallReturn(address,uint256,bytes)
  function queueSum(uint256,uint256)
  function queueAt(uint256)
  function queueRevert(uint256)
  function state()
  function unmaskedWriteAndRead(uint256,uint256)

solidity_import legacy from "Contracts/SolidityImportSmoke"
  entry "TransientStructuredAssemblySequence.sol"
  using legacyProfile
  contract TransientStructuredAssemblySequence
  function lockedProbe(address,bytes)
  function renamedProbe(address,bytes)
  function guardedCall(address,bytes)
  function guardedCallReturn(address,uint256,bytes)
  function queueSum(uint256,uint256)
  function queueAt(uint256)
  function queueRevert(uint256)
  function state()
  function unmaskedWriteAndRead(uint256,uint256)

private def oracle := SolidityImport.Differential.oracle

private def bothModels (check : CompilationModel → Bool) : Bool :=
  check ir.model && check legacy.model

/-- `keccak256("verity.fixture.transient.queue")`, the queue base. -/
private def queueBase := 0x623af9e7429a7097623a7681603826490ad0604b89d21c725179345180e1a2fc

private def tagSlot := 0x2222222222222222222222222222222222222222222222222222222222222200

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

/-- Calls of one transaction, which starts with `beginTransaction`. -/
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

/-- Persistent `total` and `probes`. -/
private def storedWords (world : Verity.ContractState) : List Nat :=
  [(world.readSlot 0).val, (world.readSlot 1).val]

/-- Transient `_locked`, `_count`, queue entries 0 to 3, the tag and the word after it. -/
private def transientWords (world : Verity.ContractState) : List Nat :=
  ([0, 1, queueBase, queueBase + 1, queueBase + 2, queueBase + 3, tagSlot, tagSlot + 1]).map
    fun slot => (world.readTransient slot).val

-- One transaction: two pushes per call into the hashed queue, the masked index (256 + i
-- reads entry i), a tag at a hashed literal slot and the untouched slot after it.
private def queueInOneTransaction (model : CompilationModel) : Bool :=
  match runTransaction model Verity.defaultState
      [("queueSum", [3, 4]), ("queueSum", [5, 6]), ("queueAt", [257]), ("queueAt", [2]),
       ("state", [])] with
  | none => false
  | some (results, final) =>
      results == [(true, words [10]), (true, words [14]), (true, words [4, 4, 14, 0]),
        (true, words [4, 5, 14, 0]), (true, words [24, 0, 0, 4])] &&
      storedWords final == [24, 0] && transientWords final == [0, 4, 3, 4, 5, 6, 14, 0]

#guard bothModels queueInOneTransaction

-- Separate transactions: the queue, counter and tag are cleared; the total persists.
private def queueResetBetweenTransactions (model : CompilationModel) : Bool :=
  match runTransaction model Verity.defaultState [("queueSum", [3, 4])] with
  | none => false
  | some (_, afterFirst) =>
      match runTransaction model afterFirst [("queueAt", [0]), ("queueSum", [1, 2])] with
      | none => false
      | some (second, final) =>
          second == [(true, words [0, 0, 0, 0]), (true, words [4])] &&
          storedWords final == [14, 0] && transientWords final == [0, 2, 1, 2, 0, 0, 4, 0]

#guard bothModels queueResetBetweenTransactions

-- A reverted call rolls back its hashed transient writes, its flag and its storage write.
private def revertRollsBack (model : CompilationModel) : Bool :=
  match runTransaction model Verity.defaultState
      [("queueSum", [3, 4]), ("queueRevert", [9]), ("queueAt", [2]), ("state", [])] with
  | none => false
  | some (results, final) =>
      results.map (·.1) == [true, false, true, true] &&
      results[2]? == some (true, words [2, 0, 10, 0]) &&
      results[3]? == some (true, words [10, 0, 0, 2]) &&
      transientWords final == [0, 2, 3, 4, 0, 0, 10, 0]

#guard bothModels revertRollsBack

#guard bothModels fun m =>
  ["_locked", "_count"].all fun name => m.fields.any fun f => f.name == name && f.isTransient

-- The ordinary Verity compiler accepts the imported model on Cancun.
#guard (Compiler.CompilationModel.compile ir.model [1, 2, 3, 4, 5, 6, 7, 8, 9] .cancun).isOk
#guard (Compiler.CompilationModel.compile legacy.model [1, 2, 3, 4, 5, 6, 7, 8, 9] .cancun).isOk

-- Unmasked full-word index `add(B, index)`: both normal slots and exact wrap-around to slot 0
-- (`index = 2^256 - queueBase`, writing non-0/1 word `2` into `_locked`'s slot) agree in both pipelines.
private def unmaskedWrapIndex : Nat := 2 ^ 256 - queueBase

private def unmaskedIndexChecks (model : CompilationModel) : Bool :=
  match runTransaction model Verity.defaultState
      [("unmaskedWriteAndRead", [5, 77]), ("unmaskedWriteAndRead", [unmaskedWrapIndex, 2])] with
  | none => false
  | some (results, final) =>
      results == [(true, words [77, 0]), (true, words [2, 1])] &&
      (final.readTransient 0).val == 2

#guard bothModels unmaskedIndexChecks

-- Every block outside the structured shapes fails closed at the block.
-- An unmasked narrow index: the legacy pipeline can leave dirty high bits in a `uint8` local.
/--
error: TransientStructuredAssemblySequence.sol:222:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _locked is unsupported
closure: TransientStructuredAssemblySequence.badNarrowIndex
assembly ("memory-safe") { tstore(add(base, index), key) }
-/
#guard_msgs in
solidity_import badNarrowIndex from "Contracts/SolidityImportSmoke"
  entry "TransientStructuredAssemblySequence.sol"
  using legacyProfile
  contract TransientStructuredAssemblySequence
  function badNarrowIndex(uint8,uint256)

-- A mask of 2^128 or more: `B + M` can exceed 2^256.
/--
error: TransientStructuredAssemblySequence.sol:229:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _locked is unsupported
closure: TransientStructuredAssemblySequence.badWideMask
assembly ("memory-safe") { tstore(add(base, and(index, 0xffffffffffffffffffffffffffffffffff)), key) }
-/
#guard_msgs in
solidity_import badWideMask from "Contracts/SolidityImportSmoke"
  entry "TransientStructuredAssemblySequence.sol"
  using irProfile
  contract TransientStructuredAssemblySequence
  function badWideMask(uint256,uint256)

-- A base below 2^128 can alias a linear transient slot.
/--
error: TransientStructuredAssemblySequence.sol:236:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _locked is unsupported
closure: TransientStructuredAssemblySequence.badLowBase
assembly ("memory-safe") { tstore(base, key) }
-/
#guard_msgs in
solidity_import badLowBase from "Contracts/SolidityImportSmoke"
  entry "TransientStructuredAssemblySequence.sol"
  using legacyProfile
  contract TransientStructuredAssemblySequence
  function badLowBase(uint256)

-- A base local assigned after its constant initializer.
/--
error: TransientStructuredAssemblySequence.sol:243:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _locked is unsupported
closure: TransientStructuredAssemblySequence.badReassignedBase
assembly ("memory-safe") { tstore(base, key) }
-/
#guard_msgs in
solidity_import badReassignedBase from "Contracts/SolidityImportSmoke"
  entry "TransientStructuredAssemblySequence.sol"
  using irProfile
  contract TransientStructuredAssemblySequence
  function badReassignedBase(uint256)

-- Arbitrary transient assembly at a linear slot.
/--
error: TransientStructuredAssemblySequence.sol:248:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _locked is unsupported
closure: TransientStructuredAssemblySequence.badArbitraryTload
assembly { word := tload(0) }
-/
#guard_msgs in
solidity_import badArbitraryTload from "Contracts/SolidityImportSmoke"
  entry "TransientStructuredAssemblySequence.sol"
  using legacyProfile
  contract TransientStructuredAssemblySequence
  function badArbitraryTload()

-- Two transient accesses in one block.
/--
error: TransientStructuredAssemblySequence.sol:254:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _locked is unsupported
closure: TransientStructuredAssemblySequence.badTwoStatements
assembly ("memory-safe") { tstore(base, key)  out := tload(base) }
-/
#guard_msgs in
solidity_import badTwoStatements from "Contracts/SolidityImportSmoke"
  entry "TransientStructuredAssemblySequence.sol"
  using irProfile
  contract TransientStructuredAssemblySequence
  function badTwoStatements(uint256)

-- A call over scratch memory rather than a `bytes memory` local.
/--
error: TransientStructuredAssemblySequence.sol:259:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _locked is unsupported
closure: TransientStructuredAssemblySequence.badScratchCall
assembly { ok := call(gas(), target, 0, 0, 0, 0, 0) }
-/
#guard_msgs in
solidity_import badScratchCall from "Contracts/SolidityImportSmoke"
  entry "TransientStructuredAssemblySequence.sol"
  using legacyProfile
  contract TransientStructuredAssemblySequence
  function badScratchCall(address)

-- `delegatecall` runs foreign code on this account's storage; it fails closed in the Yul lowering.
/--
error: TransientStructuredAssemblySequence.sol:264:42: YulFunctionCall: [solidity-import:unsupported] unsupported Yul builtin delegatecall
closure: TransientStructuredAssemblySequence.badDelegatecall
delegatecall(gas(), target, add(payload, 0x20), mload(payload), 0x00, 0x00)
-/
#guard_msgs in
solidity_import badDelegatecall from "Contracts/SolidityImportSmoke"
  entry "TransientStructuredAssemblySequence.sol"
  using irProfile
  contract TransientStructuredAssemblySequence
  function badDelegatecall(address,bytes)

-- A narrow `value` operand may carry dirty high bits on the legacy pipeline.
/--
error: TransientStructuredAssemblySequence.sol:273:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _locked is unsupported
closure: TransientStructuredAssemblySequence.badNarrowValueCall
assembly ("memory-safe") { ok := call(gas(), target, value, add(payload, 0x20), mload(payload), 0x00, 0x00) }
-/
#guard_msgs in
solidity_import badNarrowValueCall from "Contracts/SolidityImportSmoke"
  entry "TransientStructuredAssemblySequence.sol"
  using legacyProfile
  contract TransientStructuredAssemblySequence
  function badNarrowValueCall(address,uint128,bytes)

end SolidityImportSmoke.TransientStructuredAssemblyChecks
