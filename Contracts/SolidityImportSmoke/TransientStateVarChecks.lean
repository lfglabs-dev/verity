import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.Transactions

namespace SolidityImportSmoke.TransientStateVarChecks
open Compiler.CompilationModel Denote
open Compiler.CompilationModel.SolidityImport.Transactions

/-! Transient value-type state variables read and written through solc's
`transientStorageLayout`. Every expected value below was observed on solc 0.8.34
(optimizer runs 10, Cancun, Anvil) with the legacy and via-IR pipelines, which agree:
a probe seeds transient slots 0 and 1, calls the function in the same transaction
and reads transient slots 0 to 3 back. -/

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

solidity_import ir from "Contracts/SolidityImportSmoke" entry "TransientStateVarSequence.sol"
  using irProfile
  contract TransientStateVarSequence
  function count()
  function sender()
  function bump()
  function earlyReturnBump(bool)
  function failInsideGuard()
  function packed()
  function assignForms(uint16,uint8)
  function readWords()
  function lockedEquals(bool)
  function persistentWithAssembly(uint256)

solidity_import legacy from "Contracts/SolidityImportSmoke" entry "TransientStateVarSequence.sol"
  using legacyProfile
  contract TransientStateVarSequence
  function count()
  function sender()
  function bump()
  function earlyReturnBump(bool)
  function failInsideGuard()
  function packed()
  function assignForms(uint16,uint8)
  function readWords()
  function lockedEquals(bool)
  function persistentWithAssembly(uint256)

private def oracle := SolidityImport.Differential.oracle

/-- Success, return words or revert bytes, persistent slot 0 and transient slots 0 to 3
after one call from a world with `count` and transient slots 0 and 1 seeded. -/
private def observe (model : CompilationModel) (name : String) (args : List Nat)
    (count t0 t1 : Nat) :
    Option (Bool × List Nat × Option (List UInt8) × Nat × List Nat) := do
  let fn ← model.functions.find? (·.name == name)
  let world := ((Verity.defaultState.writePhysicalSlot 0 (.ofNat count)).writeTransient 0
    (.ofNat t0)).writeTransient 1 (.ofNat t1)
  let r := denoteFunction oracle model fn { sender := 0, functionSelector := 0, args } world
  let final := match bindExternalParams 0 fn.bindingParams args with
    | none => world
    | some bindings =>
        match execStmtList oracle (effectiveFields model)
            { world, bindings, errors := model.errors } fn.body with
        | .stop st | .continue st | .return _ st => st.world
        | .revert | .revertWithData _ => world
  return (r.success, r.returnWords, r.revertData, r.finalStorage 0,
    [0, 1, 2, 3].map fun slot => (final.readTransient slot).val)

private def dirty0 := 0xdeadbeefcafe0102030405060708090a0b0c0d0e0f1011ff12345601
private def dirty1 := 0xabcdef0123456789 * 2 ^ 160 + 77
private def errorGuardRollback : List UInt8 :=
  [0x08, 0xc3, 0x79, 0xa0] ++ (List.replicate 31 0 ++ [0x20]) ++ (List.replicate 31 0 ++ [14]) ++
    "guard rollback".toUTF8.toList ++ List.replicate 18 0
private def packedWord0 := 4294970368
private def packedWord1 := 13153514735978126263833163494446547176903392886786

private def bothModels (check : CompilationModel → Bool) : Bool :=
  check ir.model && check legacy.model

-- nonReentrant: an unlocked call clears the lock; a locked call reverts with empty data;
-- an early return still runs the cleanup; a revert inside the guard rolls back.
#guard bothModels fun m => observe m "bump" [] 7 0 0 == some (true, [8], none, 8, [0, 0, 0, 0])
#guard bothModels fun m => observe m "bump" [] 7 1 0 == some (false, [], some [], 7, [1, 0, 0, 0])
#guard bothModels fun m =>
  observe m "earlyReturnBump" [1] 7 0 0 == some (true, [17], none, 7, [0, 0, 0, 0])
#guard bothModels fun m =>
  observe m "earlyReturnBump" [0] 7 0 0 == some (true, [8], none, 8, [0, 0, 0, 0])
#guard bothModels fun m =>
  observe m "failInsideGuard" [] 7 0 0 == some (false, [], some errorGuardRollback, 7, [0, 0, 0, 0])

-- Packed slot 0 (bool, uint16, uint8, address), slot 1 (contract, uint64) and full-word
-- slots: compound updates, increments, `delete` and neighbor bytes from a dirty slot.
#guard bothModels fun m => observe m "packed" [] 7 0 0 ==
  some (true, [12, 0, 1, 2, 9, 0x1234, 2 ^ 256 - 5], none, 7,
    [packedWord0, packedWord1, 0x1234, 2 ^ 256 - 5])
#guard bothModels fun m => observe m "packed" [] 7 dirty0 dirty1 ==
  some (true, [13410, 0, 1, 2, 9, 0x1234, 2 ^ 256 - 5], none, 7,
    [23450803640979561573830060092471658351661967172142324985094118597121, packedWord1, 0x1234,
      2 ^ 256 - 5])

-- Assignment expression, tuple assignment from a helper, narrow compound update, `delete`;
-- checked `assigned + 1` overflows at 65535 and leaves the dirty slots untouched.
#guard bothModels fun m => observe m "assignForms" [10, 3] 7 0 0 ==
  some (true, [10, 17], none, 7,
    [50334464, 4384504911992708754611054498148849058967797628928, 0, 0])
#guard bothModels fun m => observe m "assignForms" [65535, 255] 7 dirty0 dirty1 ==
  some (false, [], some (panicBytes 0x11), 7, [dirty0, dirty1, 0, 0])

-- Reads extract each packed field from dirty words; a dirty bool byte reads as `true`.
#guard bothModels fun m => observe m "readWords" [] 7 0x12aa 0 ==
  some (true, [1, 18, 0, 0, 0], none, 7, [0x12aa, 0, 0, 0])
#guard bothModels fun m => observe m "readWords" [] 7 dirty0 dirty1 ==
  some (true, [1, 13398, 18, 1158880612783701582839550698742125304546199605759,
    12379813738877118345], none, 7, [dirty0, dirty1, 0, 0])
#guard bothModels fun m => observe m "lockedEquals" [1] 7 0x12aa 0 ==
  some (true, [1], none, 7, [0x12aa, 0, 0, 0])
#guard bothModels fun m => observe m "lockedEquals" [0] 7 0x1200 0 ==
  some (true, [1], none, 7, [0x1200, 0, 0, 0])
#guard bothModels fun m => observe m "sender" [] 7 dirty0 0 ==
  some (true, [1158880612783701582839550698742125304546199605759], none, 7, [dirty0, 0, 0, 0])
#guard bothModels fun m =>
  observe m "count" [] 7 dirty0 0 == some (true, [7], none, 7, [dirty0, 0, 0, 0])

-- A persistent-only closure with assembly keeps main's backend-specific word: legacy keeps
-- the uncleaned narrow stack word, via-IR cleans it (solc agrees on both).
#guard observe legacy.model "persistentWithAssembly" [2 ^ 200 + 65537] 7 0 0 ==
  some (true, [2 ^ 200 + 65537], none, 2 ^ 200 + 65537, [0, 0, 0, 0])
#guard observe ir.model "persistentWithAssembly" [2 ^ 200 + 65537] 7 0 0 ==
  some (true, [1], none, 2 ^ 200 + 65537, [0, 0, 0, 0])

-- Persistent storage at the same slot number is a separate channel.
private def slotZero (m : CompilationModel) (name : String) (isTransient : Bool) : Bool :=
  m.fields.any fun f => f.name == name && f.slot == some 0 && f.isTransient == isTransient
#guard bothModels fun m => slotZero m "count" false &&
  ["locked", "number", "small", "sender"].all (slotZero m · true)

-- A fresh transaction clears transient storage; a callback in the same transaction
-- sees the values and the lock the outer frame left there.
private def transactionBoundary (model : CompilationModel) : Bool := Id.run do
  let some packedFn := model.functions.find? (·.name == "packed") | return false
  let some bumpFn := model.functions.find? (·.name == "bump") | return false
  let some senderFn := model.functions.find? (·.name == "sender") | return false
  let fields := effectiveFields model
  let .ok outer := executeBody oracle fields (Verity.defaultState.writePhysicalSlot 0 (.ofNat 5))
    [] packedFn.body model.errors | return false
  let senderInCallback := match execStmtList oracle fields
      { world := outer.world, bindings := [], errors := model.errors } senderFn.body with
    | .stop st => st.observedReturnWords
    | _ => none
  let locked := outer.world.writeTransient 0 (.ofNat ((outer.world.readTransient 0).val ||| 1))
  let blocked := match execStmtList oracle fields
      { world := locked, bindings := [], errors := model.errors } bumpFn.body with
    | .revertWithData [] => true
    | _ => false
  let .ok nextTx := executeBody oracle fields outer.world [] senderFn.body model.errors
    | return false
  return outer.success && senderInCallback == some [1] &&
    blocked &&
    nextTx.success && nextTx.data == wordBytes 0 && (nextTx.world.readSlot 0).val == 5

#guard bothModels transactionBoundary

-- The ordinary Verity compiler accepts the imported transient fields on Cancun and Osaka.
private def selectors : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
#guard (Compiler.CompilationModel.compile ir.model selectors .cancun).isOk
#guard (Compiler.CompilationModel.compile legacy.model selectors .osaka).isOk

-- Narrow signed, fixed-bytes, enum and function-pointer transient types fail closed.
/--
error: TransientStateVarSequence.sol:88:67: Identifier: [solidity-import:unsupported] unsupported transient scalar storage type t_int16
closure: TransientStateVarSequence.readSigned
delta
-/
#guard_msgs in
solidity_import unsupportedSigned from "Contracts/SolidityImportSmoke" entry "TransientStateVarSequence.sol"
  using irProfile
  contract TransientStateVarSequence
  function readSigned()

/--
error: TransientStateVarSequence.sol:90:64: Identifier: [solidity-import:unsupported] unsupported transient scalar storage type t_bytes4
closure: TransientStateVarSequence.readTag
tag
-/
#guard_msgs in
solidity_import unsupportedFixedBytes from "Contracts/SolidityImportSmoke" entry "TransientStateVarSequence.sol"
  using irProfile
  contract TransientStateVarSequence
  function readTag()

/--
error: TransientStateVarSequence.sol:92:63: Identifier: [solidity-import:unsupported] unsupported transient scalar storage type t_enum(Mode)15
closure: TransientStateVarSequence.readMode
mode
-/
#guard_msgs in
solidity_import unsupportedEnum from "Contracts/SolidityImportSmoke" entry "TransientStateVarSequence.sol"
  using irProfile
  contract TransientStateVarSequence
  function readMode()

/--
error: TransientStateVarSequence.sol:94:47: Identifier: [solidity-import:unsupported] unsupported transient scalar storage type t_function_internal_nonpayable()returns()
closure: TransientStateVarSequence.clearPointer
pointer
-/
#guard_msgs in
solidity_import unsupportedPointer from "Contracts/SolidityImportSmoke" entry "TransientStateVarSequence.sol"
  using irProfile
  contract TransientStateVarSequence
  function clearPointer()

-- Inline assembly that is not transient-neutral fails closed in a closure that touches a
-- transient variable: in the root, through `x.slot`, or in a helper reached under a
-- transient modifier.
/--
error: TransientStateVarSequence.sol:98:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable number is unsupported
closure: TransientStateVarSequence.rawInRoot
assembly { word := tload(0) }
-/
#guard_msgs in
solidity_import rawAssemblyInRoot from "Contracts/SolidityImportSmoke" entry "TransientStateVarSequence.sol"
  using irProfile
  contract TransientStateVarSequence
  function rawInRoot()

/--
error: TransientStateVarSequence.sol:102:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable sender is unsupported
closure: TransientStateVarSequence.slotInRoot
assembly { slotWord := sender.slot }
-/
#guard_msgs in
solidity_import slotAssemblyInRoot from "Contracts/SolidityImportSmoke" entry "TransientStateVarSequence.sol"
  using irProfile
  contract TransientStateVarSequence
  function slotInRoot()

/--
error: TransientStateVarSequence.sol:106:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable locked is unsupported
closure: TransientStateVarSequence.rawInHelper
assembly { word := v }
-/
#guard_msgs in
solidity_import rawAssemblyInHelper from "Contracts/SolidityImportSmoke" entry "TransientStateVarSequence.sol"
  using irProfile
  contract TransientStateVarSequence
  function rawInHelper()

-- A transient variable shadowing a persistent one keeps the shadowing rejection where it is
-- used, while a root reaching only the persistent base variable imports as before.
solidity_import baseOnly from "Contracts/SolidityImportSmoke" entry "TransientStateVarSequence.sol"
  using irProfile
  contract ShadowedTransientChild
  function touchBaseOnly()

#guard observe baseOnly.model "touchBaseOnly" [] 0 0 0 == some (true, [], none, 1, [0, 0, 0, 0])
#guard baseOnly.model.fields.all (!·.isTransient)

-- A full-word Yul local in a modifier is transient-neutral (#2915): the root imports and
-- writes `number` into a clean or dirty packed slot as solc does (both pipelines).
solidity_import fullWordModifierIr from "Contracts/SolidityImportSmoke"
  entry "TransientStateVarSequence.sol"
  using irProfile
  contract TransientStateVarSequence
  function rawInModifier()

solidity_import fullWordModifierLegacy from "Contracts/SolidityImportSmoke"
  entry "TransientStateVarSequence.sol"
  using legacyProfile
  contract TransientStateVarSequence
  function rawInModifier()

#guard [fullWordModifierIr.model, fullWordModifierLegacy.model].all fun m =>
  observe m "rawInModifier" [] 7 0 0 == some (true, [], none, 7, [256, 0, 0, 0]) &&
  observe m "rawInModifier" [] 7 dirty0 dirty1 == some (true, [], none, 7,
    [23450803645956915905704497912590963418093343692702292412913120444673, dirty1, 0, 0])

/--
error: TransientStateVarSequence.sol:141:9: Identifier: [solidity-import:unsupported] shadowed storage declaration shadowed is outside this slice
closure: ShadowedTransientChild.touchChild
shadowed
-/
#guard_msgs in
solidity_import unsupportedShadowed from "Contracts/SolidityImportSmoke" entry "TransientStateVarSequence.sol"
  using irProfile
  contract ShadowedTransientChild
  function touchChild()

end SolidityImportSmoke.TransientStateVarChecks
