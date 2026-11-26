import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.Transactions

namespace SolidityImportSmoke.TransientGuardChecks
open Compiler.CompilationModel Denote
open Compiler.CompilationModel.SolidityImport.Transactions

/-! Transient-storage reentrancy guards (EIP-1153): the direct inline-assembly shape
over a namespaced slot constant, the UDVT slot-library guard shape, and the
`transient bool` state-variable shape. Both via-IR and legacy pipelines are checked
under Cancun: a revert rolls back both persistent and transient storage, a nested/reentrant
frame within the same transaction observes the active transient lock and reverts, and a
fresh transaction clears transient storage while preserving persistent `count`. -/

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

solidity_import irAssembly from "Contracts/SolidityImportSmoke" entry "TransientGuardSmoke.sol"
  using irProfile
  contract TransientGuardAssembly
  function bump()
  function bumpEarly(bool)
  function bumpFail()
  function callGuarded(uint256)
  function forwardGuarded(uint256)
  function leaveLocked(uint256)
  function lockWord()

solidity_import legacyAssembly from "Contracts/SolidityImportSmoke" entry "TransientGuardSmoke.sol"
  using legacyProfile
  contract TransientGuardAssembly
  function bump()
  function bumpEarly(bool)
  function bumpFail()
  function callGuarded(uint256)
  function forwardGuarded(uint256)
  function leaveLocked(uint256)
  function lockWord()

solidity_import irSlotLib from "Contracts/SolidityImportSmoke" entry "TransientGuardSmoke.sol"
  using irProfile
  contract TransientGuardSlotLib
  function bump()
  function bumpEarly(bool)
  function bumpFail()
  function forwardGuarded(uint256)
  function markEntered()
  function entered()

solidity_import legacySlotLib from "Contracts/SolidityImportSmoke" entry "TransientGuardSmoke.sol"
  using legacyProfile
  contract TransientGuardSlotLib
  function bump()
  function bumpEarly(bool)
  function bumpFail()
  function forwardGuarded(uint256)
  function markEntered()
  function entered()

solidity_import irStateVar from "Contracts/SolidityImportSmoke" entry "TransientGuardSmoke.sol"
  using irProfile
  contract TransientGuardStateVar
  function bump()
  function bumpFail()
  function forwardGuarded(uint256)
  function markLocked()
  function isLocked()

solidity_import legacyStateVar from "Contracts/SolidityImportSmoke" entry "TransientGuardSmoke.sol"
  using legacyProfile
  contract TransientGuardStateVar
  function bump()
  function bumpFail()
  function forwardGuarded(uint256)
  function markLocked()
  function isLocked()

/-- The namespaced assembly guard's transient slot constant. -/
private def assemblySlot : Nat :=
  0x5f7a1d2e3c4b5a69788796a5b4c3d2e1f00f1e2d3c4b5a69788796a5b4c3d2e1

/-- The UDVT slot-library guard's transient slot constant. -/
private def slotLibSlot : Nat :=
  0x11223344556677889900aabbccddeeff00112233445566778899aabbccddeeff

private def oracle := SolidityImport.Differential.oracle

/-- Success, return words or revert bytes, persistent `count` (slot 0) and the guard's
transient slot after one call from a world with `count` and the lock slot seeded. -/
private def observe (model : CompilationModel) (name : String) (args : List Nat)
    (lockSlot count lock : Nat) :
    Option (Bool × List Nat × Option (List UInt8) × Nat × Nat) := do
  let fn ← model.functions.find? (·.name == name)
  let world := ((Verity.defaultState.writePhysicalSlot 0 (.ofNat count)).writeTransient lockSlot
    (.ofNat lock))
  let r := denoteFunction oracle model fn { sender := 0, functionSelector := 0, args } world
  let final := match bindExternalParams 0 fn.bindingParams args with
    | none => world
    | some bindings =>
        match execStmtList oracle (effectiveFields model)
            { world, bindings, errors := model.errors } fn.body with
        | .stop st | .continue st | .return _ st => st.world
        | .revert | .revertWithData _ => world
  return (r.success, r.returnWords, r.revertData, r.finalStorage 0,
    (final.readTransient lockSlot).val)

private def errorGuardRollback : List UInt8 :=
  [0x08, 0xc3, 0x79, 0xa0] ++ (List.replicate 31 0 ++ [0x20]) ++ (List.replicate 31 0 ++ [14]) ++
    "guard rollback".toUTF8.toList ++ List.replicate 18 0
private def errorSlotLibRollback : List UInt8 :=
  [0x08, 0xc3, 0x79, 0xa0] ++ (List.replicate 31 0 ++ [0x20]) ++ (List.replicate 31 0 ++ [16]) ++
    "slotlib rollback".toUTF8.toList ++ List.replicate 16 0
private def errorStateRollback : List UInt8 :=
  [0x08, 0xc3, 0x79, 0xa0] ++ (List.replicate 31 0 ++ [0x20]) ++ (List.replicate 31 0 ++ [14]) ++
    "state rollback".toUTF8.toList ++ List.replicate 18 0
private def selectorBytes (sig : String) : List UInt8 :=
  let s := (KeccakEngine.keccak256_selector sig).toNat
  (List.range 4).map fun k => UInt8.ofNat ((s / 2 ^ (8 * (3 - k))) % 256)
private def errorReentrantCall : List UInt8 :=
  selectorBytes "ReentrantCall()"

private def bothAssembly (check : CompilationModel → Bool) : Bool :=
  check irAssembly.model && check legacyAssembly.model
private def bothSlotLib (check : CompilationModel → Bool) : Bool :=
  check irSlotLib.model && check legacySlotLib.model
private def bothStateVar (check : CompilationModel → Bool) : Bool :=
  check irStateVar.model && check legacyStateVar.model

-- Assembly guard: an unlocked call clears the lock, a locked call reverts with empty
-- data, an early return still releases, a revert rolls the tstore back, an internal
-- guarded helper is inlined under the same guard, and the lock slot reads back.
#guard bothAssembly fun m =>
  observe m "bump" [] assemblySlot 7 0 == some (true, [8], none, 8, 0)
#guard bothAssembly fun m =>
  observe m "bump" [] assemblySlot 7 1 == some (false, [], some [], 7, 1)
#guard bothAssembly fun m =>
  observe m "bumpEarly" [1] assemblySlot 7 0 == some (true, [17], none, 7, 0)
#guard bothAssembly fun m =>
  observe m "bumpEarly" [0] assemblySlot 7 0 == some (true, [8], none, 8, 0)
#guard bothAssembly fun m =>
  observe m "bumpFail" [] assemblySlot 7 0 == some (false, [], some errorGuardRollback, 7, 0)
#guard bothAssembly fun m =>
  observe m "callGuarded" [21] assemblySlot 7 0 == some (true, [42], none, 7, 0)
#guard bothAssembly fun m =>
  observe m "callGuarded" [21] assemblySlot 7 1 == some (false, [], some [], 7, 1)
#guard bothAssembly fun m =>
  observe m "lockWord" [] assemblySlot 7 5 == some (true, [5], none, 7, 5)

-- UDVT slot-library guard (`ReentrancyGuardTransient` / `TransientSlot` pattern).
#guard bothSlotLib fun m =>
  observe m "bump" [] slotLibSlot 7 0 == some (true, [8], none, 8, 0)
#guard bothSlotLib fun m =>
  observe m "bump" [] slotLibSlot 7 1 == some (false, [], some errorReentrantCall, 7, 1)
#guard bothSlotLib fun m =>
  observe m "bumpEarly" [1] slotLibSlot 7 0 == some (true, [17], none, 7, 0)
#guard bothSlotLib fun m =>
  observe m "bumpEarly" [0] slotLibSlot 7 0 == some (true, [8], none, 8, 0)
#guard bothSlotLib fun m =>
  observe m "bumpFail" [] slotLibSlot 7 0 == some (false, [], some errorSlotLibRollback, 7, 0)
#guard bothSlotLib fun m =>
  observe m "entered" [] slotLibSlot 7 0 == some (true, [0], none, 7, 0)
#guard bothSlotLib fun m =>
  observe m "entered" [] slotLibSlot 7 1 == some (true, [1], none, 7, 1)

-- State-variable guard: the same guard shape over a `transient bool`, with its own
-- revert message and a `require` failure inside the guarded body.
#guard bothStateVar fun m =>
  observe m "bump" [] 0 7 0 == some (true, [8], none, 8, 0)
#guard bothStateVar fun m =>
  observe m "bump" [] 0 7 1 == some (false, [], some [], 7, 1)
#guard bothStateVar fun m =>
  observe m "bumpFail" [] 0 7 0 == some (false, [], some errorStateRollback, 7, 0)
#guard bothStateVar fun m =>
  observe m "isLocked" [] 0 7 0 == some (true, [0], none, 7, 0)
#guard bothStateVar fun m =>
  observe m "isLocked" [] 0 7 1 == some (true, [1], none, 7, 1)

/-- Within one transaction, a transient write persists across nested/reentrant frames
and blocks reentrant entry; across a fresh transaction boundary (`executeBody`),
transient storage resets to zero while persistent storage is preserved. -/
private def transactionBoundary (model : CompilationModel)
    (setLockName : String) (setLockArgs : List Nat) (readLockName : String)
    (expectedReentrantRevert : List UInt8) : Bool := Id.run do
  let some setFn := model.functions.find? (·.name == setLockName) | return false
  let some bumpFn := model.functions.find? (·.name == "bump") | return false
  let some forwardFn := model.functions.find? (·.name == "forwardGuarded") | return false
  let some readFn := model.functions.find? (·.name == readLockName) | return false
  let fields := effectiveFields model
  let seed := Verity.defaultState.writePhysicalSlot 0 (.ofNat 5)
  let some setBindings := bindExternalParams 0 setFn.bindingParams setLockArgs | return false
  let some fwdBindings := bindExternalParams 0 forwardFn.bindingParams [0x1234] | return false
  let .ok outer := executeBody oracle fields seed setBindings setFn.body model.errors
    | return false
  -- Same-transaction frame sees the transient lock set by `outer` and blocks reentrant `bump`
  -- and `forwardGuarded`.
  let seenLocked := match execStmtList oracle fields
      { world := outer.world, bindings := [], errors := model.errors } readFn.body with
    | .stop st => st.observedReturnWords == some [1]
    | .return v _ => v == 1
    | _ => false
  let reentrantBlocked := match execStmtList oracle fields
      { world := outer.world, bindings := [], errors := model.errors } bumpFn.body with
    | .revertWithData bytes => bytes == expectedReentrantRevert
    | _ => false
  let forwardBlocked := match execStmtList oracle fields
      { world := outer.world, bindings := fwdBindings, errors := model.errors } forwardFn.body with
    | .revertWithData bytes => bytes == expectedReentrantRevert
    | _ => false
  -- Fresh transaction clears transient storage and preserves persistent `count == 5`.
  let .ok nextTxRead := executeBody oracle fields outer.world [] readFn.body model.errors
    | return false
  let .ok nextTxBump := executeBody oracle fields outer.world [] bumpFn.body model.errors
    | return false
  let .ok nextTxForward :=
    executeBody oracle fields nextTxBump.world fwdBindings forwardFn.body model.errors
    | return false
  return outer.success && seenLocked && reentrantBlocked && forwardBlocked &&
    nextTxRead.success && nextTxRead.data == wordBytes 0 &&
    nextTxBump.success && nextTxBump.data == wordBytes 6 &&
    nextTxForward.success && nextTxForward.data.length >= 128 &&
    (nextTxForward.world.readSlot 0).val == 7

#guard bothAssembly fun m => transactionBoundary m "leaveLocked" [1] "lockWord" []
#guard bothSlotLib fun m => transactionBoundary m "markEntered" [] "entered" errorReentrantCall
#guard bothStateVar fun m => transactionBoundary m "markLocked" [] "isLocked" []

-- All imported transient guard models compile cleanly for Cancun and Osaka.
#guard (Compiler.CompilationModel.compile irAssembly.model [1, 2, 3, 4, 5, 6, 7] .cancun).isOk
#guard (Compiler.CompilationModel.compile legacyAssembly.model [1, 2, 3, 4, 5, 6, 7] .osaka).isOk
#guard (Compiler.CompilationModel.compile irSlotLib.model [1, 2, 3, 4, 5, 6] .cancun).isOk
#guard (Compiler.CompilationModel.compile legacySlotLib.model [1, 2, 3, 4, 5, 6] .osaka).isOk
#guard (Compiler.CompilationModel.compile irStateVar.model [1, 2, 3, 4, 5] .cancun).isOk
#guard (Compiler.CompilationModel.compile legacyStateVar.model [1, 2, 3, 4, 5] .osaka).isOk

end SolidityImportSmoke.TransientGuardChecks
