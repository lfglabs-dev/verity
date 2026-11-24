import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.Transactions

/-!
Synthetic clean-room smoke checks for R9 + R9b:
- R9: Pure constant-slot storage-pointer getters (`assembly { $.slot := STORE_SLOT }` and
  `assembly ("memory-safe") { $.slot := 0x1111...1100 }`) allowed inside call closures
  that read/write a `transient bool` state variable (under both via-IR and legacy pipelines).
- R9b: Recognized structured OpenZeppelin v5 `LowLevelCall` helpers (`staticcallNoReturn`,
  `callNoReturn`, `returnDataSize`, `returnData`, `bubbleRevert`) allowed inside closures
  that also access a `transient bool` state variable and use `$.slot := CONST` — matched
  strictly by Yul AST structure (100% library-name independent, verified with `CustomBridge`).
- Negative controls: arbitrary assembly (`tload`), dynamic parameter slot assembly
  (`$.slot := slot`), multi-statement getter assembly, non-structured scratch-space Yul `call`,
  and both Solidity-level and Yul-level `delegatecall` remain REJECTED in transient closures.
-/
namespace SolidityImportSmoke.TransientWithSlotGetterChecks
open Compiler.CompilationModel Denote ByteExternalCall
open Compiler.CompilationModel.SolidityImport.Transactions

solidity_profile irProfile where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_profile legacyProfile where
  evmVersion := "osaka"
  viaIR := false
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import ir from "Contracts/SolidityImportSmoke" entry "TransientWithSlotGetterFixture.sol"
  using irProfile
  contract TransientWithSlotGetterFixture
  function addDirect(uint256,address)
  function addInBatch(uint256,uint256,address)
  function addInBatchRevert(uint256,address)
  function staticCallInBatch(address,bytes,address)
  function callInBatch(address,bytes,address)
  function renamedStaticCallInBatch(address,bytes,address)
  function readState(address)

solidity_import legacy from "Contracts/SolidityImportSmoke" entry "TransientWithSlotGetterFixture.sol"
  using legacyProfile
  contract TransientWithSlotGetterFixture
  function addDirect(uint256,address)
  function addInBatch(uint256,uint256,address)
  function addInBatchRevert(uint256,address)
  function staticCallInBatch(address,bytes,address)
  function callInBatch(address,bytes,address)
  function renamedStaticCallInBatch(address,bytes,address)
  function readState(address)

#guard ir.report.functions.length == 7
#guard ir.report.functions.all (·.denoteCovered)
#guard legacy.report.functions.length == 7
#guard legacy.report.functions.all (·.denoteCovered)

private def oracle := SolidityImport.Differential.oracle
private def selfAddr : Nat := 0xc0de
private def userA : Nat := 0xa11ce
private def wordTarget : Nat := 0xa1
private def revertPayloadTarget : Nat := 0xb1
private def revertEmptyTarget : Nat := 0xb2
private def eoaTarget : Nat := 0xe0

private def respond (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if request.target == wordTarget then
    let val := 40 + request.calldata.length
    .success world (wordBytes val) []
  else if request.target == revertPayloadTarget then
    .revert [0xde, 0xad, 0xbe, 0xef, 0x01, 0x02] []
  else if request.target == revertEmptyTarget then
    .revert [] []
  else
    .success world [] []

private def callEnv : ByteCallEnvironment :=
  { gas := some 1000000
    adversary := some
      { respond
        valid := by
          intro request world
          unfold respond
          by_cases h1 : (request.target == wordTarget) = true
          · simp [h1, Response.valid]
          · simp only [h1, Bool.false_eq_true, ↓reduceIte]
            by_cases h2 : (request.target == revertPayloadTarget) = true
            · simp [h2, Response.valid]
            · simp only [h2, Bool.false_eq_true, ↓reduceIte]
              by_cases h3 : (request.target == revertEmptyTarget) = true <;>
                simp [h3, Response.valid] } }

private def bytesTail (data : List UInt8) : List Nat :=
  data.length :: (List.range ((data.length + 31) / 32)).map fun word =>
    (List.range 32).foldl (fun acc lane => acc * 256 + (data.getD (32 * word + lane) 0).toNat) 0

private def withMockCode (world : Verity.ContractState) : Verity.ContractState :=
  { world with
    thisAddress := Verity.Core.Address.ofNat selfAddr
    accountWorld := fun a =>
      let prev := world.accountWorld a
      if a.val == selfAddr || a.val == wordTarget ||
         a.val == revertPayloadTarget || a.val == revertEmptyTarget then
        { prev with code := [⟨0x60, by decide⟩, ⟨0x00, by decide⟩] }
      else prev }

private def runTx (model : CompilationModel) (world : Verity.ContractState)
    (name : String) (args : List Nat) (resetTransient : Bool := true) :
    Option (Bool × List UInt8 × Verity.ContractState) := do
  let fn ← model.functions.find? (·.name == name)
  let tx : DenoteTransaction := { sender := 0x5e, thisAddress := selfAddr, functionSelector := 0, args }
  let seeded := if resetTransient then beginTransaction world else world
  let base := withMockCode (withTransactionContext seeded tx)
  let bindings ← bindExternalParams 0 fn.bindingParams args
  match finishFrame base (execStmtList oracle (effectiveFields model)
      { world := base, bindings, errors := model.errors, selector := base.selector,
        byteCallAdversary := callEnv.adversary, byteCallGas := callEnv.gas } fn.body) with
  | .ok r => some (r.success, r.data, r.world)
  | .error _ => none

-- `FailedCall()` selector: 0xd6bda275
private def failedCallBytes : List UInt8 := [0xd6, 0xbd, 0xa2, 0x75]
-- `AddressEmptyCode(address)` selector: 0x9996b315
private def addressEmptyCodeBytes (addr : Nat) : List UInt8 :=
  [0x99, 0x96, 0xb3, 0x15] ++ wordBytes addr

private def checkSequence (model : CompilationModel) : Bool :=
  (do
    let (ok0, d0, st0) ← runTx model Verity.defaultState "readState" [userA]
    let (ok1, d1, st1) ← runTx model st0 "addDirect" [10, userA]
    let (ok2, d2, st2) ← runTx model st1 "addInBatch" [5, 7, userA]
    let (ok3, _, st3) ← runTx model st2 "addInBatchRevert" [99, userA]
    let (ok4, d4, st4) ← runTx model st3 "readState" [userA]
    -- R9b: Address.functionStaticCall inside transient+slot-getter batch
    -- wordTarget returns 40 + 3 = 43 -> _addValue(43, userA) in batch: value = 27 + 86 = 113, runs = 2, credit = 58
    let (okS1, dS1, stS1) ← runTx model st4 "staticCallInBatch"
      ([wordTarget, 96, userA] ++ bytesTail [1, 2, 3])
    let (okS2, dS2, stS2) ← runTx model stS1 "staticCallInBatch"
      ([revertPayloadTarget, 96, userA] ++ bytesTail [1])
    let (okS3, dS3, stS3) ← runTx model stS2 "staticCallInBatch"
      ([revertEmptyTarget, 96, userA] ++ bytesTail [1])
    let (okS4, dS4, stS4) ← runTx model stS3 "staticCallInBatch"
      ([eoaTarget, 96, userA] ++ bytesTail [1])
    -- R9b: Address.functionCall inside transient+slot-getter batch
    -- wordTarget returns 40 + 2 = 42 -> _addValue(42, userA) in batch: value = 113 + 84 = 197, runs = 3, credit = 100
    let (okC1, dC1, stC1) ← runTx model stS4 "callInBatch"
      ([wordTarget, 96, userA] ++ bytesTail [9, 8])
    let (okC2, dC2, stC2) ← runTx model stC1 "callInBatch"
      ([revertPayloadTarget, 96, userA] ++ bytesTail [9])
    let (okC3, dC3, stC3) ← runTx model stC2 "callInBatch"
      ([revertEmptyTarget, 96, userA] ++ bytesTail [9])
    -- R9b library-name independence + 1-arg bubbleRevert(bytes memory):
    -- wordTarget returns 40 + 1 = 41 -> _addValue(41, userA) in batch: value = 197 + 82 = 279, runs = 4, credit = 141
    let (okR1, dR1, stR1) ← runTx model stC3 "renamedStaticCallInBatch"
      ([wordTarget, 96, userA] ++ bytesTail [7])
    let (okR2, dR2, stR2) ← runTx model stR1 "renamedStaticCallInBatch"
      ([revertPayloadTarget, 96, userA] ++ bytesTail [7])
    let (okState, dState, stState) ← runTx model stR2 "readState" [userA]
    -- Reentrant frame with transient slot 0 (_inBatch) already set to 1:
    let reentrantWorld := stState.writeTransient 0 (.ofNat 1)
    let (ok5, _, _) ← runTx model reentrantWorld "addInBatch" [1, 1, userA] (resetTransient := false)
    let (ok5s, _, _) ← runTx model reentrantWorld "staticCallInBatch"
      ([wordTarget, 96, userA] ++ bytesTail [1]) (resetTransient := false)
    let (ok5c, _, _) ← runTx model reentrantWorld "callInBatch"
      ([wordTarget, 96, userA] ++ bytesTail [1]) (resetTransient := false)
    let (ok6, d6, st6) ← runTx model reentrantWorld "addDirect" [4, userA] (resetTransient := false)
    let (ok7, d7, _) ← runTx model st6 "readState" [userA] (resetTransient := false)
    return ok0 && d0 == (wordBytes 0 ++ wordBytes 0 ++ wordBytes 0 ++ wordBytes 0) &&
           ok1 && d1 == wordBytes 10 &&
           ok2 && d2 == wordBytes 47 &&
           !ok3 &&
           ok4 && d4 == (wordBytes 27 ++ wordBytes 1 ++ wordBytes 15 ++ wordBytes 0) &&
           okS1 && dS1 == wordBytes 113 &&
           !okS2 && dS2 == [0xde, 0xad, 0xbe, 0xef, 0x01, 0x02] &&
           !okS3 && dS3 == failedCallBytes &&
           !okS4 && dS4 == addressEmptyCodeBytes eoaTarget &&
           okC1 && dC1 == wordBytes 197 &&
           !okC2 && dC2 == [0xde, 0xad, 0xbe, 0xef, 0x01, 0x02] &&
           !okC3 && dC3 == failedCallBytes &&
           okR1 && dR1 == wordBytes 279 &&
           !okR2 && dR2 == [0xde, 0xad, 0xbe, 0xef, 0x01, 0x02] &&
           okState && dState == (wordBytes 279 ++ wordBytes 4 ++ wordBytes 141 ++ wordBytes 0) &&
           !ok5 && !ok5s && !ok5c &&
           ok6 && d6 == wordBytes 287 &&
           ok7 && d7 == (wordBytes 287 ++ wordBytes 5 ++ wordBytes 145 ++ wordBytes 1)) == some true

#guard checkSequence ir.model
#guard checkSequence legacy.model

/--
error: TransientWithSlotGetterFixture.sol:269:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _inBatch is unsupported
closure: TransientWithSlotGetterFixture.badArbitraryAsm
assembly {
            word := tload(0)
        }
-/
#guard_msgs in
solidity_import rejectArbitraryAsm from "Contracts/SolidityImportSmoke" entry "TransientWithSlotGetterFixture.sol"
  using irProfile
  contract TransientWithSlotGetterFixture
  function badArbitraryAsm()

/--
error: TransientWithSlotGetterFixture.sol:165:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _inBatch is unsupported
closure: TransientWithSlotGetterFixture.badDynamicSlotAsm
assembly {
            $.slot := slot
        }
-/
#guard_msgs in
solidity_import rejectDynamicSlotAsm from "Contracts/SolidityImportSmoke" entry "TransientWithSlotGetterFixture.sol"
  using irProfile
  contract TransientWithSlotGetterFixture
  function badDynamicSlotAsm(bytes32)

/--
error: TransientWithSlotGetterFixture.sol:175:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _inBatch is unsupported
closure: TransientWithSlotGetterFixture.badExtraAsmInGetter
assembly {
            junk := tload(0)
        }
-/
#guard_msgs in
solidity_import rejectExtraAsmInGetter from "Contracts/SolidityImportSmoke" entry "TransientWithSlotGetterFixture.sol"
  using irProfile
  contract TransientWithSlotGetterFixture
  function badExtraAsmInGetter()

/--
error: TransientWithSlotGetterFixture.sol:296:39: MemberAccess: [solidity-import:unsupported] external contract calls are outside this slice
closure: TransientWithSlotGetterFixture.badDelegateCallInTransient
target.delegatecall
-/
#guard_msgs in
solidity_import rejectDelegateCallInTransient from "Contracts/SolidityImportSmoke" entry "TransientWithSlotGetterFixture.sol"
  using irProfile
  contract TransientWithSlotGetterFixture
  function badDelegateCallInTransient(address,bytes)

/--
error: TransientWithSlotGetterFixture.sol:309:19: YulFunctionCall: [solidity-import:unsupported] unsupported Yul builtin delegatecall
closure: TransientWithSlotGetterFixture.badYulDelegateCallInTransient
delegatecall(gas(), target, add(payload, 0x20), mload(payload), 0x00, 0x00)
-/
#guard_msgs in
solidity_import rejectYulDelegateCallInTransient from "Contracts/SolidityImportSmoke" entry "TransientWithSlotGetterFixture.sol"
  using irProfile
  contract TransientWithSlotGetterFixture
  function badYulDelegateCallInTransient(address,bytes)

/--
error: TransientWithSlotGetterFixture.sol:317:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _inBatch is unsupported
closure: TransientWithSlotGetterFixture.badNonStructuredCallAsmInTransient
assembly {
            ok := call(gas(), target, 0, 0, 0, 0, 0)
        }
-/
#guard_msgs in
solidity_import rejectNonStructuredCallAsmInTransient from "Contracts/SolidityImportSmoke" entry "TransientWithSlotGetterFixture.sol"
  using irProfile
  contract TransientWithSlotGetterFixture
  function badNonStructuredCallAsmInTransient(address)

end SolidityImportSmoke.TransientWithSlotGetterChecks
