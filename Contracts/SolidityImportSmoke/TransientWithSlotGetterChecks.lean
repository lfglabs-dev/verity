import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.Transactions

/-!
Synthetic clean-room smoke checks for R9:
- Pure constant-slot storage-pointer getters (`assembly { $.slot := STORE_SLOT }` and
  `assembly ("memory-safe") { $.slot := 0x1111...1100 }`) allowed inside call closures
  that read/write a `transient bool` state variable (under both via-IR and legacy pipelines).
- Arbitrary assembly (`tload`), dynamic parameter slot assembly (`$.slot := slot`), and
  multi-statement getter assembly remain REJECTED in transient closures.
-/
namespace SolidityImportSmoke.TransientWithSlotGetterChecks
open Compiler.CompilationModel Denote
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
  function readState(address)

solidity_import legacy from "Contracts/SolidityImportSmoke" entry "TransientWithSlotGetterFixture.sol"
  using legacyProfile
  contract TransientWithSlotGetterFixture
  function addDirect(uint256,address)
  function addInBatch(uint256,uint256,address)
  function addInBatchRevert(uint256,address)
  function readState(address)

#guard ir.report.functions.length == 4
#guard ir.report.functions.all (·.denoteCovered)
#guard legacy.report.functions.length == 4
#guard legacy.report.functions.all (·.denoteCovered)

private def oracle := SolidityImport.Differential.oracle
private def userA : Nat := 0xa11ce

private def runTx (model : CompilationModel) (world : Verity.ContractState)
    (name : String) (args : List Nat) (resetTransient : Bool := true) :
    Option (Bool × List Nat × Verity.ContractState) := do
  let fn ← model.functions.find? (·.name == name)
  let base := if resetTransient then beginTransaction world else world
  let r := denoteFunction oracle model fn { sender := 0x5e, functionSelector := 0, args } base
  let final := match bindExternalParams 0 fn.bindingParams args with
    | none => base
    | some bindings =>
        match execStmtList oracle (effectiveFields model)
            { world := base, bindings, errors := model.errors } fn.body with
        | .stop st | .continue st | .return _ st => st.world
        | .revert | .revertWithData _ => base
  return (r.success, r.returnWords, final)

private def checkSequence (model : CompilationModel) : Bool :=
  (do
    let (ok0, w0, st0) ← runTx model Verity.defaultState "readState" [userA]
    let (ok1, w1, st1) ← runTx model st0 "addDirect" [10, userA]
    let (ok2, w2, st2) ← runTx model st1 "addInBatch" [5, 7, userA]
    let (ok3, _, st3) ← runTx model st2 "addInBatchRevert" [99, userA]
    let (ok4, w4, st4) ← runTx model st3 "readState" [userA]
    -- Reentrant frame with transient slot 0 (_inBatch) already set to 1:
    let reentrantWorld := st4.writeTransient 0 (.ofNat 1)
    let (ok5, _, _) ← runTx model reentrantWorld "addInBatch" [1, 1, userA] (resetTransient := false)
    let (ok6, w6, st6) ← runTx model reentrantWorld "addDirect" [4, userA] (resetTransient := false)
    let (ok7, w7, _) ← runTx model st6 "readState" [userA] (resetTransient := false)
    return ok0 && w0 == [0, 0, 0, 0] &&
           ok1 && w1 == [10] &&
           ok2 && w2 == [47] &&
           !ok3 &&
           ok4 && w4 == [27, 1, 15, 0] &&
           !ok5 &&
           ok6 && w6 == [35] &&
           ok7 && w7 == [35, 2, 19, 1]) == some true

#guard checkSequence ir.model
#guard checkSequence legacy.model

/--
error: TransientWithSlotGetterFixture.sol:98:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _inBatch is unsupported
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
error: TransientWithSlotGetterFixture.sol:33:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _inBatch is unsupported
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
error: TransientWithSlotGetterFixture.sol:43:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a closure that accesses transient state variable _inBatch is unsupported
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

end SolidityImportSmoke.TransientWithSlotGetterChecks
