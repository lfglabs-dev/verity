import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-! Discarded `bytes memory` helper calls and typed external calls without return values do not
depend on the state-variable count (#2830).

`EffectCoreOneSlot` declares one state variable and `EffectCoreTwoSlots` is the same contract
plus an unrelated `uint256` and an unused function. Every function imports to the same body from
both, and its denotation matches solc 0.8.34 on Anvil (osaka, runs 466; legacy and via-IR, both
contracts):

* a discarded `bytes memory` helper call inlines its body whether its result is named or not
  (`discardNamed`, `discardDividing`, `discardEarly`, `discardUnassigned`; before this change a
  named result was rejected with one state variable and inlined with two);
* `voidWord`: a typed external call to an account without code evaluates its arguments first
  (`10 / 0` gives Panic 0x12), then reverts with no data;
* `voidStored` (legacy only): legacy ABI-encodes a storage `bytes` argument before the
  `extcodesize` check, so a corrupt length gives Panic 0x22 for an account without code. Via-IR
  checks `extcodesize` first (no data); a storage reference argument of such a call is rejected
  under via-IR (`check_storage_rejections`, `void-call-storage-argument-*`).

The external `buf = I(a).f(args)` route with a `bytes` result, which modelled a CALL with
selector 0 with more than one state variable, is rejected for every state-variable count
(`check_storage_rejections`, `external-bytes-assignment-*`). -/

namespace SolidityImportSmoke.EffectCoreStateCountChecks
open Compiler.CompilationModel

solidity_import oneLegacy from "Contracts/SolidityImportSmoke" entry "EffectCoreOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EffectCoreOneSlot
  function discardNamed(uint256)
  function discardDividing(uint256)
  function discardEarly(uint256)
  function discardUnassigned(uint256)
  function discardUnnamed(uint256)
  function voidWord(address,uint256)
  function voidStored(address)

solidity_import twoLegacy from "Contracts/SolidityImportSmoke" entry "EffectCoreTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EffectCoreTwoSlots
  function discardNamed(uint256)
  function discardDividing(uint256)
  function discardEarly(uint256)
  function discardUnassigned(uint256)
  function discardUnnamed(uint256)
  function voidWord(address,uint256)
  function voidStored(address)

solidity_import oneIr from "Contracts/SolidityImportSmoke" entry "EffectCoreOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EffectCoreOneSlot
  function discardNamed(uint256)
  function discardDividing(uint256)
  function discardEarly(uint256)
  function discardUnassigned(uint256)
  function discardUnnamed(uint256)
  function voidWord(address,uint256)

solidity_import twoIr from "Contracts/SolidityImportSmoke" entry "EffectCoreTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EffectCoreTwoSlots
  function discardNamed(uint256)
  function discardDividing(uint256)
  function discardEarly(uint256)
  function discardUnassigned(uint256)
  function discardUnnamed(uint256)
  function voidWord(address,uint256)

private def body (model : CompilationModel) (name : String) : String :=
  match model.functions.find? (·.name == name) with
  | some f => (repr f.body).pretty 100000
  | none => ""

/-- The function imports and its body does not depend on the unrelated slot. -/
private def sameBody (one two : CompilationModel) (name : String) : Bool :=
  body one name != "" && body one name == body two name

/-- Storage slot 0 (the `bytes` length word) set to `word`. -/
private def slotZero (word : Nat) : Verity.ContractState :=
  Verity.defaultState.writePhysicalSlot 0 (Verity.Core.Uint256.ofNat word)

private def run (model : CompilationModel) (name : String) (args : List Nat)
    (st : Verity.ContractState := Verity.defaultState) : Option Denote.DenoteResult :=
  (model.functions.find? (·.name == name)).map fun f =>
    Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args } st

private def allModels : List CompilationModel :=
  [oneLegacy.model, twoLegacy.model, oneIr.model, twoIr.model]

private def legacyModels : List CompilationModel :=
  [oneLegacy.model, twoLegacy.model]

private def returns (model : CompilationModel) (name : String) (args : List Nat) (n : Nat) : Bool :=
  match run model name args with
  | some r => r.success && (r.returnWords == [n] || (r.returnWords.isEmpty && r.returnValue == some n))
  | none => false

/-- solc reverts with `Panic(code)` (selector `0x4e487b71`). -/
private def panics (model : CompilationModel) (name : String) (args : List Nat) (code : Nat)
    (st : Verity.ContractState := Verity.defaultState) : Bool :=
  match run model name args st with
  | some r => !r.success && r.revertData == some ([0x4e, 0x48, 0x7b, 0x71] ++ List.replicate 31 0 ++ [code.toUInt8])
  | none => false

/-- solc reverts with no data. -/
private def revertsEmpty (model : CompilationModel) (name : String) (args : List Nat)
    (st : Verity.ContractState := Verity.defaultState) : Bool :=
  match run model name args st with
  | some r => !r.success && r.revertData == some []
  | none => false

/-- An account without code. -/
private def codeless : Nat := 0xdead

#guard sameBody oneLegacy.model twoLegacy.model "discardNamed"
#guard sameBody oneLegacy.model twoLegacy.model "discardDividing"
#guard sameBody oneLegacy.model twoLegacy.model "discardEarly"
#guard sameBody oneLegacy.model twoLegacy.model "discardUnassigned"
#guard sameBody oneLegacy.model twoLegacy.model "discardUnnamed"
#guard sameBody oneLegacy.model twoLegacy.model "voidWord"
#guard sameBody oneLegacy.model twoLegacy.model "voidStored"
#guard sameBody oneIr.model twoIr.model "discardNamed"
#guard sameBody oneIr.model twoIr.model "discardDividing"
#guard sameBody oneIr.model twoIr.model "discardEarly"
#guard sameBody oneIr.model twoIr.model "discardUnassigned"
#guard sameBody oneIr.model twoIr.model "discardUnnamed"
#guard sameBody oneIr.model twoIr.model "voidWord"

#guard allModels.all (returns · "discardNamed" [0] 32)
#guard allModels.all (returns · "discardNamed" [7] 32)
#guard allModels.all (panics · "discardDividing" [0] 0x12)
#guard allModels.all (returns · "discardDividing" [2] 32)
#guard allModels.all (returns · "discardEarly" [3] 1)
#guard allModels.all (returns · "discardEarly" [9] 10)
#guard allModels.all (returns · "discardUnassigned" [4] 33)
#guard allModels.all (returns · "discardUnnamed" [300] 2)
#guard allModels.all (panics · "voidWord" [codeless, 0] 0x12)
#guard allModels.all (revertsEmpty · "voidWord" [codeless, 1])
#guard legacyModels.all (revertsEmpty · "voidStored" [codeless])
#guard legacyModels.all (panics · "voidStored" [codeless] 0x22 (slotZero 3))
#guard legacyModels.all (revertsEmpty · "voidStored" [codeless] (slotZero 129))

end SolidityImportSmoke.EffectCoreStateCountChecks
