import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.CheckedArgumentChecks

open Compiler.CompilationModel

solidity_profile checkedArguments where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_profile checkedArgumentsLegacy where
  evmVersion := "osaka"
  viaIR := false
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import fixture from "Contracts/SolidityImportSmoke"
  entry "CheckedArgumentSequence.sol"
  using checkedArguments
  contract CheckedArgumentFixture
  function callChecked(address,uint256,uint256)
  function callOverflow(address,uint256)
  function callDynamic(address,bytes,uint256)
  function callVoid(address,uint256,uint256)
  function emitMeasured(uint256,uint256)
  function revertField(uint256)
  function revertNamedField()
  function seedWeight(uint256)
  function read()

solidity_import fixtureLegacy from "Contracts/SolidityImportSmoke"
  entry "CheckedArgumentSequence.sol"
  using checkedArgumentsLegacy
  contract CheckedArgumentFixture
  function callChecked(address,uint256,uint256)
  function callOverflow(address,uint256)
  function callDynamic(address,bytes,uint256)
  function callVoid(address,uint256,uint256)
  function emitMeasured(uint256,uint256)
  function revertField(uint256)
  function revertNamedField()
  function seedWeight(uint256)
  function read()

private def runCall (world : Verity.ContractState) (name : String) (args : List Nat) :
    Option (Bool × Option Nat × Option (List UInt8) × List (List Nat) × Verity.ContractState) := do
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
  | .continue st => some (true, none, none, Denote.encodeEvents st.world.events, st.world)
  | .stop st => some (true, none, none, Denote.encodeEvents st.world.events, st.world)
  | .return v st => some (true, some v, none, Denote.encodeEvents st.world.events, st.world)
  | .revert => some (false, none, none, [], world)
  | .revertWithData bytes => some (false, none, some bytes, [], world)

private def panicData (code : Nat) : List UInt8 := Denote.panicBytes code

private def customErrorData (name : String) (args : List Nat) : Option (List UInt8) :=
  Denote.customErrorBytes SolidityImport.Differential.oracle fixture.model.errors name args

-- Left-to-right order: `value.toUint104()` reverts with `ValueTooWide(2^104)` BEFORE
-- `other - 1` underflows (`other = 0`) and BEFORE the external call runs.
#guard
  let tooWide := 2 ^ 104
  match runCall Verity.defaultState "callChecked" [0x1234, tooWide, 0] with
  | some (false, none, some bytes, _, _) =>
      some bytes == customErrorData "ValueTooWide" [tooWide]
  | _ => false

-- Second argument underflow (`other - 1` when `other = 0`) reverts with `Panic(0x11)`
-- BEFORE the external call executes.
#guard
  match runCall Verity.defaultState "callChecked" [0x1234, 5, 0] with
  | some (false, none, some bytes, _, _) => bytes == panicData 0x11
  | _ => false

-- Checked addition overflow in external call reverts with `Panic(0x11)`.
#guard
  match runCall Verity.defaultState "callOverflow" [0x1234, 2 ^ 256 - 1] with
  | some (false, none, some bytes, _, _) => bytes == panicData 0x11
  | _ => false

-- Void external call with checked library downcast reverts with `ValueTooWide` before call.
#guard
  let tooWide := 2 ^ 104
  match runCall Verity.defaultState "callVoid" [0x1234, tooWide, 2 ^ 256 - 1] with
  | some (false, none, some bytes, _, _) =>
      some bytes == customErrorData "ValueTooWide" [tooWide]
  | _ => false

-- Event with checked arithmetic + storage member read: emits exact words on success,
-- reverts with `Panic(0x11)` on overflow or underflow.
#guard
  match runCall Verity.defaultState "seedWeight" [10] with
  | some (true, _, _, _, seeded) =>
      let okEmit := match runCall seeded "emitMeasured" [3, 4] with
        | some (true, _, _, [[7, 7]], _) => true
        | _ => false
      let overflowEmit := match runCall seeded "emitMeasured" [2 ^ 256 - 1, 1] with
        | some (false, _, some bytes, _, _) => bytes == panicData 0x11
        | _ => false
      let underflowEmit := match runCall seeded "emitMeasured" [11, 0] with
        | some (false, _, some bytes, _, _) => bytes == panicData 0x11
        | _ => false
      okEmit && overflowEmit && underflowEmit
  | _ => false

-- Custom-error arguments: checked storage expression and named storage struct member read.
#guard
  match runCall Verity.defaultState "seedWeight" [42] with
  | some (true, _, _, _, seeded) =>
      let exprErr := match runCall seeded "revertField" [5] with
        | some (false, _, some bytes, _, _) =>
            some bytes == customErrorData "FieldTooSmall" [47]
        | _ => false
      let namedErr := match runCall seeded "revertNamedField" [] with
        | some (false, _, some bytes, _, _) =>
            some bytes == customErrorData "FieldTooSmall" [42]
        | _ => false
      exprErr && namedErr
  | _ => false

end SolidityImportSmoke.CheckedArgumentChecks
