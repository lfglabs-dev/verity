import Contracts.Smoke.Storage

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

-- Solidity-0.8 checked `int256` arithmetic plus an `Int256` storage field.
-- Signed add/sub/mul/div panic on overflow / `minValue / -1` / divide-by-zero,
-- and a negative-branch `if` uses signed comparison (`slt`).
verity_contract Int256CheckedSmoke where
  storage
    last : Int256 := slot 0

  function addChecked (a : Int256, b : Int256) : Int256 := do
    let sum ← addPanic a b
    setStorage last sum
    return sum

  function subChecked (a : Int256, b : Int256) : Int256 := do
    let diff ← subPanic a b
    setStorage last diff
    return diff

  function mulChecked (a : Int256, b : Int256) : Int256 := do
    let prod ← mulPanic a b
    setStorage last prod
    return prod

  function divChecked (a : Int256, b : Int256) : Int256 := do
    let q ← divPanic a b
    setStorage last q
    return q

  function negChecked (a : Int256) : Int256 := do
    let n ← negPanic a
    setStorage last n
    return n

  function applyDelta (delta : Int256) : Int256 := do
    let current ← getStorage last
    if delta < 0 then
      let flipped ← negPanic delta
      let next ← subPanic current flipped
      setStorage last next
      return next
    else
      let next ← addPanic current delta
      setStorage last next
      return next

#check_contract Int256CheckedSmoke

-- G28 regression: an `Int256` storage read feeds the *signed* checked add in
-- the executable plane. Before the fix `getStorage last` bound a raw `Uint256`
-- word, so `addPanic current delta` used unsigned `addPanic` and reverted on
-- `-1 + 25` (the words wrap mod 2^256) while Solidity `int256 +=` succeeds.
private def okB {α : Type} : ContractResult α → Bool
  | .success _ _ => true
  | .revert _ _ => false

private def slot0After {α : Type} : ContractResult α → Uint256
  | .success _ s => s.readSlot 0
  | .revert _ s => s.readSlot 0

private def int256MinusOneState : ContractState :=
  Verity.defaultState.writeSlot 0 (Verity.Core.Uint256.ofNat (2 ^ 256 - 1))

example :
    ((Int256CheckedSmoke.applyDelta (Verity.Core.Int256.ofInt 25)).run int256MinusOneState |> okB) = true := by decide +kernel

example :
    slot0After ((Int256CheckedSmoke.applyDelta (Verity.Core.Int256.ofInt 25)).run int256MinusOneState) = 24 := by decide +kernel

-- Signed overflow still panics: `maxValue + 1`.
private def int256MaxState : ContractState :=
  Verity.defaultState.writeSlot 0 (Verity.Core.Uint256.ofNat (2 ^ 255 - 1))

example :
    ((Int256CheckedSmoke.applyDelta (Verity.Core.Int256.ofInt 1)).run int256MaxState |> okB) = false := by decide +kernel

/-! Revert bytes of a signed overflow (`maxValue + 1`), on both planes.

Fix #12 (`614a0ec7b`) made the macro lower signed checked arithmetic to
`Stmt.panic`; before it the model reverted with `Error("Panic(0x11): …")`.
Both examples pin the exact `Panic(0x11)` ABI bytes: the first fails if the
macro-generated model regresses, the second if the EDSL does. -/

private def noHashOracle : Compiler.CompilationModel.Denote.DenoteOracle :=
  { mappingSlot := fun _ _ => 0, keccakMemorySlice := fun _ _ _ => 0 }

private def modelAddOverflowRevertData : Option (List UInt8) :=
  (Int256CheckedSmoke.spec.functions.find? (·.name == "addChecked")).bind fun fn =>
    (Compiler.CompilationModel.Denote.denoteFunction noHashOracle Int256CheckedSmoke.spec fn
      { sender := 0, functionSelector := 0, args := [2 ^ 255 - 1, 1] }
      Verity.defaultState).revertData

private def edslAddOverflowRevertData : Option (List UInt8) :=
  match (Int256CheckedSmoke.addChecked (Verity.Core.Int256.ofInt (2 ^ 255 - 1))
      (Verity.Core.Int256.ofInt 1)).run Verity.defaultState with
  | .revert payload _ => some payload.encode
  | .success _ _ => none

example : modelAddOverflowRevertData =
    some (Verity.Core.RevertPayload.encode (.panic 0x11)) := by decide +kernel

example : edslAddOverflowRevertData =
    some (Verity.Core.RevertPayload.encode (.panic 0x11)) := by decide +kernel

example : Int256CheckedSmoke.spec.fields.any (fun field =>
    field.name == "last" && field.slot == some 0 &&
      match field.ty with
      | Compiler.CompilationModel.FieldType.int256 => true
      | _ => false) := by decide

end Contracts.Smoke
