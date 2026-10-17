import Lean
import Compiler.SolidityImport.TransactionAccess
import Verity.Core.Model.DenoteByteExternalCalls

open Lean Compiler.CompilationModel
open SolidityImport.Transactions Denote

private def oracle : DenoteOracle :=
  { mappingSlot := fun _ _ => 0, keccakMemorySlice := fun _ _ _ => 0 }

private def natural (item : Json) (key : String) : IO Nat := do
  IO.ofExcept ((← IO.ofExcept (item.getObjVal? key)).getNat?)

private def pair (row : Json) : IO (Nat × Nat) := do
  let cells ← IO.ofExcept row.getArr?
  unless cells.size = 2 do throw (IO.userError "access pair must have two cells")
  return (← IO.ofExcept cells[0]!.getNat?, ← IO.ofExcept cells[1]!.getNat?)

private def runCase (item : Json) : IO Json := do
  let success ← IO.ofExcept ((← IO.ofExcept (item.getObjVal? "success")).getBool?)
  let payload ← IO.ofExcept ((← IO.ofExcept (item.getObjVal? "payload")).getArr?)
  let bytes ← payload.toList.mapM fun value => do
    let n ← IO.ofExcept value.getNat?
    unless n < 256 do throw (IO.userError "invalid response byte")
    pure (UInt8.ofNat n)
  let caller ← natural item "caller"
  let target ← natural item "target"
  let cells ← IO.ofExcept ((← IO.ofExcept (item.getObjVal? "storage")).getArr?)
  let storage ← cells.toList.mapM fun row => do
    let values ← IO.ofExcept row.getArr?
    unless values.size = 3 do throw (IO.userError "storage row must have three cells")
    let account ← IO.ofExcept values[0]!.getNat?
    let slot ← IO.ofExcept values[1]!.getNat?
    let value ← IO.ofExcept values[2]!.getNat?
    pure (Verity.StorageKey.contractSlot account slot, value)
  let accesses ← IO.ofExcept ((← IO.ofExcept (item.getObjVal? "touched")).getArr?)
  let touched ← accesses.toList.mapM fun row => do
    let (account, slot) ← pair row
    pure (Verity.StorageKey.contractSlot account slot)
  let entry := { Verity.defaultState with
    thisAddress := Verity.Core.Address.ofNat caller
    storageWords := fun key => Verity.Core.Uint256.ofNat
      (storage.find? (fun row => row.1 == key) |>.map Prod.snd |>.getD 0) }
  let response := DenoteByteExternalCalls.staticAdversary fun request world =>
    if request.kind == .staticcall && request.caller == caller && request.target == target &&
        request.value == 0 && request.gas == 100000 &&
        request.calldata == [0xa0, 0x35, 0xb1, 0xfe] && (world.memory 64).val == 160 then
      (success, bytes, touched)
    else (false, [0xff], [])
  let state : DenoteState :=
    { world := beginTransaction entry, bindings := [],
      byteCallAdversary := some response, byteCallGas := some 100000 }
  let body : List Stmt :=
    [.mstore (.literal 64) (.literal 128),
     .ecm (Compiler.ECM.SolidityStaticCall.uint256Module "result" 0xa035b1fe 0)
       [.literal target],
     .return (.localVar "result")]
  let traced ← IO.ofExcept (traceStraightLine oracle [] state body)
  let frame ← IO.ofExcept (finishFrame state.world traced.outcome)
  unless traced.touched == touched do throw (IO.userError "canonical byte-call access trace differs")
  unless frame.world.events.isEmpty do throw (IO.userError "staticcall emitted logs")
  let finalStorage := storage.map fun (key, _) => (frame.world.storageWords key).val
  unless finalStorage == storage.map Prod.snd do throw (IO.userError "staticcall/rollback changed storage")
  return Json.mkObj [("success", toJson frame.success),
    ("data", toJson (frame.data.map UInt8.toNat)),
    ("touched", toJson traced.touched.length), ("storage", toJson finalStorage),
    ("events", Json.arr #[])]

def main (args : List String) : IO UInt32 := do
  let [input, output] := args | throw (IO.userError "expected INPUT OUTPUT")
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  let rows ← IO.ofExcept parsed.getArr?
  let results ← rows.toList.mapM runCase
  IO.FS.writeFile output (Json.compress (toJson results))
  return 0
