import Lean
import Compiler.SolidityImport.Transactions
import Verity.Core.Model.DenoteByteExternalCalls

open Lean Compiler.CompilationModel

def main (args : List String) : IO UInt32 := do
  let [input, output] := args | throw (IO.userError "expected INPUT OUTPUT")
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  let items ← IO.ofExcept parsed.getArr?
  let results ← items.toList.mapM fun item => do
    let success ← IO.ofExcept ((← IO.ofExcept (item.getObjVal? "success")).getBool?)
    let payload ← IO.ofExcept ((← IO.ofExcept (item.getObjVal? "payload")).getArr?)
    let bytes ← payload.toList.mapM fun value => do
      let value ← IO.ofExcept value.getNat?
      unless value < 256 do throw (IO.userError "response byte exceeds UInt8")
      pure (UInt8.ofNat value)
    let state : DenoteByteExternalCalls.State :=
      { frame := { world := Verity.defaultState, bindings := [] }, returndata := bytes }
    let frame ← IO.ofExcept (SolidityImport.Transactions.finishFrame Verity.defaultState
      (DenoteByteExternalCalls.decodeStaticUint256 { success, state }))
    pure (Json.mkObj [("success", toJson frame.success),
                      ("data", toJson (frame.data.map UInt8.toNat))])
  IO.FS.writeFile output (Json.compress (toJson results))
  return 0
