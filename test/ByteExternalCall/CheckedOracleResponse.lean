import Compiler.SolidityImport.StaticOracleMocks
import Compiler.Hex

open Lean Compiler.CompilationModel Compiler.CompilationModel.ByteExternalCall
open Compiler.CompilationModel.SolidityImport.StaticOracleMocks

/-- Independent `checked-static-oracle-v1` responses for explicit configurations
and calldata, compared by `check_checked_static_oracle_mock.py` with real EVM. -/
private def word (item : Json) (key : String) : IO Nat := do
  let text ← IO.ofExcept (item.getObjValAs? String key)
  let some value := text.toNat? | throw (IO.userError s!"invalid {key}")
  return value

private def hexBytes (text : String) : IO (List UInt8) := do
  let digits := text.toList.drop 2
  unless text.startsWith "0x" && digits.length % 2 == 0 do throw (IO.userError "invalid calldata hex")
  let rec go : List Char → IO (List UInt8)
    | high :: low :: rest => do
        let some h := Compiler.Hex.hexCharToNat? high | throw (IO.userError "invalid hex digit")
        let some l := Compiler.Hex.hexCharToNat? low | throw (IO.userError "invalid hex digit")
        return UInt8.ofNat (h * 16 + l) :: (← go rest)
    | _ => pure []
  go digits

def main (args : List String) : IO UInt32 := do
  let [input, output] := args | throw (IO.userError "expected INPUT OUTPUT")
  let items ← IO.ofExcept ((← IO.ofExcept (Json.parse (← IO.FS.readFile input))).getArr?)
  let some adversary := (checkedEnvironment [1000] 1).adversary
    | throw (IO.userError "checked mock has no adversary")
  let results ← items.toList.mapM fun item => do
    let slots := [← word item "value", ← word item "failed", ← word item "length",
                  ← word item "expected", ← word item "expectedLength"]
    let calldata ← hexBytes (← IO.ofExcept (item.getObjValAs? String "calldata"))
    let world := Verity.defaultState.withStorageWords fun key =>
      match key with
      | .contractSlot 1000 index => Verity.Core.Uint256.ofNat (slots.getD index 0)
      | _ => 0
    let request : Request :=
      { kind := .staticcall, caller := 900, target := 1000, value := 0, calldata, gas := 1 }
    let response := adversary.respond request world
    let touched := response.accesses.filterMap fun
      | .contractSlot 1000 index => some index
      | _ => none
    unless touched.length == response.accesses.length do
      throw (IO.userError "checked mock touched a foreign key")
    pure (Json.mkObj [("success", toJson response.succeeded),
      ("data", toJson (response.returndata.map UInt8.toNat)), ("touched", toJson touched)])
  IO.FS.writeFile output (Json.compress (toJson results))
  return 0
