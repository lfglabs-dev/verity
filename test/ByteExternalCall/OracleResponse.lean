import Compiler.SolidityImport.StaticOracleMocks

open Lean Compiler.CompilationModel.SolidityImport.StaticOracleMocks

def main (args : List String) : IO UInt32 := do
  let [input, output] := args | throw (IO.userError "expected INPUT OUTPUT")
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  let items ← IO.ofExcept parsed.getArr?
  let results ← items.toList.mapM fun item => do
    let text ← IO.ofExcept (item.getObjValAs? String "value")
    let some value := text.toNat? | throw (IO.userError "invalid value")
    let length ← IO.ofExcept (item.getObjValAs? Nat "length")
    pure (toJson ((responseBytes value length).map UInt8.toNat))
  IO.FS.writeFile output (Json.compress (toJson results))
  return 0
