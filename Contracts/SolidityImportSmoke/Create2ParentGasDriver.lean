import Verity.Core.Model.Create2ParentGas
import Lean.Data.Json

namespace SolidityImportSmoke.Create2ParentGasDriver
open Lean
open Compiler.CompilationModel.Create2ParentGas

private def natField (row : Json) (name : String) : Except String Nat := do
  let text ← (← row.getObjVal? name).getStr?
  let some value := text.toNat? | throw ("invalid natural field: " ++ name)
  pure value

private def execute (row : Json) : Except String Json := do
  let id ← (← row.getObjVal? "id").getStr?
  let gas ← natField row "gas"
  let oldWords ← natField row "oldWords"
  let offset ← natField row "offset"
  let size ← natField row "size"
  match charge gas oldWords offset size with
  | .outOfGas => pure (Json.mkObj [("id", .str id), ("status", .str "outOfGas")])
  | .charged state =>
      pure (Json.mkObj [("id", .str id), ("status", .str "charged"),
        ("opcodeGas", .str (toString state.opcodeGas)),
        ("childGas", .str (toString state.childGas)),
        ("reservedGas", .str (toString state.reservedGas)),
        ("memoryWords", .str (toString state.memoryWords))])

def executeInputs (input : Json) : Except String Json := do
  pure (.arr (← (← input.getArr?).toList.mapM execute).toArray)

end SolidityImportSmoke.Create2ParentGasDriver

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile input))
      let result ← IO.ofExcept (SolidityImportSmoke.Create2ParentGasDriver.executeInputs parsed)
      IO.FS.writeFile output (result.compress ++ "\n")
      pure 0
  | _ => throw (IO.userError "expected CREATE2 parent gas input and output paths")
