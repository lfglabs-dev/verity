import Verity.Core.Model.InitCodeExecution
import Lean.Data.Json

namespace SolidityImportSmoke.InitCodeExecutionDriver
open Lean
open Compiler.CompilationModel.InitCodeExecution
open Compiler.CompilationModel.DenoteMemory

private def parseByte (j : Json) : Except String Byte := do
  let value ← j.getNat?
  if h : value < 256 then pure ⟨value, h⟩ else throw "initcode byte exceeds 255"

private def execute (row : Json) : Except String Json := do
  let id ← (← row.getObjVal? "id").getStr?
  unless id != "" do throw "missing initcode identity"
  let fuel ← (← row.getObjVal? "fuel").getNat?
  unless fuel ≤ 10000 do throw "initcode instruction budget exceeds 10000"
  let code ← (← (← row.getObjVal? "code").getArr?).toList.mapM parseByte
  match run fuel code {} with
  | .returned bytes =>
      pure (Json.mkObj [("id", .str id), ("status", .str "returned"),
                       ("data", .arr (bytes.map (fun byte => toJson byte.val)).toArray)])
  | .failed error =>
      pure (Json.mkObj [("id", .str id), ("status", .str "failed"), ("error", .str (reprStr error))])
  | .running _ => throw "bounded initcode executor returned an unterminated state"

def executeInputs (input : Json) : Except String Json := do
  let rows ← input.getArr?
  let outputs ← rows.toList.mapM execute
  pure (.arr outputs.toArray)

end SolidityImportSmoke.InitCodeExecutionDriver

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile input))
      let result ← IO.ofExcept (SolidityImportSmoke.InitCodeExecutionDriver.executeInputs parsed)
      IO.FS.writeFile output (result.compress ++ "\n")
      pure 0
  | _ => throw (IO.userError "expected initcode input and output JSON paths")
