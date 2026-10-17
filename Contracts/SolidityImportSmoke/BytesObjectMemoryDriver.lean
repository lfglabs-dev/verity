import Verity.Core.Model.BytesObjectMemory
import Lean.Data.Json

namespace SolidityImportSmoke.BytesObjectMemoryDriver
open Lean
open Compiler.CompilationModel.DenoteMemory
open Compiler.CompilationModel.BytesObjectMemory

private def parseByte (j : Json) : Except String Byte := do
  let value ← j.getNat?
  if h : value < 256 then pure ⟨value, h⟩ else throw "byte exceeds 255"

private def execute (row : Json) : Except String Json := do
  let id ← (← row.getObjVal? "id").getStr?
  let payload ← (← (← row.getObjVal? "payload").getArr?).toList.mapM parseByte
  let nextPayload ← (← (← row.getObjVal? "nextPayload").getArr?).toList.mapM parseByte
  unless payload.length ≤ 4096 && nextPayload.length ≤ 4096 do
    throw "memory object instrument length exceeds 4096"
  let firstBase := 128
  let nextBase := firstBase + 32 + paddedLength payload.length
  let first := materialize Memory.empty firstBase payload
  let afterNext := materialize first nextBase nextPayload
  let before := first.slice firstBase (32 + paddedLength payload.length)
  let after := afterNext.slice firstBase (32 + paddedLength payload.length)
  pure (Json.mkObj [("id", .str id),
    ("before", .arr (before.map (fun byte => toJson byte.val)).toArray),
    ("after", .arr (after.map (fun byte => toJson byte.val)).toArray)])

def executeInputs (input : Json) : Except String Json := do
  pure (.arr (← (← input.getArr?).toList.mapM execute).toArray)

end SolidityImportSmoke.BytesObjectMemoryDriver

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile input))
      let result ← IO.ofExcept (SolidityImportSmoke.BytesObjectMemoryDriver.executeInputs parsed)
      IO.FS.writeFile output (result.compress ++ "\n")
      pure 0
  | _ => throw (IO.userError "expected memory-object input and output paths")
