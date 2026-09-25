import Compiler.SolidityImport.TransactionAccess
import Compiler.Hex
import Lean.Data.Json

/-! JSON bridge for the scalar Denote sequence adapter. Input ABI arguments are
explicit model words; decoding source calldata remains the campaign's job.
Unsupported observations fail instead of supplying synthetic values. -/
namespace Compiler.CompilationModel.SolidityImport.SequenceRunner
open Lean Denote Transactions Verity.Core

private def word (j : Json) : Except String Nat := do
  let s ← j.getStr?
  let some n := s.toNat? | throw "expected decimal model word"
  unless n < 2^256 do throw "model word exceeds uint256"
  return n

private def getWord (j : Json) (key : String) : Except String Nat := do
  word (← j.getObjVal? key)

private def hexBytes (bytes : List UInt8) : String :=
  "0x" ++ String.ofList (bytes.flatMap fun byte =>
    [Compiler.Hex.hexDigit (byte.toNat / 16), Compiler.Hex.hexDigit (byte.toNat % 16)])

private def hexWord (n : Nat) : String := hexBytes (wordBytes n)
private def hexAddress (n : Nat) : String := hexBytes ((wordBytes n).drop 12)

private def pair (j : Json) : Except String (Nat × Nat) := do
  match (← j.getArr?).toList with
  | [a, b] => return (← word a, ← word b)
  | _ => throw "expected pair of decimal words"

/-- Replay one pinned initial storage world through real Denote execution. -/
def execute (model : CompilationModel) (oracle : DenoteOracle) (input : Json) :
    Except String Json := do
  let account ← getWord input "account"
  unless account < 2^160 do throw "model account exceeds address width"
  let storage ← (← (← input.getObjVal? "storage").getArr?).toList.mapM pair
  unless (storage.map Prod.fst).eraseDups.length == storage.length do
    throw "duplicate initial model storage slot"
  let mut world := Verity.defaultState.withStorageWords fun key =>
    match key with
    | .slot slot => Uint256.ofNat ((storage.find? (·.1 == slot)).map Prod.snd |>.getD 0)
    | _ => 0
  let transactions ← (← input.getObjVal? "transactions").getArr?
  let mut rows := #[]
  let mut ids : List String := []
  for transaction in transactions do
    let ident ← transaction.getObjValAs? String "id"
    if ident.isEmpty || ids.contains ident then throw "nonempty unique model transaction ids required"
    ids := ident :: ids
    let name ← transaction.getObjValAs? String "function"
    let candidates := model.functions.filter (·.name == name)
    let [fn] := candidates | throw s!"model function must resolve uniquely: {name}"
    let args ← (← (← transaction.getObjVal? "args").getArr?).toList.mapM word
    unless args.length == fn.params.length do throw "model argument count differs"
    let sender ← getWord transaction "sender"
    unless sender < 2^160 do throw "model sender exceeds address width"
    let target ← getWord transaction "target"
    unless target == account do throw "foreign model target not supported by scalar adapter"
    let value ← getWord transaction "value"
    unless value == 0 do throw "model adapter does not yet account for value transfers"
    let timestamp ← getWord transaction "timestamp"
    let number ← getWord transaction "blockNumber"
    let observed ← (← (← transaction.getObjVal? "observe").getArr?).toList.mapM pair
    unless observed.all (fun p => p.1 == account) do
      throw "foreign storage observation not supported by scalar adapter"
    world := { world with
      sender := Address.ofNat sender
      txOrigin := Address.ofNat sender
      thisAddress := Address.ofNat account
      msgValue := 0
      blockTimestamp := Uint256.ofNat timestamp
      blockNumber := Uint256.ofNat number
      chainId := 31337 }
    let result ← executeTracedBody oracle (effectiveFields model) world
      ((fn.params.map (·.name)).zip args) fn.body
    unless result.frame.world.events.isEmpty do throw "exact event encoding is unavailable"
    let touched ← result.touched.filterMapM fun key =>
      match key with
      | .slot slot => pure (some slot)
      | .transient _ => pure none
      | _ => throw "unencoded model storage key"
    let touched := touched.eraseDups
    let slots := (touched ++ observed.map Prod.snd).eraseDups
    world := result.frame.world
    rows := rows.push (Json.mkObj [
      ("id", toJson ident), ("status", toJson (if result.frame.success then "ok" else "revert")),
      ("data", toJson (hexBytes result.frame.data)),
      ("touched", toJson (touched.map fun slot => [hexAddress account, hexWord slot])),
      ("storage", toJson (slots.map fun slot =>
        [hexAddress account, hexWord slot, hexWord (world.readSlot slot).val])),
      ("events", Json.arr #[])])
  return Json.arr rows

/-- The generated model driver supplies the actual model and hash oracle. -/
def run (model : CompilationModel) (oracle : DenoteOracle) (args : List String) : IO UInt32 := do
  let [input, output] := args | throw (IO.userError "expected INPUT OUTPUT")
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  let result ← IO.ofExcept (execute model oracle parsed)
  IO.FS.writeFile output (Json.compress result)
  return 0
end Compiler.CompilationModel.SolidityImport.SequenceRunner
