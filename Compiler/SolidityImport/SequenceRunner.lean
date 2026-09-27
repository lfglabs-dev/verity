import Compiler.SolidityImport.TransactionAccess
import Compiler.Hex
import Compiler.Keccak.Sponge
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.SelectorInteropHelpers
import Lean.Data.Json

/-! JSON bridge for the Denote sequence adapter. Input arguments are complete
word-aligned source ABI payloads, decoded using the function binding policy.
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

/-- Scalar ABI cleanup matching the compiler's event-word normalization. -/
private def eventWord (ty : ParamType) (value : Nat) : Except String Nat := do
  match ty with
  | .uint256 | .bytes32 => pure (value % 2^256)
  | .uint8 => pure (value % 2^8)
  | .uint16 => pure (value % 2^16)
  | .uintN bits =>
      unless 0 < bits && bits ≤ 256 && bits % 8 == 0 do throw "invalid event integer width"
      pure (value % 2^bits)
  | .address => pure (value % 2^160)
  | .bool => pure (if value == 0 then 0 else 1)
  | _ => throw "unsupported event observation parameter type"

/-- Exact scalar event encoding from actual Denote emissions and model declarations.
Denote's legacy eventless executor retains arguments in source order. -/
private def encodeEvent (account : Nat) (definitions : List EventDef)
    (event : Verity.Event) : Except String Json := do
  let [definition] := definitions.filter (·.name == event.name)
    | throw s!"observed event must resolve uniquely: {event.name}"
  unless event.indexedArgs.isEmpty do throw "unexpected pre-partitioned Denote event"
  unless definition.params.length == event.args.length do throw "event argument count differs"
  let pairs ← (definition.params.zip event.args).mapM fun (parameter, value) => do
    pure (parameter, ← eventWord parameter.ty value.val)
  let indexed := pairs.filter (fun p => p.1.kind == .indexed)
  unless indexed.length ≤ 3 do throw "event has more than three indexed parameters"
  let topic0 := hexBytes (KeccakEngine.keccak256_str (eventSignature definition)).data.toList
  let topics := topic0 :: indexed.map (fun p => hexWord p.2)
  let data := (pairs.filter (fun p => p.1.kind == .unindexed)).flatMap (fun p => wordBytes p.2)
  return Json.mkObj [("address", toJson (hexAddress account)),
    ("topics", toJson topics), ("data", toJson (hexBytes data))]

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
  let externalFns := model.functions.filter fun fn =>
    !fn.isInternal && !isInteropEntrypointName fn.name
  let dispatch := externalFns.map fun fn =>
    (fn, (KeccakEngine.keccak256_selector (functionSignature fn)).toNat)
  unless (dispatch.map Prod.snd).eraseDups.length == dispatch.length do
    throw "ambiguous model function selectors"
  let transactions ← (← input.getObjVal? "transactions").getArr?
  let mut rows := #[]
  let mut ids : List String := []
  for transaction in transactions do
    let ident ← transaction.getObjValAs? String "id"
    if ident.isEmpty || ids.contains ident then throw "nonempty unique model transaction ids required"
    ids := ident :: ids
    let name ← transaction.getObjValAs? String "function"
    let candidates := externalFns.filter (·.name == name)
    let [fn] := candidates | throw s!"model function must resolve uniquely: {name}"
    let args ← (← (← transaction.getObjVal? "args").getArr?).toList.mapM word
    let selector ← getWord transaction "selector"
    unless selector < 2^32 do throw "model selector exceeds four bytes"
    let [selected] := dispatch.filter (fun entry => entry.2 == selector)
      | throw "source calldata selector does not resolve to a model function"
    unless selected.1.name == name do
      throw "source calldata selector differs from model function"
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
    let tx : DenoteTransaction :=
      { sender, txOrigin := sender, thisAddress := account, msgValue := value,
        blockTimestamp := timestamp, blockNumber := number, chainId := 31337,
        functionSelector := selector, args }
    let initial := beginTransaction (withTransactionContext world tx)
    let publicResult := denoteFunction oracle model fn tx initial
    let result : TracedFrameResult ←
      match bindExternalParams selector fn.bindingParams args with
      | none => pure ⟨⟨false, [], initial⟩, []⟩
      | some bindings =>
          executeTracedBody oracle (effectiveFields model) initial
            bindings fn.body model.events model.errors selector
    unless result.frame.success == publicResult.success do
      throw "traced execution status differs from public Denote"
    if publicResult.success then
      let returned := if publicResult.returnWords.isEmpty then publicResult.returnValue.toList
        else publicResult.returnWords
      unless result.frame.data == returned.flatMap wordBytes do
        throw "traced return data differs from public Denote"
    let emitted ← result.frame.world.events.mapM (encodeEvent account model.events)
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
      ("events", toJson emitted)])
  return Json.arr rows

/-- The generated model driver supplies the actual model and hash oracle. -/
def run (model : CompilationModel) (oracle : DenoteOracle) (args : List String) : IO UInt32 := do
  let [input, output] := args | throw (IO.userError "expected INPUT OUTPUT")
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  let result ← IO.ofExcept (execute model oracle parsed)
  IO.FS.writeFile output (Json.compress result)
  return 0
end Compiler.CompilationModel.SolidityImport.SequenceRunner
