import Compiler.SolidityImport.ModelResponders

/-! Request-domain checks of the imported-model static responder: an in-domain
`STATICCALL` answers from the callee account's own storage, and every request or
execution outside the domain is rejected rather than answered. -/

open Lean Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport.ModelResponders
open ByteExternalCall

private def oracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩

private def getter (name : String) (isView : Bool) (body : List Stmt) : FunctionSpec :=
  { name, params := [], returnType := some .uint256, isView, body }

/-- One storage word, a view reader, a writer, a non-view reader, and read-only
functions that write or log. -/
private def model : CompilationModel :=
  { name := "Responder", fields := [{ name := "x", ty := .uint256, slot := some 0 }],
    constructor := none,
    events := [{ name := "Seen", params := [] }],
    functions := [
      getter "get" true [.return (.storage "x")],
      { name := "set", params := [{ name := "v", ty := .uint256 }], returnType := none,
        body := [.setStorage "x" (.param "v"), .stop] },
      getter "peek" false [.return (.storage "x")],
      getter "ownBalance" true [.return .selfBalance],
      { name := "echo", params := [{ name := "i", ty := .uint256 }], returnType := some .uint256,
        isView := true, body := [.return (.param "i")] },
      getter "viewWrites" true [.setStorage "x" (.literal 7), .return (.literal 1)],
      getter "viewLogs" true [.emit "Seen" [], .return (.literal 1)]] }

private def selectorBytes (name : String) : List UInt8 :=
  let selector := match model.functions.find? (·.name == name) with
    | some fn => (KeccakEngine.keccak256_selector (functionSignature fn)).toNat
    | none => 0
  (List.range 4).map fun index => UInt8.ofNat (selector / 2 ^ (8 * (3 - index)) % 256)

/-- The caller (900) holds balance 9 and slot 0 = 5; the callee (1000) holds
balance 3 and slot 0 = 42. -/
private def world : Verity.ContractState :=
  let base : Verity.ContractState := { Verity.defaultState with
    thisAddress := Verity.Core.Address.ofNat 900
    selfBalance := Verity.Core.Uint256.ofNat 9
    storageWords := fun key => Verity.Core.Uint256.ofNat
      (if key == Verity.StorageKey.contractSlot 1000 0 then 42 else
       if key == Verity.StorageKey.slot 0 then 5 else 0) }
  let callee := Verity.Core.Address.ofNat 1000
  base.writeAccount callee
    { base.accountWorld callee with balance := Verity.Core.Uint256.ofNat 3 }

private def request (kind : Kind) (target value : Nat) (calldata : List UInt8) : Request :=
  { kind, caller := 900, target, value, calldata, gas := 100000 }

private def answerOf (r : Request) : Option (Bool × List UInt8 × List Verity.StorageKey) :=
  answer oracle [(1000, model)] r world

def main : IO UInt32 := do
  -- In domain: the callee's own slot 0 (not the caller's) answers, and is the only access.
  match answerOf (request .staticcall 1000 0 (selectorBytes "get")) with
  | some (true, data, [.contractSlot 1000 0]) =>
      unless data == wordBytes 42 do throw (IO.userError "responder read the wrong storage")
  | _ => throw (IO.userError "in-domain static request was not answered")
  -- The callee's balance is its own account's, not the caller's.
  match answerOf (request .staticcall 1000 0 (selectorBytes "ownBalance")) with
  | some (true, data, []) =>
      unless data == wordBytes 3 do throw (IO.userError "responder read the caller's balance")
  | _ => throw (IO.userError "in-domain balance request was not answered")
  let env := environment oracle [(1000, model)] 100000
  let some adversary := env.adversary | throw (IO.userError "responder has no adversary")
  unless adversary.accepts (request .staticcall 1000 0 (selectorBytes "get")) world do
    throw (IO.userError "in-domain static request was not accepted")
  let outside : List (String × Request) := [
    ("call", request .call 1000 0 (selectorBytes "get")),
    ("value", request .staticcall 1000 1 (selectorBytes "get")),
    ("unconfigured target", request .staticcall 1001 0 (selectorBytes "get")),
    ("unknown selector", request .staticcall 1000 0 [1, 2, 3, 4]),
    ("partial word", request .staticcall 1000 0 (selectorBytes "get" ++ [0])),
    ("short calldata", request .staticcall 1000 0 [1, 2]),
    ("non-view function", request .staticcall 1000 0 (selectorBytes "set" ++ wordBytes 1)),
    ("arguments that do not bind", request .staticcall 1000 0 (selectorBytes "echo")),
    ("non-view function that only reads", request .staticcall 1000 0 (selectorBytes "peek")),
    ("read-only function that writes", request .staticcall 1000 0 (selectorBytes "viewWrites")),
    ("read-only function that logs", request .staticcall 1000 0 (selectorBytes "viewLogs")),
    ("caller target", request .staticcall 900 0 (selectorBytes "get"))]
  for (label, r) in outside do
    if (answerOf r).isSome then
      throw (IO.userError s!"out-of-domain request answered: {label}")
    if adversary.accepts r world then
      throw (IO.userError s!"out-of-domain request accepted: {label}")
  let withImmutable : CompilationModel :=
    { model with immutables := [{ name := "I", ty := .uint256, init := .literal 0 }] }
  for (models, accounts, expected) in [
      ([model], ["2"], "model responder cannot replace a reserved precompile"),
      ([model], ["900"], "model responder cannot replace caller code"),
      ([model, model], ["1000", "1000"], "duplicate model responder account"),
      ([model, model], ["1000"], "one account per responder model required"),
      ([withImmutable], ["1000"], "model responder does not supply immutable values")] do
    let input := Json.mkObj [
      ("account", toJson "900"),
      ("byteCallEnvironment", Json.mkObj [
        ("program", toJson "imported-model-static-v1"), ("gas", toJson "100000"),
        ("accounts", toJson accounts)])]
    match configure oracle models input with
    | .error message => unless message == expected do throw (IO.userError message)
    | .ok _ => throw (IO.userError s!"invalid responder configuration accepted: {expected}")
  IO.println "model responder domain checks passed"
  return 0
