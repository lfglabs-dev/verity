import Compiler.SolidityImport.SequenceRunner

namespace SolidityImportSmoke.SelectorIdentityChecks

open Lean Compiler.CompilationModel
open Compiler.CompilationModel.SolidityImport

private def model : CompilationModel :=
  { name := "SelectorChecks", fields := [], constructor := none
    functions := [
      { name := "transfer", params := [{ name := "to", ty := .address },
          { name := "amount", ty := .uint256 }], returnType := none, body := [.stop] },
      { name := "approve", params := [{ name := "to", ty := .address },
          { name := "amount", ty := .uint256 }], returnType := none, body := [.stop] }] }

private def input (name : String) (selector : Nat) : Json := Json.mkObj [
  ("account", toJson "1"), ("storage", toJson (#[] : Array Json)),
  ("transactions", Json.arr #[Json.mkObj [
    ("id", toJson "0"), ("function", toJson name),
    ("args", toJson ["2", "7"]), ("selector", toJson (toString selector)),
    ("sender", toJson "2"), ("target", toJson "1"), ("value", toJson "0"),
    ("timestamp", toJson "100"), ("blockNumber", toJson "1"),
    ("observe", toJson (#[] : Array Json))]])]

private def oracle : Denote.DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩

private def rejects (m : CompilationModel) (j : Json) (expected : String) : IO Unit := do
  match SequenceRunner.execute m oracle j with
  | .error actual => unless actual == expected do
      throw (IO.userError s!"wrong rejection: {actual}")
  | .ok _ => throw (IO.userError "invalid selector/function identity accepted")

private def accepts (m : CompilationModel) (name : String) (selector : Nat) : IO Unit := do
  let rows ← IO.ofExcept (SequenceRunner.execute m oracle (input name selector))
  let expected := Json.arr #[Json.mkObj [
    ("id", toJson "0"), ("status", toJson "ok"), ("data", toJson "0x"),
    ("touched", Json.arr #[]), ("storage", Json.arr #[]), ("events", Json.arr #[])]]
  unless rows == expected do
    throw (IO.userError s!"canonical selector observation differs: {rows.compress}")

def check : IO Unit := do
  -- Independent standard ERC20 vectors; do not compute expected selectors with
  -- the same function under test.
  accepts model "transfer" 0xa9059cbb
  accepts model "approve" 0x095ea7b3
  rejects model (input "transfer" 0x095ea7b3)
    "source calldata selector differs from model function"
  rejects model (input "transfer" 0)
    "source calldata selector does not resolve to a model function"
  rejects model (input "transfer" (2^32 + 0xa9059cbb))
    "model selector exceeds four bytes"
  let hidden := { model with functions := model.functions.map fun fn => { fn with isInternal := true } }
  rejects hidden (input "transfer" 0xa9059cbb)
    "model function must resolve uniquely: transfer"
  let duplicate := { model with functions := model.functions ++ model.functions }
  rejects duplicate (input "transfer" 0xa9059cbb) "ambiguous model function selectors"
  -- Identical internal signatures must not make the external dispatch ambiguous.
  let withInternal := { model with functions := model.functions ++ hidden.functions }
  accepts withInternal "transfer" 0xa9059cbb
  for name in ["fallback", "receive"] do
    let special := { model with functions := model.functions ++ [
      { name := name, params := [], returnType := none, body := [.stop] }] }
    accepts special "transfer" 0xa9059cbb
    rejects special (input name 0) s!"model function must resolve uniquely: {name}"
  IO.println "selector identity checks passed"

end SolidityImportSmoke.SelectorIdentityChecks

def main : IO Unit := SolidityImportSmoke.SelectorIdentityChecks.check
