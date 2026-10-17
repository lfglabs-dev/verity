import Compiler.SolidityImport.StaticOracleMocks

open Lean Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport.StaticOracleMocks

private def oracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩

private def checkTarget (target : Nat) : IO Unit := do
  let env := environment [1000] 100000 [119]
  let world : Verity.ContractState := { Verity.defaultState with
    thisAddress := Verity.Core.Address.ofNat 900
    storageWords := fun key => Verity.Core.Uint256.ofNat
      (if key == Verity.StorageKey.contractSlot 1000 0 then 42 else
       if key == Verity.StorageKey.contractSlot 1000 2 then 32 else 0) }
  let state : DenoteState :=
    { world := world.writePhysicalMemoryValue 64 128
      bindings := []
      byteCallAdversary := env.adversary
      byteCallGas := env.gas }
  let result := executeByteStaticCall oracle [] state
    (Compiler.ECM.SolidityStaticCall.uint256Module "out" 0xa035b1fe 0)
    "out" 0xa035b1fe 0 [.literal target]
  if target == 1000 then
    match result with
    | .ok (.continue next, _) =>
        unless lookupValue next.bindings "out" == 42 do
          throw (IO.userError "configured oracle response differs")
    | _ => throw (IO.userError "configured oracle request rejected")
  else if target == 119 then
    match result with
    | .ok (.revertWithData [], []) => pure ()
    | _ => throw (IO.userError "explicit empty-code target differs")
  else
    match result with
    | .error "byte call request outside adversary domain" => pure ()
    | _ => throw (IO.userError "unmodeled mock target fabricated an EVM response")

def main (args : List String) : IO UInt32 := do
  let targets ← args.mapM fun text => do
    let some target := text.toNat? | throw (IO.userError "invalid target")
    return target
  unless !targets.isEmpty do throw (IO.userError "expected target matrix")
  targets.forM checkTarget
  for (accounts, emptyAccounts, expected) in [
      (["2"], ["119"], "oracle mock cannot replace a reserved precompile"),
      (["1000"], ["2"], "empty mock account is a reserved precompile"),
      (["1000"], ["1000"], "mock code and empty accounts overlap"),
      (["1000"], ["900"], "empty mock account cannot replace caller code")] do
    let input := Json.mkObj [
      ("account", toJson "900"),
      ("byteCallEnvironment", Json.mkObj [
        ("program", toJson "raw-static-oracle-v1"), ("gas", toJson "100000"),
        ("accounts", toJson accounts), ("emptyAccounts", toJson emptyAccounts)])]
    match configure input with
    | .error message => unless message == expected do throw (IO.userError message)
    | .ok _ => throw (IO.userError "invalid mock code deployment accepted")
  IO.println "oracle request domain checks passed"
  return 0
