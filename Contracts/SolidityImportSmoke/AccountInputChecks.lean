import Compiler.SolidityImport.CallerInput

open Lean Compiler.CompilationModel.SolidityImport.AccountsInput

def runAccountInputChecks (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected case file")
  let text ← IO.FS.readFile path
  let rows ← IO.ofExcept do
    (← Json.parse text).getArr?
  for row in rows do
    let name ← IO.ofExcept (row.getObjValAs? String "name")
    let expected ← IO.ofExcept (row.getObjValAs? Bool "accept")
    let reserved ← IO.ofExcept do
      (← (← row.getObjVal? "reserved").getArr?).toList.mapM fun value => value.getNat?
    let input ← IO.ofExcept (row.getObjVal? "accounts")
    match parseAccounts input reserved with
    | .error _ =>
      if expected then throw (IO.userError s!"valid account input rejected: {name}")
    | .ok accounts =>
      unless expected do throw (IO.userError s!"invalid account input accepted: {name}")
      let sentinel : Verity.Core.Model.Create2Accounts.Account :=
        { nonce := 19, balance := Verity.Core.Uint256.ofNat 23, code := ⟨#[0xaa]⟩ }
      let seed := { Verity.defaultState with
        creationAccounts := fun address => if address == 777 then sentinel else {}
        codeSize := fun address => if address == 777 then Verity.Core.Uint256.ofNat 1 else 0 }
      let before := (seed.writeSlot 7 (Verity.Core.Uint256.ofNat 29)).writeSlot 11 (Verity.Core.Uint256.ofNat 31)
      let world := install before accounts
      unless (world.readSlot 7).val == 29 && (world.readSlot 11).val == 31 &&
          (world.creationAccounts 777).nonce == 19 &&
          (world.creationAccounts 777).balance.val == 23 &&
          (world.creationAccounts 777).code.data == #[0xaa] && (world.codeSize 777).val == 1 do
        throw (IO.userError "initial accounts erased unrelated state")
      let raw ← IO.ofExcept input.getArr?
      unless accounts.length == raw.size do throw (IO.userError "initial accounts missing rows")
      for account in accounts do
        let found := world.creationAccounts account.address
        unless found.nonce == account.account.nonce && found.code == account.account.code &&
            found.balance == account.account.balance &&
            (world.codeSize account.address).val == account.account.code.size do
          throw (IO.userError "initial accounts changed code/nonce/balance")
      if name == "complete" then
        unless (world.creationAccounts 65536).code.size == 0 &&
            (world.creationAccounts 65536).nonce == 0 &&
            (world.creationAccounts 65537).code.data == #[0,1] &&
            (world.creationAccounts 65537).nonce == 7 &&
            (world.creationAccounts 65537).balance.val == 13 &&
            (world.creationAccounts 65538).nonce == 2^64-1 &&
            (world.creationAccounts 65538).balance.val == 2^256-1 do
          throw (IO.userError "initial account boundary values changed")
    IO.println s!"ACCOUNT_INPUT_CASE:{name}"
  IO.println s!"ACCOUNT_INPUT_SUCCESS:{rows.size} exact input/world cases"

open Lean Compiler.CompilationModel.SolidityImport

def runCallerInputChecks (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected capture receipt")
  let record ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let json ← IO.ofExcept (record.getObjVal? "json")
  let account ← IO.ofExcept (AccountsInput.parseAccount json)
  let caller ← IO.ofExcept (CallerInput.parse json account.address [123])
  let before := Verity.defaultState.writeSlot 7 (Verity.Core.Uint256.ofNat 29)
  let world := CallerInput.install before caller
  unless (world.creationAccounts caller.address).nonce == 1 &&
      (world.creationAccounts caller.address).code.data == #[0, 1] &&
      (world.creationAccounts caller.address).balance.val == 13 &&
      (world.codeSize caller.address).val == 2 && world.selfBalance.val == 13 &&
      (world.readSlot 7).val == 29 do
    throw (IO.userError "actual caller metadata changed during Lean installation")
  match CallerInput.parse json (account.address + 1) [] with
  | .ok _ => throw (IO.userError "mismatched caller target accepted")
  | .error _ => pure ()
  match CallerInput.parse json account.address [account.address] with
  | .ok _ => throw (IO.userError "caller/sender collision accepted")
  | .error _ => pure ()
  IO.println "CALLER_INPUT_SUCCESS: exact actual deployment metadata; two target/sender refusals"


def main (args : List String) : IO Unit := do
  let [accounts, caller] := args | throw (IO.userError "expected ACCOUNTS CALLER")
  runAccountInputChecks [accounts]
  runCallerInputChecks [caller]
