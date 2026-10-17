import Verity.Core.Model.DenoteCreate2
import Compiler.SolidityImport.Transactions
import Compiler.Keccak.Sponge
import Lean.Data.Json

/-! Executable account-world calibration bridge. This models the fixture's
success/rollback continuation, not its ABI/event encoding or a compiled route. -/
namespace SolidityImportSmoke.DeploymentWorldDriver
open Lean Verity.Core
open Compiler.CompilationModel.DenoteCreate2
open Compiler.CompilationModel.DenoteMemory
open Compiler.CompilationModel.SolidityImport.Transactions

private def quantity (j : Json) : Except String Nat := do
  let value ← j.getStr?
  let some n := value.toNat? | throw "expected decimal account quantity"
  pure n

private def word (j : Json) : Except String Uint256 := do
  let n ← quantity j
  unless n < Uint256.modulus do throw "account word exceeds uint256"
  pure (Uint256.ofNat n)

private def address (j : Json) : Except String Address := do
  let n ← quantity j
  if h : n < Address.modulus then pure ⟨n, h⟩ else throw "account address exceeds 160 bits"

private def bytes (j : Json) : Except String (List Byte) := do
  (← j.getArr?).toList.mapM fun value => do
    let n ← value.getNat?
    if h : n < 256 then pure ⟨n, h⟩ else throw "account code byte exceeds 255"

private def account (j : Json) : Except String (Address × AccountState) := do
  let addr ← address (← j.getObjVal? "address")
  let n ← quantity (← j.getObjVal? "nonce")
  if h : n < 2^64 then
    let balance ← word (← j.getObjVal? "balance")
    let code ← bytes (← j.getObjVal? "code")
    let mut value : AccountState := { nonce := ⟨n, h⟩, balance, code }
    for pair in (← (← j.getObjVal? "storage").getArr?).toList do
      let entry ← pair.getArr?
      unless entry.size == 2 do throw "storage requires slot and value"
      let slot ← word entry[0]!
      let stored ← word entry[1]!
      value := value.writeStorage slot.val stored
    pure (addr, value)
  else throw "account nonce exceeds EIP-2681 bound"

private def hash (input : List Byte) : Uint256 :=
  let encoded : ByteArray := ⟨(input.map fun byte => UInt8.ofNat byte.val).toArray⟩
  Uint256.ofNat (KeccakEngine.byteArrayToNatBE (KeccakEngine.keccak256 encoded))

private def observe (world : Verity.ContractState) (j : Json) : Except String Json := do
  let addr ← address (← j.getObjVal? "address")
  let value := world.accountWorld addr
  let mut storageRows : Array Json := #[]
  for slot in (← (← j.getObjVal? "slots").getArr?).toList do
    let n ← word slot
    storageRows := storageRows.push (.arr #[.str (toString n.val), .str (toString (value.storageAt n.val).val)])
  pure (Json.mkObj [("address", .str (toString addr.val)), ("nonce", .str (toString value.nonce.val)),
    ("balance", .str (toString value.balance.val)),
    ("code", .arr (value.code.map (fun byte => toJson byte.val)).toArray), ("storage", .arr storageRows)])

def execute (input : Json) : Except String Json := do
  let creator ← address (← input.getObjVal? "creator")
  let initial ← (← (← input.getObjVal? "initialAccounts").getArr?).toList.mapM account
  let addresses := initial.map (·.1)
  unless addresses.eraseDups.length == addresses.length do throw "duplicate initial account"
  let ledger : AccountWorld := fun addr => ((initial.find? (fun pair => pair.1 == addr)).map (·.2)).getD {}
  let mut world : Verity.ContractState :=
    { Verity.defaultState with
      thisAddress := creator
      accountWorld := ledger
      selfBalance := (ledger creator).balance
      codeSize := fun raw => Uint256.ofNat (ledger (Address.ofNat raw)).code.length }
  let mut results : Array Json := #[]
  for row in (← (← input.getObjVal? "steps").getArr?).toList do
    let id ← (← row.getObjVal? "id").getStr?
    let value ← word (← row.getObjVal? "value")
    let childGas ← quantity (← row.getObjVal? "childGas")
    let salt ← word (← row.getObjVal? "salt")
    let code ← bytes (← row.getObjVal? "code")
    let failAfter ← (← row.getObjVal? "failAfter").getBool?
    let requireSuccess ← (← row.getObjVal? "requireSuccess").getBool?
    let snapshot := world
    let created ← denoteCreate2 hash world { creator, value, childGas } salt code
    let (operator, target, rejected) := match created.control with
      | .success addr => ("success", addr.toNat, failAfter)
      | .zero _ => ("zero", 0, requireSuccess || failAfter)
      | .abort _ => ("abort", 0, true)
    if rejected then
      let rolledBack ← finishFrame snapshot (.revertWithData [])
      world := rolledBack.world
    else world := created.world
    let observations ← (← (← row.getObjVal? "observations").getArr?).toList.mapM (observe world)
    results := results.push (Json.mkObj [("id", .str id), ("operator", .str operator),
      ("address", .str (toString target)), ("status", .str (if rejected then "revert" else "ok")),
      ("childGasLeft", .str (toString created.childGasLeft)), ("accounts", .arr observations.toArray)])
  pure (.arr results)

end SolidityImportSmoke.DeploymentWorldDriver

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile input))
      let result ← IO.ofExcept (SolidityImportSmoke.DeploymentWorldDriver.execute parsed)
      IO.FS.writeFile output (result.compress ++ "\n")
      pure 0
  | _ => throw (IO.userError "expected deployment-world input and output JSON paths")
