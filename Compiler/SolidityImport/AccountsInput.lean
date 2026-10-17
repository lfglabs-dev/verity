import Compiler.CompilationModel
import Verity.Core
import Lean.Data.Json

/-! Exact initial external-account input. No caller gas/context is supplied
and no creation or external-call support is admitted by this adapter. -/
namespace Compiler.CompilationModel.SolidityImport.AccountsInput
open Lean Verity.Core

structure InputAccount where
  address : Nat
  account : Verity.Core.Model.Create2Accounts.Account

private def decimal (json : Json) (bound : Nat) : Except String Nat := do
  let text ← json.getStr?
  let some value := text.toNat? | throw "expected decimal initial account word"
  unless text == toString value && value < bound do
    throw "noncanonical or out-of-range initial account word"
  return value

/-- Python sends code as byte values, preserving leading zeroes. All four
account fields are mandatory, even for empty-code nonce-only collisions. -/
def parseAccount (json : Json) : Except String InputAccount := do
  let fields ← json.getObj?
  unless fields.size == 4 do throw "initial account requires exactly four fields"
  let address ← decimal (← json.getObjVal? "address") (2^160)
  let nonce ← decimal (← json.getObjVal? "nonce") (2^64)
  let balance ← decimal (← json.getObjVal? "balance") (2^256)
  let code ← (← (← json.getObjVal? "code").getArr?).mapM fun byte => do
    return UInt8.ofNat (← decimal byte 256)
  return { address, account := { nonce, balance := Uint256.ofNat balance, code := ⟨code⟩ } }

def parseAccounts (json : Json) (reserved : List Nat) : Except String (List InputAccount) := do
  let accounts ← (← json.getArr?).toList.mapM parseAccount
  let addresses := accounts.map (·.address)
  unless addresses.eraseDups.length == addresses.length do throw "duplicate initial account"
  unless addresses.all (fun address => !reserved.contains address) do
    throw "initial account would overwrite a deployed fixture or sender"
  return accounts

/-- The same explicit code drives the EVM code-size view and creation-account
projection. Untouched accounts and all storage/memory/events remain unchanged. -/
def installOne (world : Verity.ContractState) (input : InputAccount) : Verity.ContractState :=
  { world with
    creationAccounts := fun address => if address == input.address then input.account else world.creationAccounts address
    codeSize := fun address => if address == input.address then Uint256.ofNat input.account.code.size else world.codeSize address }

def install (world : Verity.ContractState) (accounts : List InputAccount) : Verity.ContractState :=
  accounts.foldl installOne world

end Compiler.CompilationModel.SolidityImport.AccountsInput

namespace Compiler.CompilationModel.SolidityImport.AccountsInput

theorem install_storage (world : Verity.ContractState) (accounts : List InputAccount) :
    (install world accounts).storageWords = world.storageWords := by
  induction accounts generalizing world with
  | nil => rfl
  | cons account rest ih => exact ih (installOne world account)

theorem install_memory (world : Verity.ContractState) (accounts : List InputAccount) :
    (install world accounts).byteMemory = world.byteMemory := by
  induction accounts generalizing world with
  | nil => rfl
  | cons account rest ih => exact ih (installOne world account)

theorem install_events (world : Verity.ContractState) (accounts : List InputAccount) :
    (install world accounts).events = world.events := by
  induction accounts generalizing world with
  | nil => rfl
  | cons account rest ih => exact ih (installOne world account)

theorem install_account_frame (world : Verity.ContractState) (accounts : List InputAccount)
    (query : Nat) (outside : ∀ account ∈ accounts, query ≠ account.address) :
    (install world accounts).creationAccounts query = world.creationAccounts query := by
  induction accounts generalizing world with
  | nil => rfl
  | cons account rest ih =>
    have different := outside account (List.mem_cons_self ..)
    have remaining : ∀ member ∈ rest, query ≠ member.address :=
      fun member belongs => outside member (List.mem_cons_of_mem _ belongs)
    change (install (installOne world account) rest).creationAccounts query = _
    rw [ih (installOne world account) remaining]
    simp only [installOne, different, beq_iff_eq, ↓reduceIte]

end Compiler.CompilationModel.SolidityImport.AccountsInput
