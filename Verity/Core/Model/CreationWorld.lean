import Verity.Core

namespace Verity.ContractState

/-- Install an explicit creation-account projection, leaving all other world
observations unchanged. Runtime code installation still has to update the
code-size observation consistently in the eventual opcode evaluator. -/
def withCreationAccounts (world : ContractState)
    (accounts : Core.Model.Create2Accounts.Accounts) : ContractState :=
  { world with creationAccounts := accounts }

/-- Erase only the account projection, retaining the entire remaining world. -/
def creationFrame (world : ContractState) : ContractState :=
  world.withCreationAccounts (fun _ => {})

@[simp] theorem withCreationAccounts_accounts (world : ContractState)
    (accounts : Core.Model.Create2Accounts.Accounts) :
    (world.withCreationAccounts accounts).creationAccounts = accounts := rfl

@[simp] theorem withCreationAccounts_identity (world : ContractState) :
    world.withCreationAccounts world.creationAccounts = world := rfl

@[simp] theorem withCreationAccounts_frame (world : ContractState)
    (accounts : Core.Model.Create2Accounts.Accounts) :
    (world.withCreationAccounts accounts).creationFrame = world.creationFrame := rfl

@[simp] theorem withCreationAccounts_storageWords (world : ContractState)
    (accounts : Core.Model.Create2Accounts.Accounts) :
    (world.withCreationAccounts accounts).storageWords = world.storageWords := rfl

@[simp] theorem withCreationAccounts_storageArray (world : ContractState)
    (accounts : Core.Model.Create2Accounts.Accounts) :
    (world.withCreationAccounts accounts).storageArray = world.storageArray := rfl

@[simp] theorem withCreationAccounts_readSlot (world : ContractState)
    (accounts : Core.Model.Create2Accounts.Accounts) (slot : Nat) :
    (world.withCreationAccounts accounts).readSlot slot = world.readSlot slot := rfl

@[simp] theorem writeSlot_creationAccounts (world : ContractState)
    (slot : Nat) (value : Uint256) :
    (world.writeSlot slot value).creationAccounts = world.creationAccounts := rfl

end Verity.ContractState
