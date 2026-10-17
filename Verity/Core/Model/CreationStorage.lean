import Verity.Core.Model.CreationCommit

/-! Persistent storage reset for a distinct newly created account. This is the
parked physical/typed-word namespace; plain caller words, transient storage and
global array metadata are not a target account's parked persistent store. -/
namespace Verity.Core.Model.CreationStorage
open Verity Create2Runtime

def persistentChannel : StorageKey → Bool
  | .addr _ | .map _ _ | .mapUint _ _ | .map2 _ _ _ | .mapChain _ _ _ => true
  | _ => false

def ownsPersistent (target : Nat) : StorageKey → Bool
  | .contractSlot owner _ => owner == target
  | .scoped owner key => owner == target && persistentChannel key
  | _ => false

/-- Reset the target's parked persistent words only; this helper neither
reserves accounts nor executes initcode. -/
def clear (world : ContractState) (target : Nat) : ContractState :=
  world.withStorageWords fun key => if ownsPersistent target key then 0 else world.storageWords key

theorem clear_target_slot (world : ContractState) (target slot : Nat) :
    (clear world target).storageWords (.contractSlot target slot) = 0 := by
  simp [clear, ownsPersistent, ContractState.withStorageWords]

theorem clear_target_channel (world : ContractState) (target : Nat) (key : StorageKey)
    (persistent : persistentChannel key = true) :
    (clear world target).storageWords (.scoped target key) = 0 := by
  simp [clear, ownsPersistent, persistent, ContractState.withStorageWords]

theorem clear_other_slot (world : ContractState) (target owner slot : Nat)
    (other : owner ≠ target) :
    (clear world target).storageWords (.contractSlot owner slot) =
      world.storageWords (.contractSlot owner slot) := by
  simp [clear, ownsPersistent, other, ContractState.withStorageWords]

theorem clear_other_channel (world : ContractState) (target owner : Nat) (key : StorageKey)
    (other : owner ≠ target) :
    (clear world target).storageWords (.scoped owner key) = world.storageWords (.scoped owner key) := by
  simp [clear, ownsPersistent, other, ContractState.withStorageWords]

theorem clear_plain_slot (world : ContractState) (target slot : Nat) :
    (clear world target).readSlot slot = world.readSlot slot := rfl

theorem clear_transient (world : ContractState) (target slot : Nat) :
    (clear world target).transientStorage slot = world.transientStorage slot := rfl

theorem clear_parked_transient (world : ContractState) (target owner slot : Nat) :
    (clear world target).storageWords (.scoped owner (.transient slot)) =
      world.storageWords (.scoped owner (.transient slot)) := by
  simp [clear, ownsPersistent, persistentChannel, ContractState.withStorageWords]

theorem clear_parked_transient_map (world : ContractState) (target owner slot : Nat) (keys : List Nat) :
    (clear world target).storageWords (.scoped owner (.transientMapChain slot keys)) =
      world.storageWords (.scoped owner (.transientMapChain slot keys)) := by
  simp [clear, ownsPersistent, persistentChannel, ContractState.withStorageWords]

/-- Complete frame: only the storage-word carrier changes. -/
theorem clear_frame (world : ContractState) (target : Nat) :
    (clear world target).withStorageWords (fun _ => 0) = world.withStorageWords (fun _ => 0) := rfl

def clearOnSuccess (world : ContractState) : Outcome → ContractState
  | .created target _ => clear world target
  | .failed _ _ => world

def commit (world : ContractState) (result : Outcome) : Except String ContractState :=
  CreationCommit.commit (clearOnSuccess world result) result

def frame (world : ContractState) : ContractState :=
  (CreationCommit.frame world).withStorageWords (fun _ => 0)

theorem commit_failed_empty (world : ContractState) (accounts : Create2Accounts.Accounts) :
    commit world (.failed accounts ByteArray.empty) =
      .ok { world with creationAccounts := accounts, returndata := [] } := by
  exact CreationCommit.commit_failed_empty world accounts

theorem commit_failed_nonempty (world : ContractState) (accounts : Create2Accounts.Accounts)
    (data : ByteArray) (nonempty : data.size ≠ 0) :
    commit world (.failed accounts data) =
      .error "CREATE2 constructor revert requires the exact byte-returndata interpreter" := by
  exact CreationCommit.commit_failed_nonempty world accounts data nonempty

theorem commit_created_storage (world : ContractState) (target : Nat)
    (accounts : Create2Accounts.Accounts) (next : ContractState)
    (committed : commit world (.created target accounts) = .ok next) (key : StorageKey) :
    next.storageWords key = if ownsPersistent target key then 0 else world.storageWords key := by
  simp only [commit, clearOnSuccess, CreationCommit.commit, Except.ok.injEq] at committed
  cases committed
  rfl

theorem commit_created_codeSize (world : ContractState) (target : Nat)
    (accounts : Create2Accounts.Accounts) (next : ContractState)
    (committed : commit world (.created target accounts) = .ok next) :
    next.codeSize target = Uint256.ofNat (accounts target).code.size := by
  exact CreationCommit.commit_created_codeSize (clear world target) target accounts next committed

theorem commit_accounts (world : ContractState) (result : Outcome) (next : ContractState)
    (committed : commit world result = .ok next) : next.creationAccounts = result.accounts := by
  exact CreationCommit.commit_accounts (clearOnSuccess world result) result next committed

theorem commit_frame (world : ContractState) (result : Outcome) (next : ContractState)
    (committed : commit world result = .ok next) : frame next = frame world := by
  have accountFrame := CreationCommit.commit_frame (clearOnSuccess world result) result next committed
  have full := congrArg (fun s : ContractState => s.withStorageWords (fun _ => 0)) accountFrame
  cases result <;> exact full

end Verity.Core.Model.CreationStorage
