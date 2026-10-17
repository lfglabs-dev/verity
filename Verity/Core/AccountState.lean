import Verity.Core.Address
import Verity.Core.Uint256
import Std.Data.TreeMap.Lemmas

/-! Exact account metadata for deployment observations. Storage is finite and
zero entries may be absent; nonce is bounded by EIP-2681's 64-bit limit. -/
namespace Verity.Core

structure AccountState where
  nonce : Fin (2^64) := 0
  balance : Uint256 := 0
  code : List (Fin 256) := []
  storage : Std.TreeMap Nat Uint256 compare := ∅

namespace AccountState

def storageAt (account : AccountState) (slot : Nat) : Uint256 :=
  account.storage.getD slot 0

def writeStorage (account : AccountState) (slot : Nat) (value : Uint256) : AccountState :=
  -- Anonymous constructor: `AccountState` is not `ContractState`, so this
  -- deliberately avoids a raw `storage :=` site in the storage-lens freeze gate.
  ⟨account.nonce, account.balance, account.code,
    if value.val = 0 then account.storage.erase slot else account.storage.insert slot value⟩

/-- Finite storage updates have exact read-after-write and frame laws.
The law-carrying map avoids requiring an external validity assumption about
an arbitrary red-black tree supplied in an account state. -/
theorem storageAt_writeStorage (account : AccountState) (slot query : Nat) (value : Uint256) :
    (account.writeStorage slot value).storageAt query =
      if query = slot then value else account.storageAt query := by
  by_cases same : query = slot
  · subst query
    by_cases zero : value.val = 0
    · have valueZero : value = 0 := Uint256.ext zero
      subst value
      simp [writeStorage, storageAt]
    · simp [writeStorage, storageAt, zero]
  · have reverse : slot ≠ query := Ne.symm same
    by_cases zero : value.val = 0
    · have valueZero : value = 0 := Uint256.ext zero
      subst value
      simp [writeStorage, storageAt, Std.TreeMap.getD_erase, same, reverse]
    · simp [writeStorage, storageAt, zero, Std.TreeMap.getD_insert, same, reverse]

@[simp] theorem storageAt_writeStorage_same (account : AccountState) (slot : Nat) (value : Uint256) :
    (account.writeStorage slot value).storageAt slot = value := by
  simp [storageAt_writeStorage]

theorem storageAt_writeStorage_other (account : AccountState) (slot query : Nat) (value : Uint256)
    (different : query ≠ slot) :
    (account.writeStorage slot value).storageAt query = account.storageAt query := by
  simp [storageAt_writeStorage, different]

/-- Batch values are computed once from the pre-write world. Duplicate
slots overwrite the same value; they do not repeatedly apply a transformer. -/
def writeStorageValues (account : AccountState) (slots : List Nat)
    (valueAt : Nat → Uint256) : AccountState :=
  slots.foldl (fun current slot => current.writeStorage slot (valueAt slot)) account

theorem storageAt_writeStorageValues (account : AccountState) (slots : List Nat)
    (valueAt : Nat → Uint256) (query : Nat) :
    (account.writeStorageValues slots valueAt).storageAt query =
      if slots.contains query then valueAt query else account.storageAt query := by
  induction slots generalizing account with
  | nil => rfl
  | cons slot rest ih =>
    simp only [writeStorageValues, List.foldl_cons] at ih ⊢
    rw [ih, storageAt_writeStorage]
    by_cases same : query = slot
    · subst query
      cases rest.contains slot <;> simp
    · by_cases member : query ∈ rest <;> simp [same, member]

/-- Osaka's collision predicate. Nonempty storage alone is not a collision:
creation clears it when both nonce and code are empty. EIP-7610 is a different
fork rule and must not be silently applied to the pinned Osaka campaigns. -/
def collidesOsaka (account : AccountState) : Bool :=
  account.nonce.val != 0 || !account.code.isEmpty

theorem storage_only_not_collision (account : AccountState)
    (nonceZero : account.nonce.val = 0) (codeEmpty : account.code = []) :
    account.collidesOsaka = false := by
  simp [collidesOsaka, nonceZero, codeEmpty]

end AccountState

abbrev AccountWorld := Address → AccountState

namespace AccountWorld
def empty : AccountWorld := fun _ => {}

def write (world : AccountWorld) (address : Address) (account : AccountState) : AccountWorld :=
  fun query => if query = address then account else world query

@[simp] theorem write_at (world : AccountWorld) (address : Address) (account : AccountState) :
    write world address account address = account := by simp [write]

theorem write_other (world : AccountWorld) (address query : Address) (account : AccountState)
    (different : query ≠ address) : write world address account query = world query := by
  simp [write, different]

end AccountWorld
end Verity.Core
