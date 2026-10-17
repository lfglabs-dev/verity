import Compiler.Proofs.IRGeneration.NativeConstructorCreatorBump

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model.Create2Accounts

/-- The actual native creator nonce map insertion, retaining parent fields. -/
def creatorBumpedMachine (machine : EVM.State) (sender : AccountAddress) : EVM.State :=
  { machine with accountMap := (machine.accountMap.insert sender
    { (machine.accountMap.getD sender default) with
      nonce := (machine.accountMap.getD sender default).nonce + UInt256.ofNat 1 }) }

/-- The actual native nonce guard implies the arithmetic bound needed by the
canonical projection; no independent gas/nonce certificate is substituted. -/
theorem creator_bump_nonce_bound (nonce : UInt256) (guard : ¬ nonce.toNat ≥ 2^64 - 1) :
    nonce.toNat + 1 < UInt256.size := by
  have wide : 2^64 < UInt256.size := by decide
  omega

/-- Native CREATE2 inserts the creator before Lambda, so child entry has a
real present account even if the original lookup used the default account. -/
theorem creator_bump_present (machine : EVM.State) (sender : AccountAddress) :
    (creatorBumpedMachine machine sender).accountMap.get? sender = some
      { (machine.accountMap.getD sender default) with
        nonce := (machine.accountMap.getD sender default).nonce + UInt256.ofNat 1 } := by
  unfold creatorBumpedMachine
  exact Std.TreeMap.getElem?_insert_self

private theorem creator_bump_account (machine : EVM.State) (sender query : AccountAddress) :
    account (creatorBumpedMachine machine sender) query =
      if query = sender then { account machine query with nonce := (account machine query).nonce + UInt256.ofNat 1 }
      else account machine query := by
  unfold creatorBumpedMachine account account?
  simp only [Std.TreeMap.get?_eq_getElem?, ← Std.TreeMap.getD_eq_getD_getElem?]
  by_cases same : query = sender
  · subst query
    rw [Std.TreeMap.getD_insert_self, if_pos rfl]
  · have distinct : compare sender query ≠ Ordering.eq := by
      intro equal
      exact same (Std.LawfulEqOrd.eq_of_compare equal).symm
    rw [Std.TreeMap.getD_insert, if_neg distinct, if_neg same]

/-- The nonce insertion preserves code, balance and both entire storage maps,
including absent creators viewed through the native default-account API. -/
theorem creator_bump_account_frame (machine : EVM.State) (sender query : AccountAddress) :
    let next := account (creatorBumpedMachine machine sender) query
    let old := account machine query
    next.code = old.code ∧ next.balance = old.balance ∧ next.storage = old.storage ∧ next.tstorage = old.tstorage := by
  rw [creator_bump_account]
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem creator_bump_persistent (machine : EVM.State) (sender query : AccountAddress) (slot : UInt256) :
    persistentWord (creatorBumpedMachine machine sender) query slot = persistentWord machine query slot := by
  unfold persistentWord
  rw [(creator_bump_account_frame machine sender query).2.2.1]

private theorem creator_bump_transient (machine : EVM.State) (sender query : AccountAddress) (slot : UInt256) :
    transientWord (creatorBumpedMachine machine sender) query slot = transientWord machine query slot := by
  unfold transientWord
  rw [(creator_bump_account_frame machine sender query).2.2.2]

/-- All raw world fields survive the actual nonce insertion, while the account
projection changes by canonical bumpCreator. No storage snapshot is replaced. -/
theorem creator_bump_world_agreement (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (agrees : Agreement world machine warm)
    (sender : AccountAddress)
    (bounded : (machine.accountMap.getD sender default).nonce.toNat + 1 < UInt256.size) :
    Agreement (world.withCreationAccounts (bumpCreator world.creationAccounts sender.val))
      (creatorBumpedMachine machine sender) warm := by
  refine ⟨agrees.caller, agrees.source, agrees.origin, agrees.value, ?_, ?_, ?_, ?_, ?_, ?_, ?_, agrees.accountAccess⟩
  · intro owner
    exact constructor_creator_bump machine world.creationAccounts sender owner bounded agrees.accounts
  · change world.selfBalance = (creationAccount (creatorBumpedMachine machine sender) machine.executionEnv.codeOwner).balance
    unfold creationAccount
    rw [(creator_bump_account_frame machine sender machine.executionEnv.codeOwner).2.1]
    exact agrees.selfBalance
  · intro owner
    rw [(creator_bump_account_frame machine sender owner).1]
    exact agrees.codeSizes owner
  · intro slot
    rw [creator_bump_persistent]
    exact agrees.persistent slot
  · intro slot
    rw [creator_bump_transient]
    exact agrees.transient slot
  · intro owner foreign slot
    rw [creator_bump_persistent]
    exact agrees.parkedPersistent owner foreign slot
  · intro owner foreign slot
    rw [creator_bump_transient]
    exact agrees.parkedTransient owner foreign slot

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
