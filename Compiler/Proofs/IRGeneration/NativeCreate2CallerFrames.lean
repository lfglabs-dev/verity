import Compiler.Proofs.IRGeneration.NativeCreate2CallerMemory

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model
open Compiler.CompilationModel.DenoteMemory

/-- Fields outside the actual account/storage/returndata/memory effects.
Equality of this frame preserves all context, events, call journal, array and
known-address channels, rather than only enumerated selected observations. -/
def callerWorldFrame (world : Verity.ContractState) : Verity.ContractState :=
  { CreationStorage.frame world with byteMemory := Memory.empty, memory := fun _ => 0 }

/-- Actual canonical storage commit preserves every remaining world field. -/
theorem caller_storage_commit_frame (world committed : Verity.ContractState)
    (outcome : Create2Runtime.Outcome) (commit : CreationStorage.commit world outcome = .ok committed) :
    callerWorldFrame committed = callerWorldFrame world := by
  exact congrArg (fun frame : Verity.ContractState =>
    { frame with byteMemory := Memory.empty, memory := fun _ => 0 })
    (CreationStorage.commit_frame world outcome committed commit)

/-- Preparing actual physical memory retains the complete other-field frame. -/
theorem caller_prepared_world_frame (world : Verity.ContractState) (pre : EVM.State) (offset size : UInt256) :
    callerWorldFrame (callerPreparedWorld world pre offset size) = callerWorldFrame world := rfl

/-- Commit plus actual prepared memory preserves the original caller frame. -/
theorem caller_committed_world_frame (world committed : Verity.ContractState) (pre : EVM.State)
    (offset size : UInt256) (outcome : Create2Runtime.Outcome)
    (commit : CreationStorage.commit (callerPreparedWorld world pre offset size) outcome = .ok committed) :
    callerWorldFrame committed = callerWorldFrame world :=
  (caller_storage_commit_frame _ _ _ commit).trans (caller_prepared_world_frame world pre offset size)

/-- Every caller or foreign channel outside the new target's parked persistent
namespace survives either actual constructor outcome, including typed mappings. -/
theorem caller_constructor_storage_frame (world : Verity.ContractState)
    (before reserved : Create2Accounts.Accounts) (sender target : AccountAddress) (payload : ByteArray)
    (flag : Bool) (committed : Verity.ContractState)
    (commit : CreationStorage.commit world (constructorOutcome before reserved sender target payload flag) = .ok committed)
    (key : Verity.StorageKey) (outside : CreationStorage.ownsPersistent target.val key = false) :
    committed.storageWords key = world.storageWords key := by
  have actual := constructor_outcome_commit world before reserved sender target payload flag
  have same : committed = constructorCommitWorld world
      (constructorOutcome before reserved sender target payload flag).accounts target payload flag :=
    Except.ok.inj (commit.symm.trans actual)
  rw [same]
  cases flag
  · rfl
  · change (if CreationStorage.ownsPersistent target.val key then 0 else world.storageWords key) = _
    rw [outside]
    rfl

/-- Preserve an existing typed-to-physical slot relation through either actual
constructor outcome. No mapping-hash injectivity or layout approximation is used. -/
theorem caller_constructor_typed_coherence (world committed : Verity.ContractState)
    (before reserved : Create2Accounts.Accounts) (sender target : AccountAddress) (payload : ByteArray)
    (flag : Bool) (key : Verity.StorageKey) (slot : UInt256)
    (commit : CreationStorage.commit world (constructorOutcome before reserved sender target payload flag) = .ok committed)
    (outside : CreationStorage.ownsPersistent target.val key = false)
    (coherent : world.storageWords key = world.readSlot slot.toNat) :
    committed.storageWords key = committed.readSlot slot.toNat := by
  have typed := caller_constructor_storage_frame world before reserved sender target payload flag committed commit key outside
  have physical := caller_constructor_storage_frame world before reserved sender target payload flag committed commit
    (.slot slot.toNat) rfl
  change committed.readSlot slot.toNat = world.readSlot slot.toNat at physical
  exact typed.trans (coherent.trans physical.symm)

/-- Typed channels already coherent with actual Solidity locations remain
related to the final native storage at every tracked key. The layout is retained,
not guessed or replaced after execution. -/
theorem caller_constructor_typed_native (world committed : Verity.ContractState) (next : EVM.State)
    (before reserved : Create2Accounts.Accounts) (sender target : AccountAddress) (payload : ByteArray)
    (flag : Bool) (tracked : List Verity.StorageKey) (location : Verity.StorageKey → UInt256)
    (commit : CreationStorage.commit world (constructorOutcome before reserved sender target payload flag) = .ok committed)
    (outside : ∀ key ∈ tracked, CreationStorage.ownsPersistent target.val key = false)
    (coherent : ∀ key ∈ tracked, world.storageWords key = world.readSlot (location key).toNat)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement committed next warm) :
    ∀ key ∈ tracked, committed.storageWords key = persistentWord next next.executionEnv.codeOwner (location key) := by
  intro key member
  exact (caller_constructor_typed_coherence world committed before reserved sender target payload flag key
    (location key) commit (outside key member) (coherent key member)).trans (agrees.persistent (location key))

/-- The actual constructor changes only accessed accounts in the native
substate. Logs, refund, accessed storage and destruction bookkeeping survive. -/
theorem native_create2_child_substate (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (pre : EVM.State) (cost : Nat) (offset size salt : UInt256)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0)
    (fuel : Nat) (enough : 10 ≤ fuel)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result) :
    result.2.2.2.2.1 = pre.substate.addAccessedAccount
      (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)) := by
  have formula := completed
  unfold nativeCreate2Child at formula
  dsimp only at formula
  rw [code] at formula
  rw [lambda_constructor payload bounded] at formula
  · exact (lambda_result_bookkeeping payload _ _ _ _ _ _ _ result formula).2.2.1
  · exact vacant
  · exact enough

/-- Full native parent substate frame for the same actual child invocation. -/
theorem native_create2_parent_substate (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (pre next : EVM.State) (cost fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0)
    (enough : 10 ≤ fuel) (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (child : nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result)
    (stepped : EVM.step (fuel + 3) cost (some (.CREATE2, none)) pre = .ok next) :
    { next.substate with accessedAccounts := pre.substate.accessedAccounts } = pre.substate := by
  have frame := native_create2_child_frame (fuel + 2) cost pre next rest offset size salt result popped nonce entry child stepped
  rw [frame.2.1, native_create2_child_substate payload bounded pre cost offset size salt code vacant fuel enough result child]
  exact constructor_substate_frame _ _

/-- Remaining frame obligations, including all surviving typed storage words. -/
structure CallerFrameAgreement (before after : Verity.ContractState) (initial final : Substate)
    (target : AccountAddress) : Prop where
  world : callerWorldFrame after = callerWorldFrame before
  substate : { final with accessedAccounts := initial.accessedAccounts } = initial
  storage : ∀ key, CreationStorage.ownsPersistent target.val key = false → after.storageWords key = before.storageWords key

/-- Compute all remaining frames from the actual child, parent and commit. -/
theorem native_create2_committed_frames (world committed : Verity.ContractState) (pre next : EVM.State)
    (payload : ByteArray) (bounded : payload.size ≤ 49152) (cost fuel : Nat)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0)
    (enough : 10 ≤ fuel) (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (child : nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result)
    (stepped : EVM.step (fuel + 3) cost (some (.CREATE2, none)) pre = .ok next)
    (before reserved : Create2Accounts.Accounts)
    (commit : CreationStorage.commit (callerPreparedWorld world pre offset size)
      (constructorOutcome before reserved pre.executionEnv.codeOwner
        (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload))
        payload result.2.2.2.2.2.1) = .ok committed) :
    CallerFrameAgreement world committed pre.substate next.substate
      (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)) := by
  refine ⟨caller_committed_world_frame world committed pre offset size _ commit,
    native_create2_parent_substate payload bounded pre next cost fuel rest offset size salt code vacant
      enough popped nonce entry result child stepped, ?_⟩
  intro key outside
  exact caller_constructor_storage_frame _ before reserved pre.executionEnv.codeOwner _ payload _ committed commit key outside

/-- The returned frame certificate and raw final agreement transport every
initially coherent tracked typed channel to its actual final native slot. -/
theorem caller_frame_typed_native (world committed : Verity.ContractState) (next : EVM.State)
    (initial final : Substate) (target : AccountAddress)
    (frames : CallerFrameAgreement world committed initial final target)
    (tracked : List Verity.StorageKey) (location : Verity.StorageKey → UInt256)
    (outside : ∀ key ∈ tracked, CreationStorage.ownsPersistent target.val key = false)
    (coherent : ∀ key ∈ tracked, world.storageWords key = world.readSlot (location key).toNat)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement committed next warm) :
    ∀ key ∈ tracked, committed.storageWords key = persistentWord next next.executionEnv.codeOwner (location key) := by
  intro key member
  have typed := frames.storage key (outside key member)
  have physical := frames.storage (.slot (location key).toNat) rfl
  change committed.readSlot (location key).toNat = world.readSlot (location key).toNat at physical
  exact typed.trans ((coherent key member).trans (physical.symm.trans (agrees.persistent (location key))))

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
