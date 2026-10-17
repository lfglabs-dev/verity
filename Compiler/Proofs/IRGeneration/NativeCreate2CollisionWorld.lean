import Compiler.Proofs.IRGeneration.NativeCreate2CallerFrame

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model

/-- Raw world agreement depends on actual maps, environment and substate,
not the caller's local stack, gas or instruction counters. -/
theorem agreement_frame_transport (world : Verity.ContractState) (machine next : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world machine warm)
    (maps : next.accountMap = machine.accountMap)
    (environment : next.executionEnv = machine.executionEnv)
    (substate : next.substate = machine.substate) : Agreement world next warm := by
  have views : ∀ owner, creationAccount next owner = creationAccount machine owner := by
    intro owner
    simp only [creationAccount, account, account?, maps]
  have persistent : ∀ owner slot, persistentWord next owner slot = persistentWord machine owner slot := by
    intro owner slot
    simp only [persistentWord, account, account?, maps]
  have transient : ∀ owner slot, transientWord next owner slot = transientWord machine owner slot := by
    intro owner slot
    simp only [transientWord, account, account?, maps]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [environment] using agrees.caller
  · simpa only [environment] using agrees.source
  · simpa only [environment] using agrees.origin
  · simpa only [environment] using agrees.value
  · intro owner; rw [views]; exact agrees.accounts owner
  · rw [views, environment]; exact agrees.selfBalance
  · intro owner; simpa only [account, account?, maps] using agrees.codeSizes owner
  · intro slot; rw [persistent, environment]; exact agrees.persistent slot
  · intro slot; rw [transient, environment]; exact agrees.transient slot
  · intro owner foreign slot; rw [persistent]; exact agrees.parkedPersistent owner (by simpa only [environment] using foreign) slot
  · intro owner foreign slot; rw [transient]; exact agrees.parkedTransient owner (by simpa only [environment] using foreign) slot
  · intro owner; simpa only [accountWarm, substate] using agrees.accountAccess owner

/-- Native collision warming preserves every other raw world field. -/
theorem agreement_warmed (world : Verity.ContractState) (machine : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world machine warm) (target : AccountAddress) :
    Agreement world { machine with substate := machine.substate.addAccessedAccount target }
      (Create2Access.warm warm target.val) := by
  refine { agrees with accountAccess := ?_ }
  intro owner
  exact constructor_access_projection machine warm target owner agrees.accountAccess

/-- The actual CREATE2 child collision rolls back to its nonce-bumped input.
No initcode recognizer, payload bound or hypothetical child result is assumed. -/
theorem native_create2_child_collision (fuel cost : Nat) (pre : EVM.State) (offset size salt : UInt256)
    (collision : let machine := create2ChildEntry pre cost
      let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
        (pre.memory.readWithPadding offset.toNat size.toNat)
      let account := machine.accountMap.getD target default
      (decide (account.nonce ≠ (⟨0⟩ : UInt256)) || decide (account.code.size ≠ 0)) = true) :
    let machine := create2ChildEntry pre cost
    let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
      (pre.memory.readWithPadding offset.toNat size.toNat)
    nativeCreate2Child (fuel + 3) cost pre offset size salt =
      .ok (target, pre.createdAccounts, machine.accountMap, UInt256.ofNat 0,
        pre.substate.addAccessedAccount target, false, ByteArray.empty) := by
  apply lambda_collision
  exact collision

/-- Collision completion requires no initcode payload certificate or low-gas
bound: returned gas is exactly zero, so native word addition cannot wrap. -/
theorem native_create2_collision_completed (fuel cost : Nat) (pre : EVM.State)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (collision : let machine := create2ChildEntry pre cost
      let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
        (pre.memory.readWithPadding offset.toNat size.toNat)
      let account := machine.accountMap.getD target default
      (decide (account.nonce ≠ (⟨0⟩ : UInt256)) || decide (account.code.size ≠ 0)) = true) :
    ∃ next, EVM.step (fuel + 4) cost (some (.CREATE2, none)) pre = .ok next := by
  have completed := native_create2_child_collision fuel cost pre offset size salt collision
  have guard : ¬ (pre.gasAvailable - UInt256.ofNat cost + UInt256.ofNat 0).toNat <
      EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat := by
    have zero (value : UInt256) : value + UInt256.ofNat 0 = value := by
      cases value with
      | mk value =>
        change UInt256.mk (value + 0) = UInt256.mk value
        rw [Fin.add_zero]
    rw [zero]
    exact Nat.not_lt.mpr (native_forwarded_gas_le (pre.gasAvailable - UInt256.ofNat cost))
  simp only [EVM.step]
  dsimp only [Pure.pure, Except.pure, Bind.bind, Except.bind]
  simp only [popped, nonce, if_false, entry]
  unfold nativeCreate2Child creatorBumpedMachine at completed
  simp only [Std.TreeMap.getD_eq_getD_getElem?, Std.TreeMap.get?_eq_getElem?] at completed entry ⊢
  simp only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl,
    show UInt256.ofNat 1 = (⟨1⟩ : UInt256) by rfl] at completed entry ⊢
  simp only [entry.1, and_self, if_true]
  rw [completed]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  change ¬ (pre.gasAvailable - UInt256.ofNat cost + (⟨0⟩ : UInt256)).toNat <
    EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat at guard
  simp only [guard, if_false]
  exact ⟨_, rfl⟩

/-- Actual collision completion preserves raw world agreement after the real
creator nonce bump and target warming. Persistent/transient storage is retained. -/
theorem native_create2_collision_world (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (fuel cost : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (collision : let machine := create2ChildEntry pre cost
      let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
        (pre.memory.readWithPadding offset.toNat size.toNat)
      let account := machine.accountMap.getD target default
      (decide (account.nonce ≠ (⟨0⟩ : UInt256)) || decide (account.code.size ≠ 0)) = true) :
    let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
      (pre.memory.readWithPadding offset.toNat size.toNat)
    ∃ next, EVM.step (fuel + 4) cost (some (.CREATE2, none)) pre = .ok next ∧
      Agreement (world.withCreationAccounts (Create2Accounts.bumpCreator world.creationAccounts
        pre.executionEnv.codeOwner.val)) next (Create2Access.warm warm target.val) ∧
      next.σ₀ = pre.σ₀ ∧ next.memory = pre.memory := by
  obtain ⟨next, stepped⟩ := native_create2_collision_completed fuel cost pre rest offset size salt popped nonce entry collision
  have child := native_create2_child_collision fuel cost pre offset size salt collision
  have frame := native_create2_child_frame (fuel + 3) cost pre next rest offset size salt _ popped nonce entry child stepped
  let charged := { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat cost }
  have chargedAgreement := agreement_local world pre warm agrees charged.gasAvailable pre.pc pre.stack pre.memory
  have bound : (charged.accountMap.getD pre.executionEnv.codeOwner default).nonce.toNat + 1 < UInt256.size := by
    apply creator_bump_nonce_bound
    simpa only [Std.TreeMap.getD_eq_getD_getElem?, Std.TreeMap.get?_eq_getElem?] using nonce
  have bumped := creator_bump_world_agreement world charged warm chargedAgreement pre.executionEnv.codeOwner bound
  have warmed := agreement_warmed _ _ _ bumped
    (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (pre.memory.readWithPadding offset.toNat size.toNat))
  have transported := agreement_frame_transport _ _ next _ warmed frame.1 frame.2.2.2.1 frame.2.1
  exact ⟨next, stepped, transported, frame.2.2.2.2.1, frame.2.2.2.2.2⟩

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
