import Compiler.Proofs.IRGeneration.NativeCreate2CollisionWorld

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model

private theorem native_nonce_zero (nonce : UInt256) (zero : nonce.toNat = 0) :
    nonce = (⟨0⟩ : UInt256) := by
  cases nonce with
  | mk value =>
    congr 1
    apply Fin.ext
    exact zero

/-- Actual native collision occupancy agrees with the canonical account view. -/
theorem native_collision_occupied (machine : EVM.State) (target : AccountAddress)
    (collision : let account := machine.accountMap.getD target default
      (decide (account.nonce ≠ (⟨0⟩ : UInt256)) || decide (account.code.size ≠ 0)) = true) :
    Create2Accounts.occupied (creationAccount machine target) = true := by
  cases occupied : Create2Accounts.occupied (creationAccount machine target) with
  | true => rfl
  | false =>
    have vacant := occupied
    simp only [Create2Accounts.occupied, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at vacant
    have nonce : (machine.accountMap.getD target default).nonce = (⟨0⟩ : UInt256) := by
      apply native_nonce_zero
      simpa only [creationAccount, account, account?, Std.TreeMap.getD_eq_getD_getElem?,
        Std.TreeMap.get?_eq_getElem?] using vacant.1
    have code : (machine.accountMap.getD target default).code.size = 0 := by
      simpa only [creationAccount, account, account?, Std.TreeMap.getD_eq_getD_getElem?,
        Std.TreeMap.get?_eq_getElem?] using vacant.2
    simp only [nonce, code, ne_self_iff_false, decide_false, Bool.false_or] at collision
    contradiction

/-- A native collision at the real bumped entry selects canonical collision,
including creator/target aliasing. No native account is fabricated. -/
theorem native_collision_reservation (machine : EVM.State)
    (accounts : Create2Accounts.Accounts) (sender target : AccountAddress)
    (agrees : ∀ owner : AccountAddress,
      Create2Accounts.bumpCreator accounts sender.val owner.val = creationAccount machine owner)
    (collision : let account := machine.accountMap.getD target default
      (decide (account.nonce ≠ (⟨0⟩ : UInt256)) || decide (account.code.size ≠ 0)) = true) :
    Create2Accounts.reserve accounts sender.val target.val =
      .collision (Create2Accounts.bumpCreator accounts sender.val) := by
  have occupied := native_collision_occupied machine target collision
  have canonical : Create2Accounts.occupied (Create2Accounts.bumpCreator accounts sender.val target.val) = true := by
    rw [agrees target]
    exact occupied
  simp only [Create2Accounts.reserve, canonical, if_true]

/-- Derive full raw agreement at the actual cost-debited, nonce-bumped entry. -/
theorem create2_child_entry_agreement (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (cost : Nat)
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1) :
    Agreement (world.withCreationAccounts (Create2Accounts.bumpCreator world.creationAccounts
      pre.executionEnv.codeOwner.val)) (create2ChildEntry pre cost) warm := by
  let charged := { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat cost }
  have chargedAgreement := agreement_local world pre warm agrees charged.gasAvailable pre.pc pre.stack pre.memory
  have bound : (charged.accountMap.getD pre.executionEnv.codeOwner default).nonce.toNat + 1 < UInt256.size := by
    apply creator_bump_nonce_bound
    simpa only [Std.TreeMap.getD_eq_getD_getElem?, Std.TreeMap.get?_eq_getElem?] using nonce
  exact creator_bump_world_agreement world charged warm chargedAgreement pre.executionEnv.codeOwner bound

/-- The actual bumped native collision selects canonical reservation failure,
callee zero-gas failure and the existing storage-world commit. -/
theorem native_create2_collision_canonical (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (cost : Nat)
    (offset size salt : UInt256)
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (collision : let machine := create2ChildEntry pre cost
      let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
        (pre.memory.readWithPadding offset.toNat size.toNat)
      let account := machine.accountMap.getD target default
      (decide (account.nonce ≠ (⟨0⟩ : UInt256)) || decide (account.code.size ≠ 0)) = true) :
    let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
      (pre.memory.readWithPadding offset.toNat size.toNat)
    let after := Create2Accounts.bumpCreator world.creationAccounts pre.executionEnv.codeOwner.val
    Create2Accounts.reserve world.creationAccounts pre.executionEnv.codeOwner.val target.val = .collision after ∧
      (∀ payload gas, Create2Callee.runEntered world.creationAccounts pre.executionEnv.codeOwner.val target.val
        payload gas = .ok { outcome := .failed after ByteArray.empty, gasLeft := 0 }) ∧
      CreationStorage.commit world (.failed after ByteArray.empty) =
        .ok { world with creationAccounts := after, returndata := [] } := by
  have bumped := create2_child_entry_agreement world pre warm agrees cost nonce
  have reserved := native_collision_reservation (create2ChildEntry pre cost) world.creationAccounts
    pre.executionEnv.codeOwner _ bumped.accounts collision
  refine ⟨reserved, ?_, CreationStorage.commit_failed_empty world _⟩
  intro payload gas
  exact Create2Callee.runEntered_collision _ _ _ _ reserved payload gas

/-- Real native parent completion agrees with the actual canonical failed
storage commit. Target warming and creator nonce insertion are both retained. -/
theorem native_create2_collision_committed (world : Verity.ContractState) (pre : EVM.State)
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
    let after := Create2Accounts.bumpCreator world.creationAccounts pre.executionEnv.codeOwner.val
    ∃ next committed, EVM.step (fuel + 4) cost (some (.CREATE2, none)) pre = .ok next ∧
      CreationStorage.commit world (.failed after ByteArray.empty) = .ok committed ∧
      Agreement committed next (Create2Access.warm warm target.val) ∧
      next.σ₀ = pre.σ₀ ∧ next.memory = pre.memory := by
  obtain ⟨next, stepped, agreement, original, memory⟩ := native_create2_collision_world world pre warm agrees
    fuel cost rest offset size salt popped nonce entry collision
  have canonical := native_create2_collision_canonical world pre warm agrees cost offset size salt nonce collision
  refine ⟨next, _, stepped, canonical.2.2, ?_, original, memory⟩
  exact { agreement with }

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
