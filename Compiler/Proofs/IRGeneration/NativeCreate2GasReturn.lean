import Compiler.Proofs.IRGeneration.NativeCreate2WorldAgreement

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul

/-- Forwarded gas is never greater than the actual charged parent budget. -/
theorem native_forwarded_gas_le (gas : UInt256) : EVM.L gas.toNat ≤ gas.toNat := by
  exact Nat.sub_le _ _

/-- With an explicit parent gas bound and a derived child return bound, the
native final addition cannot wrap and its underflow guard cannot fire. -/
theorem native_parent_gas_guard (gas returned : UInt256)
    (bounded : gas.toNat < 2^255) (childBound : returned.toNat ≤ gas.toNat) :
    ¬ (gas + returned).toNat < EVM.L gas.toNat := by
  have modulus : UInt256.size = 2^256 := rfl
  have nowrap : gas.toNat + returned.toNat < UInt256.size := by
    rw [modulus]
    omega
  have sum : (gas + returned).toNat = gas.toNat + returned.toNat := by
    change (gas.toNat + returned.toNat) % UInt256.size = _
    exact Nat.mod_eq_of_lt nowrap
  rw [sum]
  have forwarded := native_forwarded_gas_le gas
  omega


private theorem collision_of_not_vacant (accounts : AccountMap .EVM) (target : AccountAddress)
    (notVacant : ¬ ((accounts.getD target default).nonce = UInt256.ofNat 0 ∧
      (accounts.getD target default).code.size = 0)) :
    (decide ((accounts.getD target default).nonce ≠ (⟨0⟩ : UInt256)) ||
      decide ((accounts.getD target default).code.size ≠ 0)) = true := by
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  have zero : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl
  rw [zero] at notVacant
  by_cases nonce : (accounts.getD target default).nonce = (⟨0⟩ : UInt256)
  · exact Or.inr (fun code => notVacant ⟨nonce, code⟩)
  · exact Or.inl nonce

/-- Every completed real Lambda returns at most its supplied gas budget,
including collisions, prefix OOG, rejected runtime and deposit OOG. -/
theorem lambda_returned_gas_le (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (blobs : List ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (accounts original : AccountMap .EVM)
    (substate : Substate) (sender origin : AccountAddress) (gas price value depth : UInt256)
    (salt : ByteArray) (header : BlockHeader) (permission : Bool)
    (fuel : Nat) (enough : 10 ≤ fuel)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : EVM.Lambda (fuel + 2) blobs created genesis blocks accounts original substate
      sender origin gas price value (Verity.Core.Model.MidnightInitcode.initcode payload)
      depth (some salt) header permission = .ok result) :
    result.2.2.2.1.toNat ≤ gas.toNat := by
  let target := nativeCreate2Target sender salt (Verity.Core.Model.MidnightInitcode.initcode payload)
  by_cases vacant : (accounts.getD target default).nonce = UInt256.ofNat 0 ∧
      (accounts.getD target default).code.size = 0
  · rw [lambda_constructor payload bounded blobs created genesis blocks accounts original substate
      sender origin gas price value depth salt header permission vacant fuel enough] at completed
    rw [lambda_result_canonical_gas payload created accounts substate sender gas value salt result completed]
    split
    · exact Nat.sub_le _ _
    · exact Nat.zero_le _
  · have collision := collision_of_not_vacant accounts target vacant
    rw [show fuel + 2 = (fuel - 1) + 3 by omega,
      lambda_collision (Verity.Core.Model.MidnightInitcode.initcode payload) blobs created genesis blocks
        accounts original substate sender origin gas price value depth salt header permission collision (fuel - 1)] at completed
    cases completed
    exact Nat.zero_le _

/-- Bound the actual CREATE2 child return by the exact forwarded word budget. -/
theorem native_create2_returned_gas_le (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (pre : EVM.State) (cost : Nat) (offset size salt : UInt256)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = Verity.Core.Model.MidnightInitcode.initcode payload)
    (fuel : Nat) (enough : 10 ≤ fuel)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result) :
    result.2.2.2.1.toNat ≤ EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat := by
  unfold nativeCreate2Child at completed
  dsimp only at completed
  rw [code] at completed
  have returned := lambda_returned_gas_le payload bounded _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel enough result completed
  have small : EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat < UInt256.size :=
    lt_of_le_of_lt (native_forwarded_gas_le _) (pre.gasAvailable - UInt256.ofNat cost).val.isLt
  have exactWord : (UInt256.ofNat (EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat)).toNat =
      EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat := Nat.mod_eq_of_lt small
  exact returned.trans (Nat.le_of_eq exactWord)


/-- The actual entered native CREATE2 step completes. Child completion and
returned gas are derived, and the native final gas guard is proved safe. -/
theorem native_create2_parent_completed (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (fuel cost : Nat) (pre : EVM.State) (rest : Stack UInt256) (offset size salt : UInt256)
    (enough : 10 ≤ fuel) (code : pre.memory.readWithPadding offset.toNat size.toNat = Verity.Core.Model.MidnightInitcode.initcode payload)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (gasBound : (pre.gasAvailable - UInt256.ofNat cost).toNat < 2^255) :
    ∃ next, EVM.step (fuel + 3) cost (some (.CREATE2, none)) pre = .ok next := by
  obtain ⟨result, completed⟩ := native_create2_child_completed payload bounded pre cost offset size salt code fuel enough
  have returned := native_create2_returned_gas_le payload bounded pre cost offset size salt code fuel enough result completed
  have guard := native_parent_gas_guard (pre.gasAvailable - UInt256.ofNat cost) result.2.2.2.1 gasBound
    (returned.trans (native_forwarded_gas_le _))
  rcases result with ⟨address, created, accounts, gas, substate, success, data⟩
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
  simp only [guard, if_false]
  exact ⟨_, rfl⟩

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
