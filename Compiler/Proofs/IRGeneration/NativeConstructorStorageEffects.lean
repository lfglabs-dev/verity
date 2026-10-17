import Compiler.Proofs.IRGeneration.NativeConstructorCanonicalFinish

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul

/-- Native zero-value reservation clears only target persistent storage;
transient storage is retained at every account, including the target. -/
theorem constructor_reservation_storage (accounts : AccountMap .EVM)
    (sender target query : AccountAddress) (entry : Account .EVM)
    (present : accounts.get? sender = some entry)
    (vacant : (accounts.getD target default).nonce = UInt256.ofNat 0) :
    let account := (constructorEnteredAccounts accounts sender target (UInt256.ofNat 0)).getD query default
    account.storage = (if query = target then default else (accounts.getD query default).storage) ∧
      account.tstorage = (accounts.getD query default).tstorage := by
  rw [constructor_zero_account accounts sender target query entry present vacant]
  split <;> exact ⟨rfl, rfl⟩

/-- Actual code insertion never changes native persistent or transient storage. -/
theorem constructor_install_storage (accounts : AccountMap .EVM) (target query : AccountAddress)
    (payload : ByteArray) :
    let account := (accounts.insert target { (accounts.getD target default) with code := payload }).getD query default
    account.storage = (accounts.getD query default).storage ∧
      account.tstorage = (accounts.getD query default).tstorage := by
  by_cases same : query = target
  · subst query
    rw [Std.TreeMap.getD_insert_self]
    exact ⟨rfl, rfl⟩
  · have distinct : compare target query ≠ Ordering.eq := by
      intro equal
      exact same (Std.LawfulEqOrd.eq_of_compare equal).symm
    rw [Std.TreeMap.getD_insert, if_neg distinct]
    exact ⟨rfl, rfl⟩

/-- Both native storage channels for either actual commit/rollback flag. -/
theorem constructor_commit_storage (accounts : AccountMap .EVM)
    (sender target query : AccountAddress) (entry : Account .EVM) (payload : ByteArray)
    (flag : Bool) (present : accounts.get? sender = some entry)
    (vacant : (accounts.getD target default).nonce = UInt256.ofNat 0) :
    let entered := constructorEnteredAccounts accounts sender target (UInt256.ofNat 0)
    let account := (if flag then entered.insert target { (entered.getD target default) with code := payload }
      else accounts).getD query default
    account.storage = (if flag && decide (query = target) then default else (accounts.getD query default).storage) ∧
      account.tstorage = (accounts.getD query default).tstorage := by
  cases flag with
  | false => exact ⟨rfl, rfl⟩
  | true =>
      have installed := constructor_install_storage
        (constructorEnteredAccounts accounts sender target (UInt256.ofNat 0)) target query payload
      have reserved := constructor_reservation_storage accounts sender target query entry present vacant
      refine ⟨installed.1.trans ?_, installed.2.trans reserved.2⟩
      simpa only [Bool.true_and, decide_eq_true_eq] using reserved.1


/-- Both storage channels of actual completed native Lambda. The real result
flag alone decides target persistent reset; all transient maps are preserved. -/
theorem lambda_storage_effects (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (machine : EVM.State) (sender origin : AccountAddress)
    (gas price depth : UInt256) (salt : ByteArray) (permission : Bool)
    (entry : Account .EVM) (present : machine.accountMap.get? sender = some entry)
    (nonce : let target := nativeCreate2Target sender salt (Verity.Core.Model.MidnightInitcode.initcode payload)
      (machine.accountMap.getD target default).nonce = UInt256.ofNat 0)
    (fuel : Nat) (enough : 10 ≤ fuel) :
    let target := nativeCreate2Target sender salt (Verity.Core.Model.MidnightInitcode.initcode payload)
    ∃ result, EVM.Lambda (fuel + 2) machine.executionEnv.blobVersionedHashes machine.createdAccounts
      machine.genesisBlockHeader machine.blocks machine.accountMap machine.σ₀ machine.substate
      sender origin gas price (UInt256.ofNat 0) (Verity.Core.Model.MidnightInitcode.initcode payload)
      depth (some salt) machine.executionEnv.header permission = .ok result ∧
      ∀ query : AccountAddress,
        (result.2.2.1.getD query default).storage =
          (if result.2.2.2.2.2.1 && decide (query = target) then default
            else (machine.accountMap.getD query default).storage) ∧
        (result.2.2.1.getD query default).tstorage = (machine.accountMap.getD query default).tstorage := by
  obtain ⟨result, completed, accounts⟩ := lambda_accounts payload bounded
    machine.executionEnv.blobVersionedHashes machine.createdAccounts machine.genesisBlockHeader
    machine.blocks machine.accountMap machine.σ₀ machine.substate sender origin gas price
    (UInt256.ofNat 0) depth salt machine.executionEnv.header permission fuel enough
  refine ⟨result, completed, ?_⟩
  intro query
  rw [accounts]
  exact constructor_commit_storage machine.accountMap sender
    (nativeCreate2Target sender salt (Verity.Core.Model.MidnightInitcode.initcode payload))
    query entry payload result.2.2.2.2.2.1 present nonce

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
