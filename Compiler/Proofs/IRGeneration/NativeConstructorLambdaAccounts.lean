import Compiler.Proofs.IRGeneration.NativeConstructorLambdaCallee

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model.MidnightInitcode

/-- Exact map commit/rollback of actual native Lambda for all target states.
All balances, code, storage and account presence remain in the actual map. -/
theorem lambda_accounts (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (blobs : List ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (substate : Substate)
    (sender origin : AccountAddress) (gas price value depth : UInt256)
    (salt : ByteArray) (header : BlockHeader) (permission : Bool)
    (fuel : Nat) (enough : 10 ≤ fuel) :
    let target := nativeCreate2Target sender salt (initcode payload)
    let entered := constructorEnteredAccounts accounts sender target value
    ∃ result, EVM.Lambda (fuel + 2) blobs created genesis blocks accounts original substate
      sender origin gas price value (initcode payload) depth (some salt) header permission = .ok result ∧
      result.2.2.1 = if result.2.2.2.2.2.1 then
        entered.insert target { (entered.getD target default) with code := payload } else accounts := by
  obtain ⟨result, completed⟩ := lambda_all_targets_completed payload bounded blobs created genesis blocks
    accounts original substate sender origin gas price value depth salt header permission fuel enough
  refine ⟨result, completed, ?_⟩
  let target := nativeCreate2Target sender salt (initcode payload)
  by_cases vacant : (accounts.getD target default).nonce = UInt256.ofNat 0 ∧
      (accounts.getD target default).code.size = 0
  · rw [lambda_constructor payload bounded blobs created genesis blocks accounts original substate
      sender origin gas price value depth salt header permission vacant fuel enough] at completed
    exact lambda_result_account_effects payload created accounts substate sender gas value salt result completed
  · have collision : (decide ((accounts.getD target default).nonce ≠ (⟨0⟩ : UInt256)) ||
        decide ((accounts.getD target default).code.size ≠ 0)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      have zeroEq : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl
      rw [zeroEq] at vacant
      by_cases nonce : (accounts.getD target default).nonce = (⟨0⟩ : UInt256)
      · exact Or.inr (fun code => vacant ⟨nonce, code⟩)
      · exact Or.inl nonce
    rw [show fuel + 2 = (fuel - 1) + 3 by omega,
      lambda_collision (initcode payload) blobs created genesis blocks accounts original substate
        sender origin gas price value depth salt header permission collision (fuel - 1)] at completed
    cases completed
    rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
