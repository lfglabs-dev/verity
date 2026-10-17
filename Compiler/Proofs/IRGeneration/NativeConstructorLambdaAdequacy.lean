import Compiler.Proofs.IRGeneration.NativeConstructorCollision

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model.MidnightInitcode

/-- The explicit result formula always represents a native completed result,
including prefix, deposit and runtime rejection. -/
theorem lambda_result_completed (payload : ByteArray)
    (created : Std.TreeSet AccountAddress compare) (accounts : AccountMap .EVM)
    (substate : Substate) (sender : AccountAddress) (gas value : UInt256) (salt : ByteArray) :
    ∃ result, lambdaConstructorResult payload created accounts substate sender gas value salt = .ok result := by
  unfold lambdaConstructorResult
  by_cases low : gas.toNat < prefixCost payload.size
  · simp only [if_pos low]; exact ⟨_, rfl⟩
  · simp only [if_neg low]; exact ⟨_, rfl⟩

/-- Native constructor fuel adequacy covers both target collision outcomes,
so no CREATE2 admission may confuse interpreter fuel with EVM failure. -/
theorem lambda_all_targets_completed (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (blobs : List ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (substate : Substate)
    (sender origin : AccountAddress) (gas price value depth : UInt256)
    (salt : ByteArray) (header : BlockHeader) (permission : Bool)
    (fuel : Nat) (enough : 10 ≤ fuel) :
    ∃ result, EVM.Lambda (fuel + 2) blobs created genesis blocks accounts original substate
      sender origin gas price value (initcode payload) depth (some salt) header permission =
      .ok result := by
  let target := nativeCreate2Target sender salt (initcode payload)
  by_cases vacant : (accounts.getD target default).nonce = UInt256.ofNat 0 ∧
      (accounts.getD target default).code.size = 0
  · rw [lambda_constructor payload bounded blobs created genesis blocks accounts original substate
      sender origin gas price value depth salt header permission vacant fuel enough]
    exact lambda_result_completed payload created accounts substate sender gas value salt
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
        sender origin gas price value depth salt header permission collision (fuel - 1)]
    exact ⟨_, rfl⟩

theorem lambda_all_targets_adequate (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (blobs : List ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (substate : Substate)
    (sender origin : AccountAddress) (gas price value depth : UInt256)
    (salt : ByteArray) (header : BlockHeader) (permission : Bool)
    (fuel : Nat) (enough : 10 ≤ fuel) :
    EVM.Lambda (fuel + 2) blobs created genesis blocks accounts original substate
      sender origin gas price value (initcode payload) depth (some salt) header permission ≠
      .error .OutOfFuel := by
  obtain ⟨result, completed⟩ := lambda_all_targets_completed payload bounded blobs created genesis blocks
    accounts original substate sender origin gas price value depth salt header permission fuel enough
  rw [completed]
  intro impossible
  cases impossible

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
