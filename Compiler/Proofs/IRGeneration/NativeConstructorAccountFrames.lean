import Compiler.Proofs.IRGeneration.NativeConstructorCreate2Fuel

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model.MidnightInitcode

private theorem account_getD_ite (condition : Prop) [Decidable condition]
    (yes no : AccountMap .EVM) (query : AccountAddress) :
    (if condition then yes else no).getD query default =
      if condition then yes.getD query default else no.getD query default := by
  split <;> rfl

private theorem account_choice (condition : Prop) [Decidable condition]
    (yes no expected : Account .EVM) (left : yes = expected) (right : no = expected) :
    (if condition then yes else no) = expected := by
  split <;> assumption

/-- Every native account outside the sender and target is preserved in full,
including storage, code, balance and transient storage. -/
theorem lambda_result_account_frame (payload : ByteArray)
    (created : Std.TreeSet AccountAddress compare) (accounts : AccountMap .EVM)
    (substate : Substate) (sender query : AccountAddress) (gas value : UInt256) (salt : ByteArray)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : lambdaConstructorResult payload created accounts substate sender gas value salt = .ok result)
    (notSender : compare sender query ≠ Ordering.eq)
    (notTarget : compare (nativeCreate2Target sender salt (initcode payload)) query ≠ Ordering.eq) :
    result.2.2.1.getD query default = accounts.getD query default := by
  unfold lambdaConstructorResult at completed
  by_cases low : gas.toNat < prefixCost payload.size
  · simp only [if_pos low] at completed
    cases completed
    rfl
  · simp only [if_neg low] at completed
    cases completed
    dsimp only
    rw [account_getD_ite]
    apply account_choice
    · rfl
    · rw [Std.TreeMap.getD_insert, if_neg notTarget]
      cases accounts.get? sender with
      | none => rfl
      | some account =>
        rw [Std.TreeMap.getD_insert, if_neg notTarget, Std.TreeMap.getD_insert, if_neg notSender]

private theorem account_getElem_ite (condition : Prop) [Decidable condition]
    (yes no : AccountMap .EVM) (query : AccountAddress) :
    (if condition then yes else no)[query]? =
      if condition then yes[query]? else no[query]? := by
  split <;> rfl

private theorem account_option_choice (condition : Prop) [Decidable condition]
    (yes no expected : Option (Account .EVM)) (left : yes = expected) (right : no = expected) :
    (if condition then yes else no) = expected := by
  split <;> assumption

/-- Every native account outside the sender and target is preserved in full,
including storage, code, balance and transient storage. -/
theorem lambda_result_presence_frame (payload : ByteArray)
    (created : Std.TreeSet AccountAddress compare) (accounts : AccountMap .EVM)
    (substate : Substate) (sender query : AccountAddress) (gas value : UInt256) (salt : ByteArray)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : lambdaConstructorResult payload created accounts substate sender gas value salt = .ok result)
    (notSender : compare sender query ≠ Ordering.eq)
    (notTarget : compare (nativeCreate2Target sender salt (initcode payload)) query ≠ Ordering.eq) :
    (result.2.2.1)[query]? = accounts[query]? := by
  unfold lambdaConstructorResult at completed
  by_cases low : gas.toNat < prefixCost payload.size
  · simp only [if_pos low] at completed
    cases completed
    rfl
  · simp only [if_neg low] at completed
    cases completed
    dsimp only
    rw [account_getElem_ite]
    apply account_option_choice
    · rfl
    · rw [Std.TreeMap.getElem?_insert, if_neg notTarget]
      cases accounts.get? sender with
      | none => rfl
      | some account =>
        rw [Std.TreeMap.getElem?_insert, if_neg notTarget, Std.TreeMap.getElem?_insert, if_neg notSender]

theorem lambda_foreign_account_frame (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (blobs : List ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (substate : Substate)
    (sender origin : AccountAddress) (gas price value depth : UInt256)
    (salt : ByteArray) (header : BlockHeader) (permission : Bool)
    (query : AccountAddress)
    (notSender : compare sender query ≠ Ordering.eq)
    (notTarget : compare (nativeCreate2Target sender salt (initcode payload)) query ≠ Ordering.eq)
    (fuel : Nat) (enough : 10 ≤ fuel)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : EVM.Lambda (fuel + 2) blobs created genesis blocks accounts original substate
      sender origin gas price value (initcode payload) depth (some salt) header permission = .ok result) :
    result.2.2.1.getD query default = accounts.getD query default := by
  let target := nativeCreate2Target sender salt (initcode payload)
  by_cases vacant : (accounts.getD target default).nonce = UInt256.ofNat 0 ∧
      (accounts.getD target default).code.size = 0
  · rw [lambda_constructor payload bounded blobs created genesis blocks accounts original substate
      sender origin gas price value depth salt header permission vacant fuel enough] at completed
    exact lambda_result_account_frame payload created accounts substate sender query gas value salt
      result completed notSender notTarget
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

theorem lambda_foreign_presence_frame (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (blobs : List ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (substate : Substate)
    (sender origin : AccountAddress) (gas price value depth : UInt256)
    (salt : ByteArray) (header : BlockHeader) (permission : Bool)
    (query : AccountAddress)
    (notSender : compare sender query ≠ Ordering.eq)
    (notTarget : compare (nativeCreate2Target sender salt (initcode payload)) query ≠ Ordering.eq)
    (fuel : Nat) (enough : 10 ≤ fuel)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : EVM.Lambda (fuel + 2) blobs created genesis blocks accounts original substate
      sender origin gas price value (initcode payload) depth (some salt) header permission = .ok result) :
    (result.2.2.1)[query]? = accounts[query]? := by
  let target := nativeCreate2Target sender salt (initcode payload)
  by_cases vacant : (accounts.getD target default).nonce = UInt256.ofNat 0 ∧
      (accounts.getD target default).code.size = 0
  · rw [lambda_constructor payload bounded blobs created genesis blocks accounts original substate
      sender origin gas price value depth salt header permission vacant fuel enough] at completed
    exact lambda_result_presence_frame payload created accounts substate sender query gas value salt
      result completed notSender notTarget
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
