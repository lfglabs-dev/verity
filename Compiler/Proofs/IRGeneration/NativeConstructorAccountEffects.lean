import Compiler.Proofs.IRGeneration.NativeConstructorAccountFrames

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model.MidnightInitcode

/-- The account reservation performed by the pinned native Lambda, including
sender absence and native value arithmetic. -/
def constructorEnteredAccounts (accounts : AccountMap .EVM) (sender target : AccountAddress)
    (value : UInt256) : AccountMap .EVM :=
  let old := accounts.getD target default
  let reserved : Account .EVM := { old with
    nonce := old.nonce + UInt256.ofNat 1
    balance := value + old.balance
    storage := default }
  match accounts.get? sender with
  | none => accounts
  | some account => (accounts.insert sender { account with balance := account.balance - value }).insert target reserved

private theorem account_select_not (condition : Bool) (yes no : AccountMap .EVM) :
    (if condition then yes else no) = (if !condition then no else yes) := by
  cases condition <;> rfl

/-- The actual completed result flag decides account commit versus rollback.
No success premise is used to discard failed creation outcomes. -/
theorem lambda_result_account_effects (payload : ByteArray)
    (created : Std.TreeSet AccountAddress compare) (accounts : AccountMap .EVM)
    (substate : Substate) (sender : AccountAddress) (gas value : UInt256) (salt : ByteArray)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : lambdaConstructorResult payload created accounts substate sender gas value salt = .ok result) :
    let target := nativeCreate2Target sender salt (initcode payload)
    let entered := constructorEnteredAccounts accounts sender target value
    result.2.2.1 = if result.2.2.2.2.2.1 then
      entered.insert target { (entered.getD target default) with code := payload }
      else accounts := by
  unfold lambdaConstructorResult at completed
  by_cases low : gas.toNat < prefixCost payload.size
  · simp only [if_pos low] at completed
    cases completed
    rfl
  · simp only [if_neg low] at completed
    cases completed
    exact account_select_not _ _ _

theorem constructor_entered_target (accounts : AccountMap .EVM) (sender target : AccountAddress)
    (value : UInt256) (account : Account .EVM) (present : accounts.get? sender = some account) :
    (constructorEnteredAccounts accounts sender target value).getD target default =
      { (accounts.getD target default) with
        nonce := (accounts.getD target default).nonce + UInt256.ofNat 1
        balance := value + (accounts.getD target default).balance
        storage := default } := by
  unfold constructorEnteredAccounts
  rw [present, Std.TreeMap.getD_insert_self]

theorem constructor_entered_sender (accounts : AccountMap .EVM) (sender target : AccountAddress)
    (value : UInt256) (account : Account .EVM) (present : accounts.get? sender = some account)
    (distinct : compare target sender ≠ Ordering.eq) :
    (constructorEnteredAccounts accounts sender target value).getD sender default =
      { account with balance := account.balance - value } := by
  unfold constructorEnteredAccounts
  rw [present, Std.TreeMap.getD_insert, if_neg distinct, Std.TreeMap.getD_insert_self]

theorem lambda_result_success_target (payload : ByteArray)
    (created : Std.TreeSet AccountAddress compare) (accounts : AccountMap .EVM)
    (substate : Substate) (sender : AccountAddress) (gas value : UInt256) (salt : ByteArray)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : lambdaConstructorResult payload created accounts substate sender gas value salt = .ok result)
    (success : result.2.2.2.2.2.1 = true)
    (account : Account .EVM) (present : accounts.get? sender = some account) :
    let target := nativeCreate2Target sender salt (initcode payload)
    result.2.2.1.getD target default =
      { (accounts.getD target default) with
        nonce := (accounts.getD target default).nonce + UInt256.ofNat 1
        balance := value + (accounts.getD target default).balance
        storage := default
        code := payload } := by
  rw [lambda_result_account_effects payload created accounts substate sender gas value salt result completed]
  simp only [success, if_true, Std.TreeMap.getD_insert_self]
  rw [constructor_entered_target accounts sender _ value account present]

theorem lambda_result_success_sender (payload : ByteArray)
    (created : Std.TreeSet AccountAddress compare) (accounts : AccountMap .EVM)
    (substate : Substate) (sender : AccountAddress) (gas value : UInt256) (salt : ByteArray)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : lambdaConstructorResult payload created accounts substate sender gas value salt = .ok result)
    (success : result.2.2.2.2.2.1 = true)
    (account : Account .EVM) (present : accounts.get? sender = some account)
    (distinct : compare (nativeCreate2Target sender salt (initcode payload)) sender ≠ Ordering.eq) :
    result.2.2.1.getD sender default = { account with balance := account.balance - value } := by
  rw [lambda_result_account_effects payload created accounts substate sender gas value salt result completed]
  simp only [success, if_true]
  rw [Std.TreeMap.getD_insert, if_neg distinct, constructor_entered_sender accounts sender _ value account present distinct]

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
