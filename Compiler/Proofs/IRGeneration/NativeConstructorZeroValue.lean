import Compiler.Proofs.IRGeneration.NativeConstructorLambdaAccounts
import Compiler.Proofs.IRGeneration.NativeCreationWorld

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul

private theorem word_sub_zero (value : UInt256) : value - UInt256.ofNat 0 = value := by
  cases value with
  | mk value =>
    change UInt256.mk (value - 0) = UInt256.mk value
    congr 1
    apply Fin.ext
    rw [Fin.sub_val_of_le (Fin.zero_le value)]
    exact Nat.sub_zero _

private theorem word_zero_add (value : UInt256) : UInt256.ofNat 0 + value = value := by
  cases value with
  | mk value =>
    change UInt256.mk (0 + value) = UInt256.mk value
    rw [Fin.zero_add]

/-- With zero endowment, native Lambda preserves its sender in full unless
it is also the target. This retains all persistent and transient storage. -/
theorem constructor_zero_sender (accounts : AccountMap .EVM) (sender target : AccountAddress)
    (account : Account .EVM) (present : accounts.get? sender = some account)
    (distinct : compare target sender ≠ Ordering.eq) :
    (constructorEnteredAccounts accounts sender target (UInt256.ofNat 0)).getD sender default = account := by
  rw [constructor_entered_sender accounts sender target _ account present distinct, word_sub_zero]

/-- Reservation creates nonce one at a vacant target and retains its balance,
while clearing persistent storage and retaining native transient storage. -/
theorem constructor_zero_target (accounts : AccountMap .EVM) (sender target : AccountAddress)
    (account : Account .EVM) (present : accounts.get? sender = some account)
    (vacant : (accounts.getD target default).nonce = UInt256.ofNat 0) :
    (constructorEnteredAccounts accounts sender target (UInt256.ofNat 0)).getD target default =
      { (accounts.getD target default) with nonce := UInt256.ofNat 1, storage := default } := by
  rw [constructor_entered_target accounts sender target _ account present, vacant, word_zero_add]
  simp only [word_zero_add]

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
