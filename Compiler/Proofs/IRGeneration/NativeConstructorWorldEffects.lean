import Compiler.Proofs.IRGeneration.NativeConstructorAccess

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld

/-- Whole native account effect of the zero-value constructor at one query. -/
theorem constructor_commit_account (accounts : AccountMap .EVM)
    (sender target query : AccountAddress) (entry : Account .EVM) (payload : ByteArray)
    (flag : Bool) (present : accounts.get? sender = some entry)
    (vacant : (accounts.getD target default).nonce = UInt256.ofNat 0) :
    let entered := constructorEnteredAccounts accounts sender target (UInt256.ofNat 0)
    (if flag then entered.insert target { (entered.getD target default) with code := payload }
      else accounts).getD query default =
      if flag && decide (query = target) then
        { (accounts.getD query default) with nonce := UInt256.ofNat 1, storage := default, code := payload }
      else accounts.getD query default := by
  cases flag with
  | false => rfl
  | true =>
      by_cases same : query = target
      · subst query
        simp only [Bool.true_and, decide_true, if_true, Std.TreeMap.getD_insert_self]
        rw [constructor_zero_target accounts sender target entry present vacant]
      · have distinct : compare target query ≠ Ordering.eq := by
          intro equal
          exact same (Std.LawfulEqOrd.eq_of_compare equal).symm
        simp only [Bool.true_and, same, decide_false, Bool.false_eq_true, if_false, if_true]
        rw [Std.TreeMap.getD_insert, if_neg distinct,
          constructor_zero_account accounts sender target query entry present vacant, if_neg same]

/-- Code at every real address follows exactly the native commit flag. -/
theorem constructor_commit_code (accounts : AccountMap .EVM)
    (sender target query : AccountAddress) (entry : Account .EVM) (payload : ByteArray)
    (flag : Bool) (present : accounts.get? sender = some entry)
    (vacant : (accounts.getD target default).nonce = UInt256.ofNat 0) :
    let entered := constructorEnteredAccounts accounts sender target (UInt256.ofNat 0)
    ((if flag then entered.insert target { (entered.getD target default) with code := payload }
      else accounts).getD query default).code =
      if flag && decide (query = target) then payload else (accounts.getD query default).code := by
  dsimp only
  rw [constructor_commit_account accounts sender target query entry payload flag present vacant]
  split <;> rfl

/-- Value-zero construction preserves every balance, including the native
creator and storage-only targets with an existing balance. -/
theorem constructor_commit_balance (accounts : AccountMap .EVM)
    (sender target query : AccountAddress) (entry : Account .EVM) (payload : ByteArray)
    (flag : Bool) (present : accounts.get? sender = some entry)
    (vacant : (accounts.getD target default).nonce = UInt256.ofNat 0) :
    let entered := constructorEnteredAccounts accounts sender target (UInt256.ofNat 0)
    ((if flag then entered.insert target { (entered.getD target default) with code := payload }
      else accounts).getD query default).balance = (accounts.getD query default).balance := by
  dsimp only
  rw [constructor_commit_account accounts sender target query entry payload flag present vacant]
  split <;> rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
