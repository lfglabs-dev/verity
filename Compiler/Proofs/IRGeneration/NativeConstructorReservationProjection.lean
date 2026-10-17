import Compiler.Proofs.IRGeneration.NativeConstructorZeroValue

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open NativeCreationWorld

/-- Zero-endowment reservation changes only the target record, even when the
query is the native sender. This statement concerns the actual native map. -/
theorem constructor_zero_account (accounts : AccountMap .EVM) (sender target query : AccountAddress)
    (entry : Account .EVM) (present : accounts.get? sender = some entry)
    (vacant : (accounts.getD target default).nonce = UInt256.ofNat 0) :
    (constructorEnteredAccounts accounts sender target (UInt256.ofNat 0)).getD query default =
      if query = target then
        { (accounts.getD query default) with nonce := UInt256.ofNat 1, storage := default }
      else accounts.getD query default := by
  by_cases same : query = target
  · subst query
    rw [if_pos rfl]
    exact constructor_zero_target accounts sender target entry present vacant
  · rw [if_neg same]
    by_cases senderEq : query = sender
    · subst query
      have distinct : compare target sender ≠ Ordering.eq := by
        intro equal
        exact same (Std.LawfulEqOrd.eq_of_compare equal).symm
      rw [constructor_zero_sender accounts sender target entry present distinct]
      rw [Std.TreeMap.getD_eq_getD_getElem?]
      change entry = (accounts.get? sender).getD default
      rw [present]
      rfl
    · unfold constructorEnteredAccounts
      rw [present, Std.TreeMap.getD_insert]
      have targetNe : compare target query ≠ Ordering.eq := by
        intro equal
        exact same (Std.LawfulEqOrd.eq_of_compare equal).symm
      have senderNe : compare sender query ≠ Ordering.eq := by
        intro equal
        exact senderEq (Std.LawfulEqOrd.eq_of_compare equal).symm
      rw [if_neg targetNe, Std.TreeMap.getD_insert, if_neg senderNe]

/-- The native reservation projects to the canonical nonce-one reservation at
every real address. It makes no modulo-alias claim for arbitrary natural keys. -/
theorem constructor_reservation_projection (machine : EVM.State) (sender target query : AccountAddress)
    (entry : Account .EVM) (present : machine.accountMap.get? sender = some entry)
    (vacant : (machine.accountMap.getD target default).nonce = UInt256.ofNat 0) :
    creationAccount { machine with accountMap := constructorEnteredAccounts machine.accountMap sender target (UInt256.ofNat 0) } query =
      if query = target then { creationAccount machine query with nonce := 1 }
      else creationAccount machine query := by
  have actual := constructor_zero_account machine.accountMap sender target query entry present vacant
  simp only [Std.TreeMap.getD_eq_getD_getElem?] at actual
  unfold creationAccount account account?
  simp only [Std.TreeMap.get?_eq_getElem?]
  rw [actual]
  split <;> rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
