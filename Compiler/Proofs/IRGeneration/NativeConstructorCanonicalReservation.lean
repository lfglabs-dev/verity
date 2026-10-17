import Compiler.Proofs.IRGeneration.NativeConstructorReservationProjection

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open NativeCreationWorld
open Verity.Core.Model.Create2Accounts

private theorem vacant_projection (machine : EVM.State) (target : AccountAddress)
    (nonce : (machine.accountMap.getD target default).nonce = UInt256.ofNat 0)
    (code : (machine.accountMap.getD target default).code.size = 0) :
    (creationAccount machine target).nonce = 0 ∧ (creationAccount machine target).code.size = 0 := by
  unfold creationAccount account account?
  simp only [Std.TreeMap.getD_eq_getD_getElem?, Std.TreeMap.get?_eq_getElem?] at nonce code ⊢
  rw [nonce]
  exact ⟨rfl, code⟩

/-- The native Lambda starts after the creator nonce bump. Given agreement at
that real boundary, its zero-value reservation is exactly canonical reserve,
queried only at real EVM addresses; no fabricated initial machine is used. -/
theorem constructor_canonical_reservation (machine : EVM.State)
    (before : Accounts) (sender target : AccountAddress) (entry : Account .EVM)
    (present : machine.accountMap.get? sender = some entry)
    (nonce : (machine.accountMap.getD target default).nonce = UInt256.ofNat 0)
    (code : (machine.accountMap.getD target default).code.size = 0)
    (agrees : ∀ owner : AccountAddress,
      bumpCreator before sender.val owner.val = creationAccount machine owner) :
    ∃ after, reserve before sender.val target.val = .reserved after ∧
      ∀ query : AccountAddress,
        creationAccount { machine with accountMap := constructorEnteredAccounts machine.accountMap sender target (UInt256.ofNat 0) } query =
          after query.val := by
  let bumped := bumpCreator before sender.val
  let after : Accounts := fun query => if query = target.val then
    { bumped query with nonce := 1 } else bumped query
  have vacant := vacant_projection machine target nonce code
  have unoccupied : occupied (bumped target.val) = false := by
    rw [show bumped target.val = creationAccount machine target from agrees target]
    simp only [occupied, vacant.1, vacant.2, bne_self_eq_false, Bool.false_or]
  refine ⟨after, ?_, ?_⟩
  · change (if occupied (bumped target.val) then Reservation.collision bumped
      else Reservation.reserved after) = Reservation.reserved after
    rw [unoccupied]
    rfl
  · intro query
    rw [constructor_reservation_projection machine sender target query entry present nonce]
    change (if query = target then { creationAccount machine query with nonce := 1 }
      else creationAccount machine query) =
      if query.val = target.val then { bumped query.val with nonce := 1 } else bumped query.val
    rw [show bumped query.val = creationAccount machine query from agrees query]
    have same : query.val = target.val ↔ query = target := Fin.val_inj
    simp only [same]


/-- Runtime installation projects the actual native account insertion; account
presence and storage remain in the native map rather than this narrow view. -/
theorem constructor_install_projection (machine : EVM.State) (target query : AccountAddress)
    (payload : ByteArray) :
    creationAccount { machine with accountMap := (machine.accountMap.insert target
      { (machine.accountMap.getD target default) with code := payload }) } query =
      if query = target then { creationAccount machine query with code := payload }
      else creationAccount machine query := by
  have actual : (machine.accountMap.insert target
      { (machine.accountMap.getD target default) with code := payload }).getD query default =
      if query = target then { (machine.accountMap.getD query default) with code := payload }
      else machine.accountMap.getD query default := by
    by_cases same : query = target
    · subst query
      rw [if_pos rfl, Std.TreeMap.getD_insert_self]
    · have distinct : compare target query ≠ Ordering.eq := by
        intro equal
        exact same (Std.LawfulEqOrd.eq_of_compare equal).symm
      rw [if_neg same, Std.TreeMap.getD_insert, if_neg distinct]
  simp only [Std.TreeMap.getD_eq_getD_getElem?] at actual
  unfold creationAccount account account?
  simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getD_eq_getD_getElem?]
  rw [actual]
  split <;> rfl

/-- Given the real reserved boundary projection, native code installation is
canonical installRuntime at every EVM address. -/
theorem constructor_canonical_install (machine : EVM.State) (accounts : Accounts)
    (target query : AccountAddress) (payload : ByteArray)
    (agrees : ∀ owner : AccountAddress, accounts owner.val = creationAccount machine owner) :
    creationAccount { machine with accountMap := (machine.accountMap.insert target
      { (machine.accountMap.getD target default) with code := payload }) } query =
      Verity.Core.Model.Create2Runtime.installRuntime accounts target.val payload query.val := by
  rw [constructor_install_projection]
  unfold Verity.Core.Model.Create2Runtime.installRuntime
  rw [agrees query]
  simp only [Fin.val_inj]

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
