import Compiler.Proofs.IRGeneration.NativeConstructorWorldTransport

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model.Create2Accounts

private theorem nonce_add_one (nonce : UInt256) (bounded : nonce.toNat + 1 < UInt256.size) :
    (nonce + UInt256.ofNat 1).toNat = nonce.toNat + 1 := by
  change (nonce.toNat + 1) % UInt256.size = nonce.toNat + 1
  exact Nat.mod_eq_of_lt bounded

/-- The creator nonce insertion used by actual native CREATE2 projects to the
canonical bump at every real account address, with an explicit no-wrap bound. -/
theorem constructor_creator_bump (machine : EVM.State) (accounts : Accounts)
    (sender query : AccountAddress)
    (bounded : (machine.accountMap.getD sender default).nonce.toNat + 1 < UInt256.size)
    (agrees : ∀ owner : AccountAddress, accounts owner.val = creationAccount machine owner) :
    bumpCreator accounts sender.val query.val =
      creationAccount { machine with accountMap := (machine.accountMap.insert sender
        { (machine.accountMap.getD sender default) with
          nonce := (machine.accountMap.getD sender default).nonce + UInt256.ofNat 1 }) } query := by
  have actual : (machine.accountMap.insert sender
      { (machine.accountMap.getD sender default) with
        nonce := (machine.accountMap.getD sender default).nonce + UInt256.ofNat 1 }).getD query default =
      if query = sender then { (machine.accountMap.getD query default) with
        nonce := (machine.accountMap.getD query default).nonce + UInt256.ofNat 1 }
      else machine.accountMap.getD query default := by
    by_cases same : query = sender
    · subst query
      rw [Std.TreeMap.getD_insert_self, if_pos rfl]
    · have distinct : compare sender query ≠ Ordering.eq := by
        intro equal
        exact same (Std.LawfulEqOrd.eq_of_compare equal).symm
      rw [Std.TreeMap.getD_insert, if_neg distinct, if_neg same]
  unfold bumpCreator
  rw [agrees query]
  unfold creationAccount account account?
  simp only [Std.TreeMap.get?_eq_getElem?, ← Std.TreeMap.getD_eq_getD_getElem?]
  rw [actual]
  by_cases same : query = sender
  · subst query
    simp only [if_true, nonce_add_one _ bounded]
  · have values : query.val ≠ sender.val := fun equal => same (Fin.ext equal)
    rw [if_neg values, if_neg same]

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
