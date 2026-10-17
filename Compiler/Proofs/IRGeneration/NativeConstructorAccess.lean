import Compiler.Proofs.IRGeneration.NativeConstructorStorageWords

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld

/-- Native target warming is exactly canonical warming at each real address,
including an already-warm target and any query outside the target. -/
theorem constructor_access_projection (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (target query : AccountAddress)
    (agrees : ∀ owner : AccountAddress, warm owner.val = accountWarm machine owner) :
    Verity.Core.Model.Create2Access.warm warm target.val query.val =
      accountWarm { machine with substate := machine.substate.addAccessedAccount target } query := by
  unfold Verity.Core.Model.Create2Access.warm accountWarm Substate.addAccessedAccount
  rw [Std.TreeSet.contains_insert]
  by_cases same : query = target
  · subst query
    simp only [if_true, Std.ReflCmp.compare_self, BEq.rfl, Bool.true_or]
  · have values : query.val ≠ target.val := fun equal => same (Fin.ext equal)
    have distinct : compare target query ≠ Ordering.eq := by
      intro equal
      exact same (Std.LawfulEqOrd.eq_of_compare equal).symm
    rw [if_neg values]
    have compared : (compare target query == Ordering.eq) = false := by
      cases order : compare target query <;> simp_all
    rw [compared, Bool.false_or]
    exact agrees query

/-- Warming is the only native substate update at this constructor boundary:
raw logs, refund, storage access and destruction bookkeeping are retained. -/
theorem constructor_substate_frame (substate : Substate) (target : AccountAddress) :
    { (substate.addAccessedAccount target) with accessedAccounts := substate.accessedAccounts } = substate := rfl


/-- Successful canonical reservation rules out creator/target aliasing. The
native-to-canonical boundary can derive distinctness instead of assuming it. -/
theorem constructor_reserved_distinct (accounts : Verity.Core.Model.Create2Accounts.Accounts)
    (sender target : AccountAddress) (after : Verity.Core.Model.Create2Accounts.Accounts)
    (reserved : Verity.Core.Model.Create2Accounts.reserve accounts sender.val target.val = .reserved after) :
    target ≠ sender := by
  intro same
  subst target
  rw [Verity.Core.Model.Create2Accounts.reserve_self_collision] at reserved
  cases reserved

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
