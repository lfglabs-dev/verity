import Compiler.Proofs.IRGeneration.NativeConstructorStorageEffects
import Verity.Core.Model.CreationStorage

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld

/-- Persistent word observation from the exact map effect, including zero
reads of the freshly cleared native target storage. -/
theorem constructor_persistent_word (before after : EVM.State) (target query : AccountAddress)
    (flag : Bool) (slot : UInt256)
    (effect : (after.accountMap.getD query default).storage =
      if flag && decide (query = target) then default else (before.accountMap.getD query default).storage) :
    persistentWord after query slot = if flag && decide (query = target) then 0
      else persistentWord before query slot := by
  unfold persistentWord account account?
  simp only [Std.TreeMap.get?_eq_getElem?, ← Std.TreeMap.getD_eq_getD_getElem?]
  rw [effect]
  split <;> rfl

/-- Transient word equality follows from the retained actual transient map. -/
theorem constructor_transient_word (before after : EVM.State) (query : AccountAddress)
    (slot : UInt256)
    (effect : (after.accountMap.getD query default).tstorage = (before.accountMap.getD query default).tstorage) :
    transientWord after query slot = transientWord before query slot := by
  unfold transientWord account account?
  simp only [Std.TreeMap.get?_eq_getElem?, ← Std.TreeMap.getD_eq_getD_getElem?]
  rw [effect]

/-- Canonical parked physical storage agrees with the actual native reset.
The caller's own store is a separate channel; it requires target distinctness. -/
theorem constructor_parked_persistent (world : Verity.ContractState) (before after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (agrees : Agreement world before warm)
    (target owner : AccountAddress) (flag : Bool) (slot : UInt256)
    (foreign : owner ≠ before.executionEnv.codeOwner)
    (effect : (after.accountMap.getD owner default).storage =
      if flag && decide (owner = target) then default else (before.accountMap.getD owner default).storage) :
    (if flag then Verity.Core.Model.CreationStorage.clear world target.val else world).storageWords
      (.contractSlot owner.val slot.toNat) = persistentWord after owner slot := by
  rw [constructor_persistent_word before after target owner flag slot effect]
  cases flag with
  | false => exact agrees.parkedPersistent owner foreign slot
  | true =>
      by_cases same : owner = target
      · subst owner
        simp only [Bool.true_and, decide_true, if_true]
        exact Verity.Core.Model.CreationStorage.clear_target_slot world target.val slot.toNat
      · have values : owner.val ≠ target.val := fun equal => same (Fin.ext equal)
        simp only [Bool.true_and, same, decide_false, Bool.false_eq_true, if_false, if_true]
        rw [Verity.Core.Model.CreationStorage.clear_other_slot world target.val owner.val slot.toNat values]
        exact agrees.parkedPersistent owner foreign slot


/-- The distinct creation target cannot reset the caller's plain storage. -/
theorem constructor_caller_persistent (world : Verity.ContractState) (before after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (agrees : Agreement world before warm)
    (target : AccountAddress) (flag : Bool) (slot : UInt256)
    (distinct : before.executionEnv.codeOwner ≠ target)
    (effect : (after.accountMap.getD before.executionEnv.codeOwner default).storage =
      if flag && decide (before.executionEnv.codeOwner = target) then default
      else (before.accountMap.getD before.executionEnv.codeOwner default).storage) :
    (if flag then Verity.Core.Model.CreationStorage.clear world target.val else world).readSlot slot.toNat =
      persistentWord after before.executionEnv.codeOwner slot := by
  rw [constructor_persistent_word before after target before.executionEnv.codeOwner flag slot effect]
  simp only [distinct, decide_false, Bool.and_false, Bool.false_eq_true, if_false]
  cases flag <;> exact agrees.persistent slot

/-- Canonical target clearing preserves the caller's transient channel. -/
theorem constructor_caller_transient (world : Verity.ContractState) (before after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (agrees : Agreement world before warm)
    (target : AccountAddress) (flag : Bool) (slot : UInt256)
    (effect : (after.accountMap.getD before.executionEnv.codeOwner default).tstorage =
      (before.accountMap.getD before.executionEnv.codeOwner default).tstorage) :
    (if flag then Verity.Core.Model.CreationStorage.clear world target.val else world).transientStorage slot.toNat =
      transientWord after before.executionEnv.codeOwner slot := by
  rw [constructor_transient_word before after before.executionEnv.codeOwner slot effect]
  cases flag <;> exact agrees.transient slot

/-- Parked transient channels survive both native commit and canonical clear. -/
theorem constructor_parked_transient (world : Verity.ContractState) (before after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (agrees : Agreement world before warm)
    (target owner : AccountAddress) (flag : Bool) (slot : UInt256)
    (foreign : owner ≠ before.executionEnv.codeOwner)
    (effect : (after.accountMap.getD owner default).tstorage = (before.accountMap.getD owner default).tstorage) :
    (if flag then Verity.Core.Model.CreationStorage.clear world target.val else world).storageWords
      (.scoped owner.val (.transient slot.toNat)) = transientWord after owner slot := by
  rw [constructor_transient_word before after owner slot effect]
  cases flag with
  | false => exact agrees.parkedTransient owner foreign slot
  | true =>
      simp only [if_true]
      rw [Verity.Core.Model.CreationStorage.clear_parked_transient]
      exact agrees.parkedTransient owner foreign slot

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
