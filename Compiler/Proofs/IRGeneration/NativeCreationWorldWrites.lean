import Compiler.Proofs.IRGeneration.NativeCreationWorldSteps
import Compiler.Proofs.EvmYulUInt256Order
import Std.Data.TreeMap.Lemmas

/-! Exact reads after actual pinned storage writes. The shared native word-order module
supplies the proven TransCmp instance for native UInt256, not a new assumption.
These observations still require full canonical/source-channel preservation. -/
namespace Compiler.Proofs.IRGeneration.NativeCreationWorldWrites
open EvmYul NativeCreationWorldSteps

theorem sstore_self_account (state : EvmYul.State .EVM) (slot value : UInt256)
    (entry : Account .EVM)
    (present : state.lookupAccount state.executionEnv.codeOwner = some entry) :
    (state.sstore slot value).lookupAccount state.executionEnv.codeOwner =
      some (entry.updateStorage slot value) := by
  unfold EvmYul.State.lookupAccount
  rw [sstore_account state slot value entry present]
  change (state.accountMap.insert state.executionEnv.codeOwner
    (entry.updateStorage slot value))[state.executionEnv.codeOwner]? = _
  exact Std.TreeMap.getElem?_insert_self

theorem tstore_self_account (state : EvmYul.State .EVM) (slot value : UInt256)
    (entry : Account .EVM)
    (present : state.lookupAccount state.executionEnv.codeOwner = some entry) :
    (state.tstore slot value).lookupAccount state.executionEnv.codeOwner =
      some (entry.updateTransientStorage slot value) := by
  unfold EvmYul.State.lookupAccount
  rw [tstore_account state slot value entry present]
  change (state.accountMap.insert state.executionEnv.codeOwner
    (entry.updateTransientStorage slot value))[state.executionEnv.codeOwner]? = _
  exact Std.TreeMap.getElem?_insert_self

private theorem native_beq_zero (value : UInt256)
    (h : (value == UInt256.ofNat 0) = true) : value = UInt256.ofNat 0 := by
  cases value with
  | mk value =>
      change (value == (UInt256.ofNat 0).val) = true at h
      have eq := LawfulBEq.eq_of_beq h
      exact congrArg UInt256.mk eq

/-- Zero erases the finite-map entry; it still reads as exactly zero. -/
theorem updateStorage_read_self (entry : Account .EVM) (slot value : UInt256) :
    (entry.updateStorage slot value).lookupStorage slot = value := by
  unfold Account.updateStorage
  split
  · rename_i zero
    have valueZero := native_beq_zero value zero
    subst value
    unfold Account.lookupStorage
    change (entry.storage.erase slot).getD slot (UInt256.ofNat 0) = _
    exact Std.TreeMap.getD_erase_self
  · unfold Account.lookupStorage
    change (entry.storage.insert slot value).getD slot (UInt256.ofNat 0) = _
    exact Std.TreeMap.getD_insert_self

theorem updateTransientStorage_read_self (entry : Account .EVM) (slot value : UInt256) :
    (entry.updateTransientStorage slot value).lookupTransientStorage slot = value := by
  unfold Account.updateTransientStorage
  split
  · rename_i zero
    have valueZero := native_beq_zero value zero
    subst value
    unfold Account.lookupTransientStorage
    change (entry.tstorage.erase slot).getD slot (UInt256.ofNat 0) = _
    exact Std.TreeMap.getD_erase_self
  · unfold Account.lookupTransientStorage
    change (entry.tstorage.insert slot value).getD slot (UInt256.ofNat 0) = _
    exact Std.TreeMap.getD_insert_self

theorem sstore_read_self (state : EvmYul.State .EVM) (slot value : UInt256)
    (entry : Account .EVM)
    (present : state.lookupAccount state.executionEnv.codeOwner = some entry) :
    ((state.sstore slot value).lookupAccount state.executionEnv.codeOwner).map
      (fun account => account.lookupStorage slot) = some value := by
  rw [sstore_self_account state slot value entry present]
  simp only [Option.map_some, updateStorage_read_self]

theorem tstore_read_self (state : EvmYul.State .EVM) (slot value : UInt256)
    (entry : Account .EVM)
    (present : state.lookupAccount state.executionEnv.codeOwner = some entry) :
    ((state.tstore slot value).lookupAccount state.executionEnv.codeOwner).map
      (fun account => account.lookupTransientStorage slot) = some value := by
  rw [tstore_self_account state slot value entry present]
  simp only [Option.map_some, updateTransientStorage_read_self]

/-- The native zero-erasing representation preserves every distinct slot. -/
theorem updateStorage_read_other (entry : Account .EVM) (slot other value : UInt256)
    (different : other ≠ slot) :
    (entry.updateStorage slot value).lookupStorage other = entry.lookupStorage other := by
  have distinct : compare slot other ≠ Ordering.eq := by
    intro equal
    exact different (Compiler.Proofs.EvmYulUInt256Order.UInt256_eq_of_compare_eq equal).symm
  unfold Account.updateStorage
  split
  · change (entry.storage.erase slot).getD other (UInt256.ofNat 0) = _
    rw [Std.TreeMap.getD_erase, if_neg distinct]
    rfl
  · change (entry.storage.insert slot value).getD other (UInt256.ofNat 0) = _
    rw [Std.TreeMap.getD_insert, if_neg distinct]
    rfl

theorem updateTransientStorage_read_other (entry : Account .EVM) (slot other value : UInt256)
    (different : other ≠ slot) :
    (entry.updateTransientStorage slot value).lookupTransientStorage other =
      entry.lookupTransientStorage other := by
  have distinct : compare slot other ≠ Ordering.eq := by
    intro equal
    exact different (Compiler.Proofs.EvmYulUInt256Order.UInt256_eq_of_compare_eq equal).symm
  unfold Account.updateTransientStorage
  split
  · change (entry.tstorage.erase slot).getD other (UInt256.ofNat 0) = _
    rw [Std.TreeMap.getD_erase, if_neg distinct]
    rfl
  · change (entry.tstorage.insert slot value).getD other (UInt256.ofNat 0) = _
    rw [Std.TreeMap.getD_insert, if_neg distinct]
    rfl

end Compiler.Proofs.IRGeneration.NativeCreationWorldWrites
