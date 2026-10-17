import Compiler.Proofs.IRGeneration.NativeCreationWorldWrites

/-! Flat-slot agreement after exact native writes. These lemmas do not assert
agreement of source hashed channels, gas/refunds, events or whole execution. -/
namespace Compiler.Proofs.IRGeneration.NativeCreationFlatStorage
open EvmYul NativeCreationWorldWrites

private theorem slot_toNat_injective (a b : UInt256) (same : a.toNat = b.toNat) :
    a = b := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      exact congrArg UInt256.mk (Fin.ext same)

/-- A persistent write preserves agreement at every native word address,
including the zero value represented by erasure in the native finite map. -/
theorem persistent_write (world : Verity.ContractState) (entry : Account .EVM)
    (agrees : ∀ key : UInt256, world.readSlot key.toNat =
      Verity.Core.Uint256.ofNat (entry.lookupStorage key).toNat)
    (slot value : UInt256) :
    ∀ key : UInt256,
      (world.writeSlot slot.toNat (Verity.Core.Uint256.ofNat value.toNat)).readSlot key.toNat =
      Verity.Core.Uint256.ofNat ((entry.updateStorage slot value).lookupStorage key).toNat := by
  intro key
  by_cases same : key = slot
  · subst key
    rw [Verity.ContractState.readSlot_writeSlot_same, updateStorage_read_self]
  · have different : key.toNat ≠ slot.toNat := fun equal =>
      same (slot_toNat_injective key slot equal)
    rw [Verity.ContractState.readSlot_writeSlot_other world different,
      updateStorage_read_other entry slot key value same]
    exact agrees key

/-- Transient writes preserve the same flat-slot relation independently of
persistent storage. This is a relation on actual native account updates. -/
theorem transient_write (world : Verity.ContractState) (entry : Account .EVM)
    (agrees : ∀ key : UInt256, world.transientStorage key.toNat =
      Verity.Core.Uint256.ofNat (entry.lookupTransientStorage key).toNat)
    (slot value : UInt256) :
    ∀ key : UInt256,
      (world.writeTransient slot.toNat (Verity.Core.Uint256.ofNat value.toNat)).transientStorage key.toNat =
      Verity.Core.Uint256.ofNat
        ((entry.updateTransientStorage slot value).lookupTransientStorage key).toNat := by
  intro key
  by_cases same : key = slot
  · subst key
    rw [Verity.ContractState.transientStorage_writeTransient_same,
      updateTransientStorage_read_self]
  · have different : key.toNat ≠ slot.toNat := fun equal =>
      same (slot_toNat_injective key slot equal)
    rw [Verity.ContractState.transientStorage_writeTransient_other world different,
      updateTransientStorage_read_other entry slot key value same]
    exact agrees key

/-- Lift flat persistent agreement through the actual native state primitive.
Account presence is required; absent-account writes cannot be manufactured. -/
theorem persistent_sstore (world : Verity.ContractState) (state : EvmYul.State .EVM)
    (entry : Account .EVM)
    (present : state.lookupAccount state.executionEnv.codeOwner = some entry)
    (agrees : ∀ key : UInt256, world.readSlot key.toNat =
      Verity.Core.Uint256.ofNat (entry.lookupStorage key).toNat)
    (slot value key : UInt256) :
    ((state.sstore slot value).lookupAccount state.executionEnv.codeOwner).map
      (fun account => Verity.Core.Uint256.ofNat (account.lookupStorage key).toNat) =
      some ((world.writeSlot slot.toNat (Verity.Core.Uint256.ofNat value.toNat)).readSlot key.toNat) := by
  rw [sstore_self_account state slot value entry present]
  simp only [Option.map_some]
  exact congrArg some (persistent_write world entry agrees slot value key).symm

/-- Lift flat transient agreement through the actual native state primitive. -/
theorem transient_tstore (world : Verity.ContractState) (state : EvmYul.State .EVM)
    (entry : Account .EVM)
    (present : state.lookupAccount state.executionEnv.codeOwner = some entry)
    (agrees : ∀ key : UInt256, world.transientStorage key.toNat =
      Verity.Core.Uint256.ofNat (entry.lookupTransientStorage key).toNat)
    (slot value key : UInt256) :
    ((state.tstore slot value).lookupAccount state.executionEnv.codeOwner).map
      (fun account => Verity.Core.Uint256.ofNat (account.lookupTransientStorage key).toNat) =
      some ((world.writeTransient slot.toNat (Verity.Core.Uint256.ofNat value.toNat)).transientStorage key.toNat) := by
  rw [tstore_self_account state slot value entry present]
  simp only [Option.map_some]
  exact congrArg some (transient_write world entry agrees slot value key).symm

end Compiler.Proofs.IRGeneration.NativeCreationFlatStorage
