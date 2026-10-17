import Compiler.Proofs.IRGeneration.NativePairedCallerRefusals
import Compiler.Proofs.Storage.HashedMappingLayout

namespace Compiler.Proofs.IRGeneration.NativeHashedStorageAgreement
open EvmYul NativeCreationWorld NativeCreationStorageOpcodes
open Compiler.Proofs.Storage.HashedMappingLayout

/-- Adding a symbolic shadow does not change any raw physical/native channel. -/
theorem agreement_symbolic_write (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (agrees : Agreement world machine warm)
    (entry : Entry) (value : Verity.Core.Uint256) :
    Agreement (world.writeMapChain entry.1 entry.2.1 entry.2.2 value) machine warm := by
  constructor
  · exact agrees.caller
  · exact agrees.source
  · exact agrees.origin
  · exact agrees.value
  · exact agrees.accounts
  · exact agrees.selfBalance
  · exact agrees.codeSizes
  · intro slot
    simpa only [Verity.ContractState.readSlot_writeMapChain] using agrees.persistent slot
  · exact agrees.transient
  · exact agrees.parkedPersistent
  · exact agrees.parkedTransient
  · exact agrees.accountAccess

/-- The compiler's actual hashed location is a representable native storage word. -/
theorem location_word (entry : Entry) :
    (UInt256.ofNat entry.location).toNat = entry.location := by
  change entry.location % UInt256.size = entry.location
  apply Nat.mod_eq_of_lt
  exact Nat.mod_lt _ (by decide)

/-- An aligned symbolic write matches the real checked native SSTORE and retains layout coherence. -/
theorem checked_hashed_sstore (world : Verity.ContractState) (machine after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some account)
    (agrees : Agreement world machine warm) (tracked : List Entry)
    (coherent : HashedCoherentOn tracked world) (layout : LayoutNonAlias tracked)
    (entry : Entry) (member : entry ∈ tracked) (value : UInt256) (tail : Stack UInt256)
    (success : CreationCaller.checkedStep
      { machine with stack := UInt256.ofNat entry.location :: value :: tail } .SSTORE none = .ok after) :
    let written := alignedWrite world entry (Verity.Core.Uint256.ofNat value.toNat)
    Agreement written after warm ∧ HashedCoherentOn tracked written ∧
      ∀ key ∈ tracked, key.read written =
        persistentWord after after.executionEnv.codeOwner (UInt256.ofNat key.location) := by
  dsimp only
  have shadow := agreement_symbolic_write world machine warm agrees entry (Verity.Core.Uint256.ofNat value.toNat)
  have actual := checked_sstore_agreement _ machine warm account present shadow
    (UInt256.ofNat entry.location) value tail after success
  rw [location_word] at actual
  have retained := alignedWrite_preserves coherent layout member (Verity.Core.Uint256.ofNat value.toNat)
  refine ⟨actual, retained, ?_⟩
  intro key trackedKey
  have native := actual.persistent (UInt256.ofNat key.location)
  rw [location_word] at native
  exact (retained key trackedKey).trans native

/-- Transient mapping shadows leave all raw physical/native channels unchanged. -/
theorem agreement_transient_symbolic_write (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (agrees : Agreement world machine warm)
    (entry : TEntry) (value : Verity.Core.Uint256) :
    Agreement (world.writeTransientMapChain entry.1 entry.2 value) machine warm := by
  constructor
  · exact agrees.caller
  · exact agrees.source
  · exact agrees.origin
  · exact agrees.value
  · exact agrees.accounts
  · exact agrees.selfBalance
  · exact agrees.codeSizes
  · exact agrees.persistent
  · exact agrees.transient
  · exact agrees.parkedPersistent
  · exact agrees.parkedTransient
  · exact agrees.accountAccess

/-- A transient mapping location has the same exact native word representation. -/
theorem transient_location_word (entry : TEntry) :
    (UInt256.ofNat entry.location).toNat = entry.location := by
  exact location_word (entry.1, entry.2, 0)

/-- Aligned transient channels agree with the actual checked TSTORE at every tracked key. -/
theorem checked_hashed_tstore (world : Verity.ContractState) (machine after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some account)
    (agrees : Agreement world machine warm) (tracked : List TEntry)
    (coherent : TransientHashedCoherentOn tracked world)
    (layout : ∀ e ∈ tracked, ∀ e' ∈ tracked, e ≠ e' → e.location ≠ e'.location)
    (entry : TEntry) (member : entry ∈ tracked) (value : UInt256) (tail : Stack UInt256)
    (success : CreationCaller.checkedStep
      { machine with stack := UInt256.ofNat entry.location :: value :: tail } .TSTORE none = .ok after) :
    let written := alignedTransientWrite world entry (Verity.Core.Uint256.ofNat value.toNat)
    Agreement written after warm ∧ TransientHashedCoherentOn tracked written ∧
      ∀ key ∈ tracked, written.readTransientMapChain key.1 key.2 =
        transientWord after after.executionEnv.codeOwner (UInt256.ofNat key.location) := by
  dsimp only
  have shadow := agreement_transient_symbolic_write world machine warm agrees entry (Verity.Core.Uint256.ofNat value.toNat)
  have actual := checked_tstore_agreement _ machine warm account present shadow
    (UInt256.ofNat entry.location) value tail after success
  rw [transient_location_word] at actual
  have retained := alignedTransientWrite_preserves coherent layout member (Verity.Core.Uint256.ofNat value.toNat)
  refine ⟨actual, retained, ?_⟩
  intro key trackedKey
  have native := actual.transient (UInt256.ofNat key.location)
  rw [transient_location_word] at native
  exact (retained key trackedKey).trans native

end Compiler.Proofs.IRGeneration.NativeHashedStorageAgreement
