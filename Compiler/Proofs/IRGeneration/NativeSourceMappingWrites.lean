import Compiler.Proofs.IRGeneration.NativeHashedStorageAgreement
import Compiler.Proofs.IRGeneration.SourceSemantics

namespace Compiler.Proofs.IRGeneration.NativeSourceMappingWrites
open EvmYul NativeCreationWorld NativeCreationStorageOpcodes
open Compiler.Proofs.Storage.HashedMappingLayout

/-- A single actual source target is the same physical write as the native bridge. -/
theorem writeSlots_single (world : Verity.ContractState) (slot : Nat) (value : Verity.Core.Uint256) :
    world.writeSlots [slot] value = world.writeSlot slot value := by
  unfold Verity.ContractState.writeSlots Verity.ContractState.writeSlot
  congr 1
  funext key
  cases key <;> simp [BEq.beq, eq_comm]

/-- Actual source mapping-chain writes use the compiler's exact folded Keccak location. -/
theorem source_chain_write (world : Verity.ContractState) (base : Nat) (keys : List Nat) (value : Nat) :
    SourceSemantics.writeAddressKeyedMappingChainSlots world [base] keys value =
      world.writeSlot (Entry.location (base, keys, 0)) (Verity.Core.Uint256.ofNat value) := by
  have location : SourceSemantics.wordNormalize (SourceSemantics.mappingSlotChain base keys) =
      Entry.location (base, keys, 0) := by
    rfl
  simp only [SourceSemantics.writeAddressKeyedMappingChainSlots, List.map_cons, List.map_nil, location]
  exact writeSlots_single world _ _

/-- The real source mapping update and checked native SSTORE retain full raw agreement. -/
theorem checked_source_chain_write (world : Verity.ContractState) (machine after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some account)
    (agrees : Agreement world machine warm) (base : Nat) (keys : List Nat)
    (value : UInt256) (tail : Stack UInt256)
    (success : CreationCaller.checkedStep
      { machine with stack := UInt256.ofNat (Entry.location (base, keys, 0)) :: value :: tail }
      .SSTORE none = .ok after) :
    Agreement (SourceSemantics.writeAddressKeyedMappingChainSlots world [base] keys value.toNat) after warm := by
  rw [source_chain_write]
  have actual := checked_sstore_agreement world machine warm account present agrees
    (UInt256.ofNat (Entry.location (base, keys, 0))) value tail after success
  rw [NativeHashedStorageAgreement.location_word] at actual
  exact actual

/-- Transient multi-target writes also reduce exactly to their single physical target. -/
theorem writeTransientSlots_single (world : Verity.ContractState) (slot : Nat) (value : Verity.Core.Uint256) :
    world.writeTransientSlots [slot] value = world.writeTransient slot value := by
  unfold Verity.ContractState.writeTransientSlots Verity.ContractState.writeTransient
  congr 1
  funext key
  cases key <;> simp [BEq.beq, eq_comm]

/-- The actual transient source field helper targets the same folded Keccak slot. -/
theorem source_transient_chain_write (fields : List Compiler.CompilationModel.Field) (name : String)
    (transient : SourceSemantics.fieldIsTransient fields name = true)
    (world : Verity.ContractState) (base : Nat) (keys : List Nat) (value : Nat) :
    SourceSemantics.writeAddressKeyedMappingChainFieldSlots fields name world [base] keys value =
      world.writeTransient (Entry.location (base, keys, 0)) (Verity.Core.Uint256.ofNat value) := by
  simp only [SourceSemantics.writeAddressKeyedMappingChainFieldSlots, transient, ite_true,
    List.map_cons, List.map_nil, SourceSemantics.writeTransientTargets]
  simp only [SourceSemantics.wordNormalize_eq_mod, Nat.mod_mod]
  exact writeTransientSlots_single world _ _

/-- A successful native TSTORE matches the actual transient mapping-chain source helper. -/
theorem checked_source_transient_chain_write (world : Verity.ContractState) (machine after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some account)
    (agrees : Agreement world machine warm) (base : Nat) (keys : List Nat)
    (fields : List Compiler.CompilationModel.Field) (name : String)
    (transient : SourceSemantics.fieldIsTransient fields name = true)
    (value : UInt256) (tail : Stack UInt256)
    (success : CreationCaller.checkedStep
      { machine with stack := UInt256.ofNat (Entry.location (base, keys, 0)) :: value :: tail }
      .TSTORE none = .ok after) :
    Agreement (SourceSemantics.writeAddressKeyedMappingChainFieldSlots fields name world [base] keys value.toNat) after warm := by
  rw [source_transient_chain_write fields name transient]
  have actual := checked_tstore_agreement world machine warm account present agrees
    (UInt256.ofNat (Entry.location (base, keys, 0))) value tail after success
  rw [NativeHashedStorageAgreement.location_word] at actual
  exact actual

/-- The persistent source field dispatcher uses the proved checked SSTORE helper. -/
theorem checked_source_persistent_chain_field (world : Verity.ContractState) (machine after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some account)
    (agrees : Agreement world machine warm) (base : Nat) (keys : List Nat)
    (fields : List Compiler.CompilationModel.Field) (name : String)
    (persistent : SourceSemantics.fieldIsTransient fields name = false)
    (value : UInt256) (tail : Stack UInt256)
    (success : CreationCaller.checkedStep
      { machine with stack := UInt256.ofNat (Entry.location (base, keys, 0)) :: value :: tail }
      .SSTORE none = .ok after) :
    Agreement (SourceSemantics.writeAddressKeyedMappingChainFieldSlots fields name world [base] keys value.toNat) after warm := by
  simp only [SourceSemantics.writeAddressKeyedMappingChainFieldSlots, persistent, Bool.false_eq_true, ite_false]
  exact checked_source_chain_write world machine after warm account present agrees base keys value tail success

end Compiler.Proofs.IRGeneration.NativeSourceMappingWrites
