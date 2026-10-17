import Contracts.SolidityImportSmoke.ImportedCreationHeadAllocation

namespace Contracts.SolidityImportSmoke.ImportedCreationDecoderAllocation
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory

def segment : List Stmt := SolidityImport.AbiEncoding.reserve
  "_verity_slice_tmp_0_memory" "_verity_slice_tmp_0_next" (.literal 256)

def allocated (state : DenoteState) (base : Nat) : DenoteState :=
  { state with
    bindings := bindValue (bindValue state.bindings "_verity_slice_tmp_0_memory" base)
      "_verity_slice_tmp_0_next" (base + 256)
    world := state.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat (base + 256)) }

/-- The actual decoder reserves the eight-word Market object before reading fields. -/
theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 5).take 5) = some segment := by rfl

/-- Exact decoder allocation, retaining all original state outside real updates. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base : Nat) (pointer : (state.world.memory 64).val = base)
    (budget : base + 256 ≤ 2^64 - 1) :
    execStmtList oracle fields state segment = .continue (allocated state base) := by
  exact execStmtList_reserve_physical oracle fields state
    "_verity_slice_tmp_0_memory" "_verity_slice_tmp_0_next" (.literal 256)
    base 256 pointer (by decide) (by rfl) budget

/-- Reservation only writes the allocator word; every other byte is unchanged. -/
theorem byte_frame (state : DenoteState) (base query : Nat)
    (outside : query < 64 ∨ 96 ≤ query) :
    (allocated state base).world.physicalByte query = state.world.physicalByte query := by
  exact writePhysicalMemoryValue_byte_outside _ _ _ _ outside

/-- A real allocation establishes coherent overlapping memory observations. -/
theorem coherent (state : DenoteState) (base : Nat) :
    Coherent (allocated state base).world := by
  exact writePhysicalMemoryValue_coherent _ _ _

/-- The next free pointer follows from the actual store, not an output premise. -/
theorem free_pointer (state : DenoteState) (base : Nat) :
    (allocated state base).world.memory 64 = Verity.Core.Uint256.ofNat (base + 256) := by
  exact writePhysicalMemoryValue_at _ _ _

def initialized (state : DenoteState) : DenoteState :=
  { state with world := state.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat 128) }

/-- The real function starts with the Solidity allocator initialization. -/
theorem actual_initial :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body.take 1) = some [.mstore (.literal 64) (.literal 128)] := by rfl

/-- Initializing the allocator is an actual Denote step, for any original world. -/
theorem execute_initial (oracle : DenoteOracle) (fields : List Field) (state : DenoteState) :
    execStmtList oracle fields state [.mstore (.literal 64) (.literal 128)] =
      .continue (initialized state) := by
  exact (SolidityImport.exec_singleton oracle fields state _).trans
    (execStmt_mstore_physical oracle fields state (.literal 64) (.literal 128)
      64 128 (by rfl) (by rfl))

/-- The actual initial store establishes the concrete decoder source address. -/
theorem initial_pointer (state : DenoteState) :
    ((initialized state).world.memory 64).val = 128 := by
  rw [show (initialized state).world.memory 64 = Verity.Core.Uint256.ofNat 128 from
    writePhysicalMemoryValue_at _ _ _]
  rfl

/-- Once intervening guards have passed without world writes, reservation needs
no allocator input hypothesis: source128 and next384 follow from initialization.
This theorem does not assume or assert that those guards pass. -/
theorem execute_initialized (oracle : DenoteOracle) (fields : List Field) (state : DenoteState) :
    execStmtList oracle fields (initialized state) segment =
      .continue (allocated (initialized state) 128) := by
  exact execute oracle fields (initialized state) 128 (initial_pointer state) (by decide)

/-- The concrete reserved Market object lies wholly before the next free pointer. -/
theorem initialized_geometry (state : DenoteState) :
    lookupValue (allocated (initialized state) 128).bindings "_verity_slice_tmp_0_memory" = 128 ∧
    (allocated (initialized state) 128).world.memory 64 = Verity.Core.Uint256.ofNat 384 := by
  constructor
  · exact (SolidityImport.lookup_bind_other _ "_verity_slice_tmp_0_next"
      "_verity_slice_tmp_0_memory" _ (by decide)).trans (SolidityImport.lookup_bind_same _ _ _)
  · exact free_pointer (initialized state) 128

end Contracts.SolidityImportSmoke.ImportedCreationDecoderAllocation
