import Contracts.SolidityImportSmoke.ImportedCreationAllocatedPacking

namespace Contracts.SolidityImportSmoke.ImportedCreationOriginalSnapshots
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration
open ImportedCreationAllocatedPacking

/-- Exact entire allocator world, derived from its actual successful run. -/
theorem allocator_world (oracle : DenoteOracle) (fields : List Field)
    (initial allocated : DenoteState) (destination size : Nat)
    (pointer : (initial.world.memory 64).val = destination)
    (length : lookupValue initial.bindings "_verity_slice_tmp_22" = size)
    (bounded : destination + 32 * ((size + 31) / 32) ≤ 2^64 - 1)
    (executed : execStmtList oracle fields initial ImportedCreationAllocator.segment = .continue allocated) :
    allocated.world = abiClearPhysicalWorld
      (initial.world.writePhysicalMemoryValue 64
        (Verity.Core.Uint256.ofNat (destination + 32 * ((size + 31) / 32))))
      destination ((size + 31) / 32) := by
  obtain ⟨after, ran, _, memory, _⟩ := execStmtList_packedBuffer_coherent oracle fields initial
    "_verity_slice_tmp_23" "_verity_slice_tmp_24" "_verity_slice_tmp_25" "_verity_slice_tmp_22"
    destination size pointer length (by decide) (by decide) (by decide) (by decide) bounded
  have combined : execStmtList oracle fields initial ImportedCreationAllocator.segment =
      .continue { after with bindings := bindValue after.bindings "_verity_slice_tmp_26" 0 } := by
    rw [ImportedCreationAllocator.segment, SolidityImport.exec_append, ImportedCreationAllocator.allocation, ran]
    rfl
  have same := StmtOutcome.continue.inj (executed.symm.trans combined)
  have projected := congrArg DenoteState.world same
  exact projected.trans memory

/-- A source interval before the allocation, away from the free pointer,
retains every physical byte through the ACTUAL allocator execution. -/
theorem allocator_source (oracle : DenoteOracle) (fields : List Field)
    (initial allocated : DenoteState) (destination size source count : Nat)
    (pointer : (initial.world.memory 64).val = destination)
    (length : lookupValue initial.bindings "_verity_slice_tmp_22" = size)
    (bounded : destination + 32 * ((size + 31) / 32) ≤ 2^64 - 1)
    (executed : execStmtList oracle fields initial ImportedCreationAllocator.segment = .continue allocated)
    (pastPointer : 96 ≤ source) (beforeOutput : source + count ≤ destination) :
    ∀ index < count, allocated.world.physicalByte (source + index) =
      initial.world.physicalByte (source + index) := by
  intro index inside
  rw [allocator_world oracle fields initial allocated destination size pointer length bounded executed,
    abiClearPhysicalWorld_byte, if_neg (by omega)]
  exact writePhysicalMemoryValue_byte_outside _ _ _ _ (Or.inr (by omega))

/-- Convert the derived allocated-state copies to ORIGINAL segment-entry
snapshots. The allocator's pointer write and clearing are framed explicitly. -/
theorem original_snapshot (oracle : DenoteOracle) (fields : List Field)
    (initial allocated : DenoteState) (hsource psource destination size : Nat)
    (geometry : Geometry hsource psource destination size)
    (headerPastPointer : 96 ≤ hsource) (payloadPastPointer : 96 ≤ psource)
    (pointer : (initial.world.memory 64).val = destination)
    (length : lookupValue initial.bindings "_verity_slice_tmp_22" = 11 + size)
    (bounded : destination + 32 * ((11 + size + 31) / 32) ≤ 2^64 - 1)
    (executed : execStmtList oracle fields initial ImportedCreationAllocator.segment = .continue allocated) :
    Verity.Core.Model.Create2.physicalInitcodeBytes
      ((allocated.world.copyPhysicalBytes allocated.world.physicalByte destination hsource 11).copyPhysicalBytes
        allocated.world.physicalByte (destination + 11) psource size) destination (11 + size) =
    Verity.Core.Model.Create2.physicalInitcodeBytes
      ((initial.world.copyPhysicalBytes initial.world.physicalByte destination hsource 11).copyPhysicalBytes
        initial.world.physicalByte (destination + 11) psource size) destination (11 + size) := by
  exact CreationRelocatedCopies.packed_slice allocated.world initial.world
    allocated.world.physicalByte initial.world.physicalByte
    allocated.world.physicalByte initial.world.physicalByte destination destination hsource hsource psource psource 11 size
    (allocator_source oracle fields initial allocated destination (11 + size) hsource 11 pointer length
      bounded executed headerPastPointer geometry.headerBefore)
    (allocator_source oracle fields initial allocated destination (11 + size) psource size pointer length
      bounded executed payloadPastPointer geometry.payloadBefore)

/-- The actual ten-statement segment copies precisely the ORIGINAL header and
payload bytes. No intermediate snapshot/world or zero condition is an input. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (hsource psource destination size : Nat) (geometry : Geometry hsource psource destination size)
    (headerPastPointer : 96 ≤ hsource) (payloadPastPointer : 96 ≤ psource)
    (pointer : (state.world.memory 64).val = destination)
    (sizeValue : lookupValue state.bindings "_verity_slice_tmp_22" = 11 + size)
    (header : lookupValue state.bindings "_verity_slice_tmp_20" = hsource)
    (payload : lookupValue state.bindings "_verity_slice_tmp_3" = psource)
    (length : lookupValue state.bindings "_verity_slice_tmp_19" = size)
    (bounded : destination + 32 * ((11 + size + 31) / 32) ≤ 2^64 - 1) :
    ∃ final, execStmtList oracle fields state segment = .continue final ∧
      Verity.Core.Model.Create2.physicalInitcodeBytes final.world destination (11 + size) =
        Verity.Core.Model.Create2.physicalInitcodeBytes
          ((state.world.copyPhysicalBytes state.world.physicalByte destination hsource 11).copyPhysicalBytes
            state.world.physicalByte (destination + 11) psource size) destination (11 + size) := by
  obtain ⟨allocated, final, allocation, run, code⟩ := execute_segment oracle fields state
    hsource psource destination size geometry pointer sizeValue header payload length bounded
  exact ⟨final, run, code.trans (original_snapshot oracle fields state allocated hsource psource destination size
    geometry headerPastPointer payloadPastPointer pointer sizeValue bounded allocation)⟩

end Contracts.SolidityImportSmoke.ImportedCreationOriginalSnapshots
