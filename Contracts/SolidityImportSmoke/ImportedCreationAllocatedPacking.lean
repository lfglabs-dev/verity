import Contracts.SolidityImportSmoke.ImportedCreationAllocator

namespace Contracts.SolidityImportSmoke.ImportedCreationAllocatedPacking
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration
open ImportedCreationCopySlices ImportedCreationPackingFrames

def copies : List Stmt := [ImportedCreationCopySlices.statement false, increment,
  ImportedCreationCopySlices.statement true]
def segment := ImportedCreationAllocator.segment ++ copies

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 78).take 10) = some segment := by rfl

structure Geometry (hsource psource destination size : Nat) : Prop where
  headerAligned : hsource % 32 = 0
  payloadAligned : psource % 32 = 0
  destinationAligned : destination % 32 = 0
  headerBefore : hsource + 11 ≤ destination
  payloadBefore : psource + size ≤ destination

structure Ready (state : DenoteState) (hsource psource destination size : Nat) : Prop where
  header : (inputs false hsource destination 0).Holds state
  payload : lookupValue state.bindings "_verity_slice_tmp_3" = psource
  count : lookupValue state.bindings "_verity_slice_tmp_19" = size
  coherent : Coherent state.world
  zero : ∀ index < 11 + size, state.world.physicalByte (destination + index) = zeroByte

/-- The real assignment preserves the complete frame used by copy invariants. -/
theorem increment_frame (oracle : DenoteOracle) (fields : List Field)
    (before after : DenoteState) (executed : execStmt oracle fields before increment = .continue after) :
    abiCopyFrame after = abiCopyFrame before := by
  unfold increment at executed
  cases evaluated : evalExpr oracle fields before
      (.add (.localVar "_verity_slice_tmp_26") (.literal 11)) with
  | none => simp [execStmt, evaluated] at executed
  | some value =>
    simp only [execStmt, evaluated] at executed
    cases executed
    rfl

/-- Rebase only the initial local binding change; no physical memory or
execution context may be replaced by this rule. -/
theorem invariant_rebase (inputs : AbiCopyInputs) (before ready final : DenoteState) (size : Nat)
    (world : ready.world = before.world) (frame : abiCopyFrame ready = abiCopyFrame before)
    (copied : AbiCopyLoopInvariant inputs ready size final) :
    AbiCopyLoopInvariant inputs before size final := by
  refine ⟨copied.1, ?_, copied.2.2.1, copied.2.2.2.trans frame⟩
  simpa only [world] using copied.2.1

/-- Derive the second loop's zero-area premise from the actual first loop. -/
theorem payload_zero (initial header ready : DenoteState) (hsource psource destination size : Nat)
    (conditions : Ready initial hsource psource destination size)
    (copied : AbiCopyLoopInvariant (inputs false hsource destination 0) initial 11 header)
    (world : ready.world = header.world) :
    ∀ index < size, abiMemoryByte ready.world.memory (destination + 11 + index) = 0 := by
  intro index inside
  rw [world]
  have zero : abiMemoryByte initial.world.memory (destination + 11 + index) = 0 := by
    rw [abiMemoryByte_physical initial.world _ conditions.coherent]
    have cleared := conditions.zero (11 + index) (by omega)
    simpa only [Nat.add_assoc, zeroByte] using congrArg Fin.val cleared
  simpa only [inputs, Nat.add_zero] using
    ImportedCreationPacking.header_preserves_zero (inputs false hsource destination 0)
      initial header 11 index copied (by simpa only [inputs, Nat.add_zero] using zero)

/-- Execute both real loops and the real intervening assignment. The final
code comes from original input snapshots, not a supplied desired poststate. -/
theorem execute_copies (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (hsource psource destination size : Nat)
    (geometry : Geometry hsource psource destination size)
    (range : destination + (11 + size) < Verity.Core.Uint256.modulus)
    (conditions : Ready state hsource psource destination size) :
    ∃ final, execStmtList oracle fields state copies = .continue final ∧
      Verity.Core.Model.Create2.physicalInitcodeBytes final.world destination (11 + size) =
        Verity.Core.Model.Create2.physicalInitcodeBytes
          ((state.world.copyPhysicalBytes state.world.physicalByte destination hsource 11).copyPhysicalBytes
            state.world.physicalByte (destination + 11) psource size) destination (11 + size) := by
  have hzero : ∀ index < 11, abiMemoryByte state.world.memory (destination + 0 + index) = 0 := by
    intro index inside
    rw [abiMemoryByte_physical state.world _ conditions.coherent]
    simpa only [Nat.add_zero, zeroByte] using congrArg Fin.val (conditions.zero index (by omega))
  obtain ⟨header, hrun, hcopy, _⟩ := actual_slice false oracle fields state hsource destination 0 11
    (by rfl) conditions.coherent conditions.header geometry.headerAligned geometry.destinationAligned
    (by have := geometry.headerBefore; have := range; omega)
    (by have := range; omega) (Or.inl (by simpa using geometry.headerBefore)) hzero
  obtain ⟨ready, advance, world, held, length⟩ := payload_inputs oracle fields state header hsource psource
    destination size hrun hcopy conditions.payload conditions.count
  have coherent : Coherent ready.world := by rw [world]; exact hcopy.2.2.1
  obtain ⟨final, prun, pcopy, _⟩ := actual_slice true oracle fields ready psource destination 11 size
    (congrArg some length) coherent held geometry.payloadAligned geometry.destinationAligned
    (by have := geometry.payloadBefore; have := range; omega) range
    (Or.inl (by have := geometry.payloadBefore; omega))
    (payload_zero state header ready hsource psource destination size conditions hcopy world)
  have rebased := invariant_rebase _ header ready final size world
    (increment_frame oracle fields header ready advance) pcopy
  have code := ImportedCreationPacking.packed_snapshot (inputs false hsource destination 0)
    (inputs true psource destination 11) state header final 11 size conditions.coherent hcopy rebased
    (by simp [inputs]) (Or.inl (by simpa [inputs] using geometry.payloadBefore))
  refine ⟨final, ?_, ?_⟩
  · simp only [copies, execStmtList, hrun, advance, prun]
  · simpa only [inputs, Nat.add_zero] using code

/-- Execute the actual ten-statement allocator/packing segment. In particular,
coherence, zeros and payload-start descriptors are not supplied as hypotheses. -/
theorem execute_segment (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (hsource psource destination size : Nat)
    (geometry : Geometry hsource psource destination size)
    (pointer : (state.world.memory 64).val = destination)
    (sizeValue : lookupValue state.bindings "_verity_slice_tmp_22" = 11 + size)
    (header : lookupValue state.bindings "_verity_slice_tmp_20" = hsource)
    (payload : lookupValue state.bindings "_verity_slice_tmp_3" = psource)
    (length : lookupValue state.bindings "_verity_slice_tmp_19" = size)
    (bounded : destination + 32 * ((11 + size + 31) / 32) ≤ 2^64 - 1) :
    ∃ allocated final,
      execStmtList oracle fields state ImportedCreationAllocator.segment = .continue allocated ∧
      execStmtList oracle fields state segment = .continue final ∧
      Verity.Core.Model.Create2.physicalInitcodeBytes final.world destination (11 + size) =
        Verity.Core.Model.Create2.physicalInitcodeBytes
          ((allocated.world.copyPhysicalBytes allocated.world.physicalByte destination hsource 11).copyPhysicalBytes
            allocated.world.physicalByte (destination + 11) psource size) destination (11 + size) := by
  obtain ⟨allocated, allocation, held, payload, length, coherent, zero⟩ :=
    ImportedCreationAllocator.inputs oracle fields state destination hsource psource size
      pointer sizeValue header payload length bounded
  have range : destination + (11 + size) < Verity.Core.Uint256.modulus := by
    have rounded := (abiPhysicalRoundedSize_bounds (11 + size)).1
    have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
    omega
  obtain ⟨final, executed, code⟩ := execute_copies oracle fields allocated hsource psource destination size
    geometry range ⟨held, payload, length, coherent, zero⟩
  refine ⟨allocated, final, allocation, ?_, code⟩
  rw [segment, SolidityImport.exec_append, allocation]
  exact executed

end Contracts.SolidityImportSmoke.ImportedCreationAllocatedPacking

