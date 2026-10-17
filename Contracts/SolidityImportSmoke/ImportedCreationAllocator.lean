import Contracts.SolidityImportSmoke.ImportedCreationPackingFrames
import Compiler.Proofs.IRGeneration.ImportedLocalFrames

namespace Contracts.SolidityImportSmoke.ImportedCreationAllocator
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration

def allocation : List Stmt := SolidityImport.AbiEncoding.packedBuffer
  "_verity_slice_tmp_23" "_verity_slice_tmp_24" "_verity_slice_tmp_25" (.localVar "_verity_slice_tmp_22")

def segment : List Stmt := allocation ++ [.letVar "_verity_slice_tmp_26" (.literal 0)]

/-- Exactly the six allocator statements followed by the initial start binding. -/
theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 78).take 7) = some segment := by rfl

/-- Actual allocator execution preserves all original buffer descriptors and
payload size. Only the allocator's own fresh names can change. -/
theorem binding_frame (oracle : DenoteOracle) (fields : List Field)
    (initial final : DenoteState) (key : String)
    (allowed : key = "_verity_slice_tmp_3" ∨ key = "_verity_slice_tmp_19" ∨
      key = "_verity_slice_tmp_20" ∨ key = "_verity_slice_tmp_22")
    (executed : execStmtList oracle fields initial segment = .continue final) :
    lookupValue final.bindings key = lookupValue initial.bindings key := by
  have safe : ImportedLocalFrames.safeList key segment = true := by
    rcases allowed with rfl | rfl | rfl | rfl <;> decide
  have result := ImportedLocalFrames.list_frame oracle fields key segment safe initial
  simpa only [ImportedLocalFrames.preserves, executed] using result

/-- Execute the actual allocator/start segment. Complete physical clearing,
coherence, destination and start descriptors are derived, not poststate inputs. -/
theorem execute (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (base size : Nat)
    (pointer : (state.world.memory 64).val = base)
    (sizeValue : lookupValue state.bindings "_verity_slice_tmp_22" = size)
    (bounded : base + 32 * ((size + 31) / 32) ≤ 2^64 - 1) :
    ∃ ready, execStmtList oracle fields state segment = .continue ready ∧
      lookupValue ready.bindings "_verity_slice_tmp_23" = base ∧
      lookupValue ready.bindings "_verity_slice_tmp_26" = 0 ∧ Coherent ready.world ∧
      (∀ index < size, ready.world.physicalByte (base + index) = zeroByte) := by
  obtain ⟨after, ran, dest, memory, coherent⟩ := execStmtList_packedBuffer_coherent oracle fields state
    "_verity_slice_tmp_23" "_verity_slice_tmp_24" "_verity_slice_tmp_25" "_verity_slice_tmp_22"
    base size pointer sizeValue (by decide) (by decide) (by decide) (by decide) bounded
  let ready : DenoteState := { after with bindings := bindValue after.bindings "_verity_slice_tmp_26" 0 }
  refine ⟨ready, ?_, ?_, ?_, coherent, ?_⟩
  · rw [segment, SolidityImport.exec_append, allocation, ran]
    rfl
  · simpa only [ready, SolidityImport.lookup_bind_other _ _ _ _
      (by decide : "_verity_slice_tmp_26" ≠ "_verity_slice_tmp_23")] using dest
  · exact SolidityImport.lookup_bind_same _ _ _
  · intro index inside
    change after.world.physicalByte (base + index) = zeroByte
    rw [memory, abiClearPhysicalWorld_byte, if_pos (by have := (abiPhysicalRoundedSize_bounds size).1; omega)]

/-- The allocator also derives the original header and payload descriptors.
This combines actual execution with the checked non-clobbering certificate. -/
theorem inputs (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (base hsource psource size : Nat)
    (pointer : (state.world.memory 64).val = base)
    (sizeValue : lookupValue state.bindings "_verity_slice_tmp_22" = 11 + size)
    (header : lookupValue state.bindings "_verity_slice_tmp_20" = hsource)
    (payload : lookupValue state.bindings "_verity_slice_tmp_3" = psource)
    (length : lookupValue state.bindings "_verity_slice_tmp_19" = size)
    (bounded : base + 32 * ((11 + size + 31) / 32) ≤ 2^64 - 1) :
    ∃ ready, execStmtList oracle fields state segment = .continue ready ∧
      (ImportedCreationCopySlices.inputs false hsource base 0).Holds ready ∧
      lookupValue ready.bindings "_verity_slice_tmp_3" = psource ∧
      lookupValue ready.bindings "_verity_slice_tmp_19" = size ∧ Coherent ready.world ∧
      (∀ index < 11 + size, ready.world.physicalByte (base + index) = zeroByte) := by
  obtain ⟨ready, ran, dest, start, coherent, zero⟩ := execute oracle fields state base (11 + size)
    pointer sizeValue bounded
  refine ⟨ready, ran, ?_, ?_, ?_, coherent, zero⟩
  · exact ⟨(binding_frame oracle fields state ready _ (Or.inr (Or.inr (Or.inl rfl))) ran).trans header, dest, start⟩
  · exact (binding_frame oracle fields state ready _ (Or.inl rfl) ran).trans payload
  · exact (binding_frame oracle fields state ready _ (Or.inr (Or.inl rfl)) ran).trans length

end Contracts.SolidityImportSmoke.ImportedCreationAllocator
