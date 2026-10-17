import Compiler.Proofs.IRGeneration.CreationRelocatedCopies

namespace Compiler.Proofs.IRGeneration.CreationPackedBytes
open Compiler.CompilationModel DenoteMemory
open Verity.Core.Model

/-- Every byte in a physical slice is included exactly once, in order. -/
theorem slice_append (world : Verity.ContractState) (offset first second : Nat) :
    Create2.physicalInitcodeBytes world offset (first + second) =
      Create2.physicalInitcodeBytes world offset first ++
        Create2.physicalInitcodeBytes world (offset + first) second := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [Create2.physicalInitcodeBytes, ByteArray.data_append, Array.toList_append,
    List.toList_toArray, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro index _
  simp only [Function.comp_apply, Nat.add_assoc]

/-- Snapshot copying reads exact original bytes even when output layouts differ. -/
theorem copied_code (world : Verity.ContractState) (header payload : Nat → Byte)
    (destination hstart pstart hsize psize : Nat) :
    Create2.physicalInitcodeBytes
      ((world.copyPhysicalBytes header destination hstart hsize).copyPhysicalBytes
        payload (destination + hsize) pstart psize) destination (hsize + psize) =
      (⟨((List.range hsize).map fun index => UInt8.ofNat (header (hstart + index)).val).toArray⟩ : ByteArray) ++
      (⟨((List.range psize).map fun index => UInt8.ofNat (payload (pstart + index)).val).toArray⟩ : ByteArray) := by
  rw [slice_append]
  congr 1
  · apply congrArg (fun bytes : List UInt8 => (⟨bytes.toArray⟩ : ByteArray))
    apply List.map_congr_left
    intro index inside
    rw [CreationRelocatedCopies.appended_header _ _ _ _ _ _ _ _ _ (List.mem_range.mp inside)]
  · apply congrArg (fun bytes : List UInt8 => (⟨bytes.toArray⟩ : ByteArray))
    apply List.map_congr_left
    intro index inside
    rw [Verity.ContractState.copyPhysicalBytes_at _ _ _ _ _ ⟨index, List.mem_range.mp inside⟩]

end Compiler.Proofs.IRGeneration.CreationPackedBytes
