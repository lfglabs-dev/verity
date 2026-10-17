import Compiler.Proofs.IRGeneration.IRRuntimeTypes

namespace Compiler.Proofs.IRGeneration.PhysicalCopyRevert
open Compiler.CompilationModel.DenoteMemory

/-- Every captured byte comes from the actual copy, including copies into
nonempty memory. This is a physical-memory law, not a fuel adequacy claim. -/
theorem copied_byte (state : IRState) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) (index : Fin size) :
    ((state.copyPhysicalBytes source destOffset sourceOffset size).captureRevert
      destOffset size).byteMemory.readByte (destOffset + index.val) =
      source (sourceOffset + index.val) := by
  rw [IRState.captureRevert_memory, IRState.copyPhysicalBytes_byteMemory]
  exact Memory.readByte_copyFrom_at _ _ _ _ _ index

/-- Capturing precisely the copied extent observes precisely its source bytes.
Zero-length copies still produce an observed empty REVERT, distinct from an
interpreter failure with no observation. -/
theorem copied_payload (state : IRState) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) :
    ((state.copyPhysicalBytes source destOffset sourceOffset size).captureRevert
      destOffset size).revertBytes =
      some ((List.range size).map (fun index =>
        UInt8.ofNat (source (sourceOffset + index)).val)) := by
  simp only [IRState.revertBytes, IRState.captureRevert_observed, Option.map_some]
  congr 1
  apply List.map_congr_left
  intro index member
  have bound : index < size := List.mem_range.mp member
  rw [copied_byte state source destOffset sourceOffset size ⟨index, bound⟩]

theorem returndata_payload (state : IRState) :
    ((state.copyPhysicalReturndata 0 0 (32 * state.returndata.length)).captureRevert
      0 (32 * state.returndata.length)).revertBytes =
      some ((List.range (32 * state.returndata.length)).map (fun index =>
        UInt8.ofNat (wordListByte state.returndata index).val)) := by
  simpa only [IRState.copyPhysicalReturndata, Nat.zero_add] using
    copied_payload state (wordListByte state.returndata) 0 0 (32 * state.returndata.length)

end Compiler.Proofs.IRGeneration.PhysicalCopyRevert
