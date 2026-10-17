import Compiler.Proofs.IRGeneration.CreationMemoryLayout
import Verity.Core.Model.PhysicalCopy

namespace Compiler.Proofs.IRGeneration.CreationRelocatedCopies
open Verity.Core.Model Compiler.CompilationModel.DenoteMemory CreationMemoryFrames

/-- Equality of the bytes read by CREATE2 permits distinct base pointers. -/
theorem relocated_slice (left right : Verity.ContractState) (loffset roffset size : Nat)
    (same : ∀ index < size, left.physicalByte (loffset + index) =
      right.physicalByte (roffset + index)) :
    Create2.physicalInitcodeBytes left loffset size =
      Create2.physicalInitcodeBytes right roffset size := by
  apply congrArg (fun values : List UInt8 => (⟨values.toArray⟩ : ByteArray))
  apply List.map_congr_left
  intro index belongs
  exact congrArg (fun byte : Byte => UInt8.ofNat byte.val)
    (same index (List.mem_range.mp belongs))

/-- Two independently executed byte copies derive equal code, without assuming
post-copy slice equality or equal initial memories. Zero length is included. -/
theorem copied_slice (left right : Verity.ContractState) (lsource rsource : Nat → Byte)
    (loffset roffset lstart rstart size : Nat)
    (same : ∀ index < size, lsource (lstart + index) = rsource (rstart + index)) :
    Create2.physicalInitcodeBytes
        (left.copyPhysicalBytes lsource loffset lstart size) loffset size =
      Create2.physicalInitcodeBytes
        (right.copyPhysicalBytes rsource roffset rstart size) roffset size := by
  apply relocated_slice
  intro index bound
  rw [Verity.ContractState.copyPhysicalBytes_at _ _ _ _ _ ⟨index, bound⟩,
    Verity.ContractState.copyPhysicalBytes_at _ _ _ _ _ ⟨index, bound⟩]
  exact same index bound

/-- Appending a payload preserves every previously written header byte. -/
theorem appended_header (world : Verity.ContractState) (header payload : Nat → Byte)
    (offset hstart pstart hsize psize index : Nat) (bound : index < hsize) :
    ((world.copyPhysicalBytes header offset hstart hsize).copyPhysicalBytes
      payload (offset + hsize) pstart psize).physicalByte (offset + index) =
        header (hstart + index) := by
  rw [Verity.ContractState.copyPhysicalBytes_outside _ _ _ _ _ _ (Or.inl (by omega))]
  exact Verity.ContractState.copyPhysicalBytes_at _ _ _ _ _ ⟨index, bound⟩

/-- Actual header-then-payload copies at different pointers yield equal entire
initcodes. Both parts are arbitrary; neither final memory is supplied. -/
theorem packed_slice (left right : Verity.ContractState)
    (lh rh lp rp : Nat → Byte) (loffset roffset lhstart rhstart lpstart rpstart hsize psize : Nat)
    (header : ∀ index < hsize, lh (lhstart + index) = rh (rhstart + index))
    (payload : ∀ index < psize, lp (lpstart + index) = rp (rpstart + index)) :
    Create2.physicalInitcodeBytes
      ((left.copyPhysicalBytes lh loffset lhstart hsize).copyPhysicalBytes
        lp (loffset + hsize) lpstart psize) loffset (hsize + psize) =
    Create2.physicalInitcodeBytes
      ((right.copyPhysicalBytes rh roffset rhstart hsize).copyPhysicalBytes
        rp (roffset + hsize) rpstart psize) roffset (hsize + psize) := by
  apply relocated_slice
  intro index bound
  by_cases head : index < hsize
  · rw [appended_header _ _ _ _ _ _ _ _ _ head, appended_header _ _ _ _ _ _ _ _ _ head]
    exact header index head
  · have tail : index - hsize < psize := by omega
    have leftAddress : loffset + index = (loffset + hsize) + (index - hsize) := by omega
    have rightAddress : roffset + index = (roffset + hsize) + (index - hsize) := by omega
    rw [leftAddress, rightAddress,
      Verity.ContractState.copyPhysicalBytes_at _ _ _ _ _ ⟨index - hsize, tail⟩,
      Verity.ContractState.copyPhysicalBytes_at _ _ _ _ _ ⟨index - hsize, tail⟩]
    exact payload (index - hsize) tail

/-- The ABI encoder's trailing zero word cannot change the initcode slice. -/
theorem trailing_word_slice (world : Verity.ContractState) (offset size : Nat)
    (value : Verity.Core.Uint256) :
    Create2.physicalInitcodeBytes
      (world.writePhysicalMemoryValue (offset + size) value) offset size =
      Create2.physicalInitcodeBytes world offset size := by
  apply relocated_slice
  intro index bound
  exact Compiler.CompilationModel.PhysicalMemory.writePhysicalMemoryValue_byte_outside _ _ _ _
    (Or.inl (by omega))

end Compiler.Proofs.IRGeneration.CreationRelocatedCopies

