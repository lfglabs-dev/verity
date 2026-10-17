import Compiler.Proofs.IRGeneration.NativeSourceFieldAddressBounds
namespace Compiler.Proofs.IRGeneration.NativeSourceGeometricFree
open EvmYul
theorem context_free (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (platform : 7 ≤ System.Platform.numBits)
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (sd : d.toNat < 2 ^ 64) (se : e.toNat < 2 ^ 64)
    (sf : f.toNat < 2 ^ 64) (sg : g.toNat < 2 ^ 64)
    (fields : c.toNat + 288 < 2 ^ 64) (sizeAddress : j.toNat < 2 ^ 64) :
    NativeSourceDecodedPackingStart.free cost
      (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail) =
      j + NativeSourceAllocatorOverflowEntry.amount (b - c) := by
  obtain ⟨d1, d2, d3, d4⟩ := NativeSourceFieldAddressBounds.field_bounds c fields
  exact NativeSourceOriginalFree.context_free cost pre a b c d e f g h i j k tail
    platform upper sd se sf sg d1 d2 d3 d4 sizeAddress

theorem fields_from_allocator (base size : UInt256)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩)
    (fits : size.toNat + 31 < 2 ^ 256) (requested : 288 ≤ size.toNat) :
    base.toNat + 288 < 2 ^ 64 := by
  have bound := NativeSourceRequestedMargin.requested_end base size guard fits
  omega

end Compiler.Proofs.IRGeneration.NativeSourceGeometricFree

