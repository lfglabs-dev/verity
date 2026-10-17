import Compiler.Proofs.IRGeneration.NativeSourceGeometricFree
namespace Compiler.Proofs.IRGeneration.NativeSourceAcceptedFree
open EvmYul
theorem free_bound (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (platform : 7 ≤ System.Platform.numBits)
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (sd : d.toNat < 2 ^ 64) (se : e.toNat < 2 ^ 64)
    (sf : f.toNat < 2 ^ 64) (sg : g.toNat < 2 ^ 64)
    (fields : c.toNat + 288 < 2 ^ 64)
    (guard : NativeSourceAllocatorDecision.flag j (b - c) = ⟨0⟩) :
    (NativeSourceDecodedPackingStart.free cost
      (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail)).toNat < 2 ^ 64 := by
  rw [NativeSourceGeometricFree.context_free cost pre a b c d e f g h i j k tail
    platform upper sd se sf sg fields (NativeSourceAllocatorMargin.base_bound j (b - c) guard)]
  exact (NativeSourceAllocatorAcceptedBounds.natural_bounds j (b - c) guard).1

end Compiler.Proofs.IRGeneration.NativeSourceAcceptedFree
