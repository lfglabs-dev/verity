import Compiler.Proofs.IRGeneration.NativeSourceAllocatorAcceptedBounds

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorMargin
open EvmYul NativeSourceAllocatorOverflowEntry

theorem base_bound (base size : UInt256)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩) :
    base.toNat < 2 ^ 64 := by
  have bound := NativeSourceAllocatorAcceptedBounds.sum_bound base size guard
  omega

theorem margin_bound (base size : UInt256) (extra : Nat)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩)
    (margin : extra ≤ (amount size).toNat) :
    base.toNat + extra < 2 ^ 64 := by
  have bound := NativeSourceAllocatorAcceptedBounds.sum_bound base size guard
  omega

theorem copy_padding (base size : UInt256) (memory : ByteArray)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩)
    (platform : 64 ≤ System.Platform.numBits)
    (margin : 32 ≤ (amount size).toNat) :
    (base + UInt256.ofNat 32).toNat - memory.size < 2 ^ System.Platform.numBits := by
  have bounded := margin_bound base size 32 guard margin
  apply NativeSourceBoundedPadding.copy_padding base memory
  · exact bounded.trans_le (Nat.pow_le_pow_right (by decide) platform)
  · have large : 2 ^ 64 < 2 ^ 256 := by decide
    omega

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorMargin
