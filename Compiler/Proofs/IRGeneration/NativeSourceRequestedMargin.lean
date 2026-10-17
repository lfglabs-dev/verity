import Compiler.Proofs.IRGeneration.NativeSourceRoundingArithmetic

namespace Compiler.Proofs.IRGeneration.NativeSourceRequestedMargin
open EvmYul

theorem requested_end (base size : UInt256)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩)
    (fits : size.toNat + 31 < 2 ^ 256) :
    base.toNat + size.toNat < 2 ^ 64 := by
  exact NativeSourceAllocatorMargin.margin_bound base size size.toNat guard
    (NativeSourceRoundingArithmetic.amount_covers size fits)

theorem copy_padding (base size : UInt256) (memory : ByteArray)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩)
    (fits : size.toNat + 31 < 2 ^ 256)
    (positive : 0 < size.toNat) (platform : 64 ≤ System.Platform.numBits) :
    (base + UInt256.ofNat 32).toNat - memory.size < 2 ^ System.Platform.numBits := by
  exact NativeSourceAllocatorMargin.copy_padding base size memory guard platform
    (NativeSourceRoundingArithmetic.positive_margin size fits positive)

theorem field_padding (base size : UInt256) (memory : ByteArray)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩)
    (fits : size.toNat + 31 < 2 ^ 256)
    (requested : 192 ≤ size.toNat) (platform : 64 ≤ System.Platform.numBits) :
    (base + UInt256.ofNat 192).toNat - memory.size < 2 ^ System.Platform.numBits := by
  have bound := requested_end base size guard fits
  have small : base.toNat + 192 < 2 ^ 64 := by omega
  apply NativeSourceBoundedPadding.field_padding base memory
  · exact small.trans_le (Nat.pow_le_pow_right (by decide) platform)
  · have large : 2 ^ 64 < 2 ^ 256 := by decide
    omega

end Compiler.Proofs.IRGeneration.NativeSourceRequestedMargin
