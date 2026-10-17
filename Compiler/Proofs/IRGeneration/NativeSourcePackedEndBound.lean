import Compiler.Proofs.IRGeneration.NativeSourceOriginalContainedReturn

namespace Compiler.Proofs.IRGeneration.NativeSourcePackedEndBound
open EvmYul NativeSourcePackedRequested

theorem natural_end (cost : Nat) (pre : EVM.State) (length b c d base f dest x y : UInt256)
    (tail : Stack UInt256)
    (endFits : (((base.toNat + length.toNat) + (amount cost pre length b c d base f base dest x y tail).toNat) + d.toNat) + 31 < 2 ^ 256)
    (guard : NativeSourceAllocatorDecision.flag base
      (NativeSourcePackedAllocation.size cost pre length b c d base f base dest x y tail) = ⟨0⟩) :
    ((base.toNat + length.toNat) + (amount cost pre length b c d base f base dest x y tail).toNat) + d.toNat < 2 ^ 64 := by
  have requested := NativeSourceRequestedMargin.requested_end base
    (NativeSourcePackedAllocation.size cost pre length b c d base f base dest x y tail) guard
    (size_rounding_fits cost pre length b c d base f base dest x y tail endFits)
  rw [size_value cost pre length b c d base f base dest x y tail (by omega)] at requested
  omega

theorem finish_value (cost : Nat) (pre : EVM.State) (length b c d base f dest x y : UInt256)
    (tail : Stack UInt256)
    (fits : ((base.toNat + length.toNat) + (amount cost pre length b c d base f base dest x y tail).toNat) + d.toNat < 2 ^ 256) :
    (NativeSourceFinalSizeContext.finish cost pre length b c d base f base dest x y tail).toNat =
      ((base.toNat + length.toNat) + (amount cost pre length b c d base f base dest x y tail).toNat) + d.toNat := by
  have first := NativeSourceAddressGeometry.add_toNat base length (by omega)
  have second := NativeSourceAddressGeometry.add_toNat (base + length)
    (amount cost pre length b c d base f base dest x y tail) (by omega)
  change (((base + length) + amount cost pre length b c d base f base dest x y tail) + d).toNat = _
  rw [NativeSourceAddressGeometry.add_toNat _ d (by omega), second, first]

theorem final_padding (cost : Nat) (pre : EVM.State) (length b c d base f dest x y : UInt256)
    (tail : Stack UInt256) (memory : ByteArray) (platform : 64 ≤ System.Platform.numBits)
    (endFits : (((base.toNat + length.toNat) + (amount cost pre length b c d base f base dest x y tail).toNat) + d.toNat) + 31 < 2 ^ 256)
    (guard : NativeSourceAllocatorDecision.flag base
      (NativeSourcePackedAllocation.size cost pre length b c d base f base dest x y tail) = ⟨0⟩) :
    (NativeSourceFinalSizeContext.finish cost pre length b c d base f base dest x y tail).toNat - memory.size <
      2 ^ System.Platform.numBits := by
  have bound := natural_end cost pre length b c d base f dest x y tail endFits guard
  have value := finish_value cost pre length b c d base f dest x y tail (by omega)
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  exact NativeSourceBoundedPadding.padding_of_address _ _ (by omega)

end Compiler.Proofs.IRGeneration.NativeSourcePackedEndBound

