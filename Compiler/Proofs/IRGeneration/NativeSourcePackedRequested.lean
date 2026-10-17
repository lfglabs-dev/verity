import Compiler.Proofs.IRGeneration.NativeSourceRequestedGeometry

namespace Compiler.Proofs.IRGeneration.NativeSourcePackedRequested
open EvmYul

abbrev amount (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) :=
  (NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b

theorem size_value (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (fits : ((e.toNat + length.toNat) + (amount cost pre length b c d e f g dest x y tail).toNat) + d.toNat < 2 ^ 256) :
    (NativeSourcePackedAllocation.size cost pre length b c d e f g dest x y tail).toNat =
      length.toNat + (amount cost pre length b c d e f g dest x y tail).toNat + d.toNat := by
  exact NativeSourceRequestedGeometry.requested_toNat e length _ d fits

theorem size_positive (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (fits : ((e.toNat + length.toNat) + (amount cost pre length b c d e f g dest x y tail).toNat) + d.toNat < 2 ^ 256)
    (gap : 0 < d.toNat) :
    0 < (NativeSourcePackedAllocation.size cost pre length b c d e f g dest x y tail).toNat := by
  rw [size_value cost pre length b c d e f g dest x y tail fits]
  omega

theorem size_rounding_fits (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (endBound : (((e.toNat + length.toNat) + (amount cost pre length b c d e f g dest x y tail).toNat) + d.toNat) + 31 < 2 ^ 256) :
    (NativeSourcePackedAllocation.size cost pre length b c d e f g dest x y tail).toNat + 31 < 2 ^ 256 := by
  rw [size_value cost pre length b c d e f g dest x y tail (by omega)]
  omega

theorem copy_padding (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (memory : ByteArray)
    (endBound : (((e.toNat + length.toNat) + (amount cost pre length b c d e f g dest x y tail).toNat) + d.toNat) + 31 < 2 ^ 256)
    (gap : 0 < d.toNat) (platform : 64 ≤ System.Platform.numBits)
    (guard : NativeSourceAllocatorDecision.flag g
      (NativeSourcePackedAllocation.size cost pre length b c d e f g dest x y tail) = ⟨0⟩) :
    (g + UInt256.ofNat 32).toNat - memory.size < 2 ^ System.Platform.numBits := by
  apply NativeSourceRequestedMargin.copy_padding g
    (NativeSourcePackedAllocation.size cost pre length b c d e f g dest x y tail) memory guard
  · exact size_rounding_fits cost pre length b c d e f g dest x y tail endBound
  · exact size_positive cost pre length b c d e f g dest x y tail (by omega) gap
  · exact platform

end Compiler.Proofs.IRGeneration.NativeSourcePackedRequested

