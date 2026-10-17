import Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadGeometry

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadAllocated
open EvmYul

theorem readback (original : ByteArray) (cost : Nat) (pre : EVM.State)
    (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (positive : 0 < (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat)
    (bounded : (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat < 2 ^ 64)
    (originalInside : c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat ≤ original.size)
    (inside : c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat ≤ (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size)
    (storePadding : (NativeSourceSecondPayload.output length d e).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (preserved : (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.readWithPadding c.toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat = original.readWithPadding c.toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat)
    (endBound : (e + length).toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat + d.toNat < 2 ^ 256)
    (above : g.toNat + 32 ≤ (NativeSourceSecondPayload.output length d e).toNat)
    (allocatorAbove : 96 ≤ (NativeSourceSecondPayload.output length d e).toNat) :
    (NativeSourcePackedAllocation.returned cost pre length b c d e f g dest x y tail).memory.readWithPadding (NativeSourceSecondPayload.output length d e).toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat = original.extract c.toNat (c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat) := by
  have padding : (NativeSourceSecondPayload.output length d e).toNat - (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits := by
    rw [NativeSourceIntercopyCarrier.loaded_size cost pre length b c d e f g dest x y tail storePadding]
    change ((e + length) + d).toNat - max _ (((e + length) + d).toNat + 32) < _
    rw [Nat.sub_eq_zero_of_le (Nat.le_trans (by omega) (Nat.le_max_right _ _))]
    exact Nat.two_pow_pos _
  have copiedInside := NativeSourceSecondPayloadGeometry.copy_inside (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory
    (NativeSourceSecondPayload.output length d e).toNat c.toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat positive inside padding
  have packedInside : (NativeSourceSecondPayload.output length d e).toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat ≤ (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size := copiedInside
  have finish := NativeSourceFieldGeometry.payload_boundary (e + length)
    (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail) d endBound
  have below : (NativeSourceSecondPayload.output length d e).toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat ≤ (NativeSourceFinalSizeContext.finish cost pre length b c d e f g dest x y tail).toNat := by
    exact Nat.le_of_eq finish
  have finalPadding : (NativeSourceFinalSizeContext.finish cost pre length b c d e f g dest x y tail).toNat - (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits := by
    rw [show (NativeSourceFinalSizeContext.finish cost pre length b c d e f g dest x y tail).toNat = (NativeSourceSecondPayload.output length d e).toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat from finish.symm]
    rw [Nat.sub_eq_zero_of_le packedInside]
    exact Nat.two_pow_pos _
  rw [NativeSourcePackedReturnFrame.preserve cost pre length b c d e f g dest x y tail
    (NativeSourceSecondPayload.output length d e).toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat
    finalPadding positive bounded copiedInside below above allocatorAbove]
  exact NativeSourceSecondPayload.readback original cost pre length b c d e f g dest x y tail
    positive bounded originalInside inside storePadding preserved

end Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadAllocated
