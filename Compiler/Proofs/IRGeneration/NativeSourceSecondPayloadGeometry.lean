import Compiler.Proofs.IRGeneration.NativeSourceFieldGeometry
import Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadSized

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadGeometry
open EvmYul

theorem copy_inside (memory : ByteArray) (dest source size : Nat)
    (positive : 0 < size) (input : source + size ≤ memory.size)
    (padding : dest - memory.size < 2 ^ System.Platform.numBits) :
    dest + size ≤ (memory.write source memory dest size).size := by
  rw [NativeSourceMcopyGrowth.write_snapshot memory dest source size positive input padding]
  have snapshot : (memory.extract source (source + size)).size = size := by
    rw [ByteArray.size_extract]
    omega
  rw [ByteArray.size_write _ memory dest size positive snapshot padding]
  exact Nat.le_max_right _ _

theorem readback (original : ByteArray) (cost : Nat) (pre : EVM.State)
    (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (positive : 0 < (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat)
    (bounded : (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat < 2 ^ 64)
    (originalInside : c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat ≤ original.size)
    (inside : c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat ≤ (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size)
    (storePadding : (NativeSourceSecondPayload.output length d e).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (preserved : (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.readWithPadding c.toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat = original.readWithPadding c.toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat)
    (endBound : (e + length).toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat + d.toNat < 2 ^ 256) :
    (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail).memory.readWithPadding (NativeSourceSecondPayload.output length d e).toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat = original.extract c.toNat (c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat) := by
  have padding : (NativeSourceSecondPayload.output length d e).toNat - (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits := by
    rw [NativeSourceIntercopyCarrier.loaded_size cost pre length b c d e f g dest x y tail storePadding]
    change ((e + length) + d).toNat - max _ (((e + length) + d).toNat + 32) < _
    rw [Nat.sub_eq_zero_of_le (Nat.le_trans (by omega) (Nat.le_max_right _ _))]
    exact Nat.two_pow_pos _
  have copiedInside := copy_inside (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory
    (NativeSourceSecondPayload.output length d e).toNat c.toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat positive inside padding
  have finish := NativeSourceFieldGeometry.payload_boundary (e + length)
    (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail) d endBound
  exact NativeSourceSecondPayloadSized.readback original cost pre length b c d e f g dest x y tail
    positive bounded originalInside inside storePadding preserved copiedInside finish.symm

end Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadGeometry

