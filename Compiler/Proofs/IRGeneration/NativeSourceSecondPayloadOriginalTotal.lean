import Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadAllocated
import Compiler.Proofs.IRGeneration.NativeSourceEmptyPayload

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadOriginalTotal
open EvmYul

theorem readback (original : ByteArray) (cost : Nat) (pre : EVM.State)
    (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (bounded : (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat < 2 ^ 64)
    (originalInside : c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat ≤ original.size)
    (sourceInside : c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat ≤ pre.memory.size)
    (storePadding : (NativeSourceSecondPayload.output length d e).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (preserved : pre.memory.readWithPadding c.toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat = original.readWithPadding c.toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat)
    (below : c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat ≤ (NativeSourceSecondPayload.output length d e).toNat)
    (endBound : (e + length).toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat + d.toNat < 2 ^ 256)
    (above : g.toNat + 32 ≤ (NativeSourceSecondPayload.output length d e).toNat)
    (allocatorAbove : 96 ≤ (NativeSourceSecondPayload.output length d e).toNat) :
    (NativeSourcePackedAllocation.returned cost pre length b c d e f g dest x y tail).memory.readWithPadding (NativeSourceSecondPayload.output length d e).toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat = original.extract c.toNat (c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat) := by
  by_cases zero : (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat = 0
  · rw [zero, NativeSourceEmptyPayload.read_zero, NativeSourceEmptyPayload.extract_zero]
  · have positive : 0 < (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat := by omega
    have inside := sourceInside.trans (NativeSourceSecondPackingFrame.loaded_monotone cost pre length b c d e f g dest x y tail storePadding)
    have frame := NativeSourceIntercopyStoreFrame.loaded_read_below cost pre length b c d e f g dest x y tail
      c.toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat storePadding positive bounded sourceInside below
    exact NativeSourceSecondPayloadAllocated.readback original cost pre length b c d e f g dest x y tail
      positive bounded originalInside inside storePadding (frame.trans preserved) endBound above allocatorAbove

end Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadOriginalTotal
