import Compiler.Proofs.IRGeneration.NativeSourceFirstCopySourceWindow

namespace Compiler.Proofs.IRGeneration.NativeSourceTwoCopySecondPayload
open EvmYul

theorem readback (cost : Nat) (pre : EVM.State)
    (length a b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (firstSource : a.toNat + length.toNat ≤ pre.memory.size)
    (firstPadding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (bounded : (NativeSourceSecondPayload.amount cost (NativeSourceFirstPayloadSurvival.first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).toNat < 2 ^ 64)
    (sourceInside : c.toNat + (NativeSourceSecondPayload.amount cost (NativeSourceFirstPayloadSurvival.first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).toNat ≤ pre.memory.size)
    (storePadding : (NativeSourceSecondPayload.output length d e).toNat - (NativeSourceFirstPayloadSurvival.first cost pre length a b c d e f g dest (x :: y :: tail)).memory.size < 2 ^ System.Platform.numBits)
    (firstBelow : c.toNat + (NativeSourceSecondPayload.amount cost (NativeSourceFirstPayloadSurvival.first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).toNat ≤ dest.toNat)
    (below : c.toNat + (NativeSourceSecondPayload.amount cost (NativeSourceFirstPayloadSurvival.first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).toNat ≤ (NativeSourceSecondPayload.output length d e).toNat)
    (endBound : (e + length).toNat + (NativeSourceSecondPayload.amount cost (NativeSourceFirstPayloadSurvival.first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).toNat + d.toNat < 2 ^ 256)
    (above : g.toNat + 32 ≤ (NativeSourceSecondPayload.output length d e).toNat)
    (allocatorAbove : 96 ≤ (NativeSourceSecondPayload.output length d e).toNat) :
    (NativeSourcePackedAllocation.returned cost (NativeSourceFirstPayloadSurvival.first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).memory.readWithPadding (NativeSourceSecondPayload.output length d e).toNat (NativeSourceSecondPayload.amount cost (NativeSourceFirstPayloadSurvival.first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).toNat = pre.memory.extract c.toNat (c.toNat + (NativeSourceSecondPayload.amount cost (NativeSourceFirstPayloadSurvival.first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).toNat) := by
  have preserved := NativeSourceFirstCopySourceWindow.first_read_below cost pre length a b c d e f g dest (x :: y :: tail)
    c.toNat (NativeSourceSecondPayload.amount cost (NativeSourceFirstPayloadSurvival.first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).toNat firstSource firstPadding bounded sourceInside firstBelow
  have inside := sourceInside.trans (NativeSourcePayloadReturn.copy_monotone pre.memory dest.toNat a.toNat length.toNat firstSource firstPadding)
  exact NativeSourceSecondPayloadOriginalTotal.readback pre.memory cost (NativeSourceFirstPayloadSurvival.first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail
    bounded sourceInside inside storePadding preserved below endBound above allocatorAbove

end Compiler.Proofs.IRGeneration.NativeSourceTwoCopySecondPayload
