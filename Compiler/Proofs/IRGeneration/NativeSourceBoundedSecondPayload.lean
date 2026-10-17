import Compiler.Proofs.IRGeneration.NativeSourceAddressGeometry

namespace Compiler.Proofs.IRGeneration.NativeSourceBoundedSecondPayload
open EvmYul NativeSourceSecondPayload

theorem readback_return (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (bounded : (amount cost pre length b c d e f g dest x y tail).toNat < 2 ^ 64)
    (sourceInside : c.toNat + (amount cost pre length b c d e f g dest x y tail).toNat ≤ pre.memory.size)
    (padding : (output length d e).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (finalPadding : (NativeSourceFinalSizeContext.finish cost pre length b c d e f g dest x y tail).toNat -
      (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits)
    (endFits : ((e.toNat + length.toNat) +
      (amount cost pre length b c d e f g dest x y tail).toNat) + d.toNat < 2 ^ 256)
    (above : g.toNat + 32 ≤ (output length d e).toNat) (allocatorAbove : 96 ≤ (output length d e).toNat)
    (below : c.toNat + (amount cost pre length b c d e f g dest x y tail).toNat ≤ (output length d e).toNat) :
    (NativeSourcePackedAllocation.returned cost pre length b c d e f g dest x y tail).memory.readWithPadding
      (output length d e).toNat (amount cost pre length b c d e f g dest x y tail).toNat =
      pre.memory.extract c.toNat (c.toNat + (amount cost pre length b c d e f g dest x y tail).toNat) := by
  have finalBelow : (output length d e).toNat +
      (amount cost pre length b c d e f g dest x y tail).toNat ≤
      (NativeSourceFinalSizeContext.finish cost pre length b c d e f g dest x y tail).toNat :=
    NativeSourceAddressGeometry.final_bound e length d
      (amount cost pre length b c d e f g dest x y tail) endFits
  exact NativeSourceTotalSecondPayload.readback_return cost pre length b c d e f g dest x y tail
    bounded sourceInside padding finalPadding finalBelow above allocatorAbove below

end Compiler.Proofs.IRGeneration.NativeSourceBoundedSecondPayload
