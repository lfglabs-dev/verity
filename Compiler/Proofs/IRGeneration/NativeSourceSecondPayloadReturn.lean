import Compiler.Proofs.IRGeneration.NativeSourceSecondSourceFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadReturn
open EvmYul NativeSourceSecondPayload

theorem copied_inside (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (positive : 0 < (amount cost pre length b c d e f g dest x y tail).toNat)
    (sourceInside : c.toNat + (amount cost pre length b c d e f g dest x y tail).toNat ≤ pre.memory.size)
    (padding : (output length d e).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (output length d e).toNat + (amount cost pre length b c d e f g dest x y tail).toNat ≤ (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size := by
  have inside := sourceInside.trans (NativeSourceSecondPackingFrame.loaded_monotone cost pre length b c d e f g dest x y tail padding)
  have copyPadding : (output length d e).toNat - (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits := by
    rw [NativeSourceIntercopyCarrier.loaded_size cost pre length b c d e f g dest x y tail padding]
    change ((e + length) + d).toNat - max _ (((e + length) + d).toNat + 32) < _
    rw [Nat.sub_eq_zero_of_le (Nat.le_trans (by omega) (Nat.le_max_right _ _))]
    exact Nat.two_pow_pos _
  change (output length d e).toNat + (amount cost pre length b c d e f g dest x y tail).toNat ≤ ((NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.write c.toNat (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory (output length d e).toNat (amount cost pre length b c d e f g dest x y tail).toNat).size
  rw [NativeSourceMcopyGrowth.write_snapshot _ _ _ _ positive inside copyPadding]
  rw [ByteArray.size_write _ _ _ _ positive (by rw [ByteArray.size_extract]; omega) copyPadding]
  exact Nat.le_max_right _ _

theorem readback_return (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (positive : 0 < (amount cost pre length b c d e f g dest x y tail).toNat)
    (bounded : (amount cost pre length b c d e f g dest x y tail).toNat < 2 ^ 64)
    (sourceInside : c.toNat + (amount cost pre length b c d e f g dest x y tail).toNat ≤ pre.memory.size)
    (padding : (output length d e).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (finalPadding : (NativeSourceFinalSizeContext.finish cost pre length b c d e f g dest x y tail).toNat -
      (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits)
    (finalBelow : (output length d e).toNat + (amount cost pre length b c d e f g dest x y tail).toNat ≤
      (NativeSourceFinalSizeContext.finish cost pre length b c d e f g dest x y tail).toNat)
    (above : g.toNat + 32 ≤ (output length d e).toNat) (allocatorAbove : 96 ≤ (output length d e).toNat)
    (below : c.toNat + (amount cost pre length b c d e f g dest x y tail).toNat ≤ (output length d e).toNat) :
    (NativeSourcePackedAllocation.returned cost pre length b c d e f g dest x y tail).memory.readWithPadding
      (output length d e).toNat (amount cost pre length b c d e f g dest x y tail).toNat =
      pre.memory.extract c.toNat (c.toNat + (amount cost pre length b c d e f g dest x y tail).toNat) := by
  have finalInside := copied_inside cost pre length b c d e f g dest x y tail positive sourceInside padding
  rw [NativeSourcePackedReturnFrame.preserve cost pre length b c d e f g dest x y tail
    (output length d e).toNat (amount cost pre length b c d e f g dest x y tail).toNat finalPadding positive bounded finalInside finalBelow above allocatorAbove]
  exact NativeSourceSecondSourceFrame.readback cost pre length b c d e f g dest x y tail positive bounded sourceInside padding below

end Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadReturn
