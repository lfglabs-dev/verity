import Compiler.Proofs.IRGeneration.NativeSourceSecondPayload

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondSourceFrame
open EvmYul NativeSourceSecondPayload

theorem readback (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (positive : 0 < (amount cost pre length b c d e f g dest x y tail).toNat)
    (bounded : (amount cost pre length b c d e f g dest x y tail).toNat < 2 ^ 64)
    (sourceInside : c.toNat + (amount cost pre length b c d e f g dest x y tail).toNat ≤ pre.memory.size)
    (padding : (output length d e).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (below : c.toNat + (amount cost pre length b c d e f g dest x y tail).toNat ≤ (output length d e).toNat) :
    (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.readWithPadding
      (output length d e).toNat (amount cost pre length b c d e f g dest x y tail).toNat =
      pre.memory.extract c.toNat (c.toNat + (amount cost pre length b c d e f g dest x y tail).toNat) := by
  have insideLoaded := sourceInside.trans
    (NativeSourceSecondPackingFrame.loaded_monotone cost pre length b c d e f g dest x y tail padding)
  have preserved := NativeSourceIntercopyStoreFrame.loaded_read_below cost pre length b c d e f g dest x y tail
    c.toNat (amount cost pre length b c d e f g dest x y tail).toNat padding positive bounded sourceInside below
  exact NativeSourceSecondPayload.readback pre.memory cost pre length b c d e f g dest x y tail
    positive bounded sourceInside insideLoaded padding preserved

end Compiler.Proofs.IRGeneration.NativeSourceSecondSourceFrame
