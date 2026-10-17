import Compiler.Proofs.IRGeneration.NativeSourceSecondPayload
import Compiler.Proofs.IRGeneration.NativeSourceStoreFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadSized
open EvmYul

theorem packing_read_below (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (padding : ((a + b) + c).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ pre.memory.size) (below : start + length ≤ ((a + b) + c).toNat) :
    (NativeSourcePackingSize.s6 cost pre a b c d e f g h tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  exact NativeSourceStoreFrame.read_below
    (NativeSourcePackingSize.s4 cost pre a b c d e f g h tail).toMachineState
    ((a + b) + c) h start length padding positive bounded inside below

theorem readback (original : ByteArray) (cost : Nat) (pre : EVM.State)
    (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (positive : 0 < (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat)
    (bounded : (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat < 2 ^ 64)
    (originalInside : c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat ≤ original.size)
    (inside : c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat ≤ (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size)
    (storePadding : (NativeSourceSecondPayload.output length d e).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (preserved : (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.readWithPadding c.toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat = original.readWithPadding c.toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat)
    (copiedInside : (NativeSourceSecondPayload.output length d e).toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat ≤ (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size)
    (finish : (((e + length) + NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail) + d).toNat = (NativeSourceSecondPayload.output length d e).toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat) :
    (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail).memory.readWithPadding (NativeSourceSecondPayload.output length d e).toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat = original.extract c.toNat (c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat) := by
  have frame := packing_read_below cost (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail)
    (e + length) (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail) d e f g dest x (y :: tail)
    (NativeSourceSecondPayload.output length d e).toNat (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat
    (by rw [finish]; rw [Nat.sub_eq_zero_of_le copiedInside]; exact Nat.two_pow_pos _) positive bounded copiedInside (by rw [finish])
  exact frame.trans (NativeSourceSecondPayload.readback original cost pre length b c d e f g dest x y tail positive bounded originalInside inside storePadding preserved)

end Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadSized
