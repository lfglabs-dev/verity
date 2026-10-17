import Compiler.Proofs.IRGeneration.NativeSourcePreCreateMemory

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondPayload
open EvmYul

def amount (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) :=
  (NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b

def output (length d e : UInt256) := (e + length) + d

theorem readback (original : ByteArray) (cost : Nat) (pre : EVM.State)
    (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (positive : 0 < (amount cost pre length b c d e f g dest x y tail).toNat)
    (bounded : (amount cost pre length b c d e f g dest x y tail).toNat < 2 ^ 64)
    (originalInside : c.toNat + (amount cost pre length b c d e f g dest x y tail).toNat ≤ original.size)
    (inside : c.toNat + (amount cost pre length b c d e f g dest x y tail).toNat ≤
      (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size)
    (storePadding : (output length d e).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (preserved : (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.readWithPadding
      c.toNat (amount cost pre length b c d e f g dest x y tail).toNat =
      original.readWithPadding c.toNat (amount cost pre length b c d e f g dest x y tail).toNat) :
    (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.readWithPadding
      (output length d e).toNat (amount cost pre length b c d e f g dest x y tail).toNat =
      original.extract c.toNat (c.toNat + (amount cost pre length b c d e f g dest x y tail).toNat) := by
  have padding : (output length d e).toNat -
      (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits := by
    rw [NativeSourceIntercopyCarrier.loaded_size cost pre length b c d e f g dest x y tail storePadding]
    change ((e + length) + d).toNat - max _ (((e + length) + d).toNat + 32) < _
    rw [Nat.sub_eq_zero_of_le (Nat.le_trans (by omega) (Nat.le_max_right _ _))]
    exact Nat.two_pow_pos _
  exact NativeSourceFirstCopyProvenance.second_readback original cost
    (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail)
    (amount cost pre length b c d e f g dest x y tail) (output length d e) (e + length) c
    (d :: e :: f :: g :: dest :: x :: y :: tail) positive bounded originalInside inside padding preserved

end Compiler.Proofs.IRGeneration.NativeSourceSecondPayload
