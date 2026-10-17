import Compiler.Proofs.IRGeneration.NativeSourceSecondPackingFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstPayloadSurvival
open EvmYul

def first (cost : Nat) (pre : EVM.State) (length a b c d e f g dest : UInt256) (tail : Stack UInt256) :=
  NativeSourceFirstCopy.copied pre cost cost cost cost length a b c d e f g dest tail

theorem first_size (cost : Nat) (pre : EVM.State)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256)
    (positive : 0 < length.toNat) (sourceInside : a.toNat + length.toNat ≤ pre.memory.size)
    (padding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (first cost pre length a b c d e f g dest tail).memory.size =
      max pre.memory.size (dest.toNat + length.toNat) := by
  unfold first
  rw [NativeSourceFirstCopyProvenance.copied_memory,
    NativeSourceMcopyGrowth.write_snapshot pre.memory dest.toNat a.toNat length.toNat positive sourceInside padding]
  exact ByteArray.size_write _ pre.memory dest.toNat length.toNat positive
    (by rw [ByteArray.size_extract]; omega) padding

theorem readback (original : ByteArray) (cost : Nat) (pre : EVM.State)
    (length a b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (positive : 0 < length.toNat) (bounded : length.toNat < 2 ^ 64)
    (originalInside : a.toNat + length.toNat ≤ original.size)
    (sourceInside : a.toNat + length.toNat ≤ pre.memory.size)
    (firstPadding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (preserved : pre.memory.readWithPadding a.toNat length.toNat = original.readWithPadding a.toNat length.toNat)
    (padding : ((e + length) + d).toNat - (first cost pre length a b c d e f g dest (x :: y :: tail)).memory.size < 2 ^ System.Platform.numBits)
    (secondSource : c.toNat + ((NativeSourceSecondCopyStore.stored cost
      (first cost pre length a b c d e f g dest (x :: y :: tail)) length b c d e f g dest x y tail).toMachineState.lookupMemory b).toNat ≤
      (NativeSourceSecondCopyStore.loaded cost (first cost pre length a b c d e f g dest (x :: y :: tail))
        length b c d e f g dest x y tail).memory.size)
    (below : dest.toNat + length.toNat ≤ ((e + length) + d).toNat) :
    (NativeSourceSecondPacking.packed cost (first cost pre length a b c d e f g dest (x :: y :: tail))
      length b c d e f g dest x y tail).memory.readWithPadding dest.toNat length.toNat =
      original.extract a.toNat (a.toNat + length.toNat) := by
  have inside : dest.toNat + length.toNat ≤
      (first cost pre length a b c d e f g dest (x :: y :: tail)).memory.size := by
    rw [first_size cost pre length a b c d e f g dest (x :: y :: tail) positive sourceInside firstPadding]
    exact Nat.le_max_right _ _
  rw [NativeSourceSecondPackingFrame.read_below cost (first cost pre length a b c d e f g dest (x :: y :: tail))
    length b c d e f g dest x y tail dest.toNat length.toNat padding secondSource positive bounded inside below]
  exact NativeSourceFirstCopyProvenance.readback original pre cost cost cost cost length a b c d e f g dest (x :: y :: tail)
    positive bounded originalInside sourceInside firstPadding preserved

end Compiler.Proofs.IRGeneration.NativeSourceFirstPayloadSurvival
