import Compiler.Proofs.IRGeneration.NativeSourceCopyProvenance

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstCopyProvenance
open EvmYul

theorem prepared_memory (pre : EVM.State) (cost1 cost2 cost3 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256) :
    (NativeSourcePackingStack.prepared pre cost1 cost2 cost3 length a b c d e f g dest tail).memory =
      pre.memory := by
  rfl

theorem copied_memory (pre : EVM.State) (cost1 cost2 cost3 cost4 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256) :
    (NativeSourceFirstCopy.copied pre cost1 cost2 cost3 cost4 length a b c d e f g dest tail).memory =
      pre.memory.write a.toNat pre.memory dest.toNat length.toNat := by
  rfl

theorem readback (original : ByteArray) (pre : EVM.State) (cost1 cost2 cost3 cost4 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256)
    (positive : 0 < length.toNat) (bounded : length.toNat < 2 ^ 64)
    (originalInside : a.toNat + length.toNat ≤ original.size)
    (inside : a.toNat + length.toNat ≤ pre.memory.size)
    (padding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (preserved : pre.memory.readWithPadding a.toNat length.toNat = original.readWithPadding a.toNat length.toNat) :
    (NativeSourceFirstCopy.copied pre cost1 cost2 cost3 cost4 length a b c d e f g dest tail).memory.readWithPadding
      dest.toNat length.toNat = original.extract a.toNat (a.toNat + length.toNat) := by
  rw [copied_memory]
  exact NativeSourceCopyProvenance.readback_original original pre.memory dest.toNat a.toNat length.toNat
    positive bounded originalInside inside padding preserved

theorem second_copied_memory (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceSecondCopy.copied cost pre length dest finish source tail).memory =
      pre.memory.write source.toNat pre.memory dest.toNat length.toNat := by
  rfl

theorem second_readback (original : ByteArray) (cost : Nat) (pre : EVM.State)
    (length dest finish source : UInt256) (tail : Stack UInt256)
    (positive : 0 < length.toNat) (bounded : length.toNat < 2 ^ 64)
    (originalInside : source.toNat + length.toNat ≤ original.size)
    (inside : source.toNat + length.toNat ≤ pre.memory.size)
    (padding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (preserved : pre.memory.readWithPadding source.toNat length.toNat = original.readWithPadding source.toNat length.toNat) :
    (NativeSourceSecondCopy.copied cost pre length dest finish source tail).memory.readWithPadding
      dest.toNat length.toNat = original.extract source.toNat (source.toNat + length.toNat) := by
  rw [second_copied_memory]
  exact NativeSourceCopyProvenance.readback_original original pre.memory dest.toNat source.toNat length.toNat
    positive bounded originalInside inside padding preserved

end Compiler.Proofs.IRGeneration.NativeSourceFirstCopyProvenance
