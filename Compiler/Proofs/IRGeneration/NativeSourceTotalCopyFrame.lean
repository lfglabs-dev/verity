import Compiler.Proofs.IRGeneration.NativeSourceEmptyCopy

namespace Compiler.Proofs.IRGeneration.NativeSourceTotalCopyFrame
open EvmYul

theorem read_below (memory : ByteArray) (dest source size start length : Nat)
    (sourceInside : source + size ≤ memory.size)
    (padding : dest - memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ memory.size) (below : start + length ≤ dest) :
    (memory.write source memory dest size).readWithPadding start length =
      memory.readWithPadding start length := by
  by_cases zero : size = 0
  · subst size
    rw [NativeSourceEmptyCopy.write_zero]
  · exact NativeSourceCopyWindowFrame.preserving_read_below memory dest source size start length
      (by omega) sourceInside padding positive bounded inside below

theorem first_below (pre : EVM.State) (cost1 cost2 cost3 cost4 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256) (start count : Nat)
    (sourceInside : a.toNat + length.toNat ≤ pre.memory.size)
    (padding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (inside : start + count ≤ pre.memory.size) (below : start + count ≤ dest.toNat) :
    (NativeSourceFirstCopy.copied pre cost1 cost2 cost3 cost4 length a b c d e f g dest tail).memory.readWithPadding start count =
      pre.memory.readWithPadding start count := by
  rw [NativeSourceFirstCopyProvenance.copied_memory]
  exact read_below pre.memory dest.toNat a.toNat length.toNat start count
    sourceInside padding positive bounded inside below

theorem second_below (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256)
    (tail : Stack UInt256) (start count : Nat)
    (sourceInside : source.toNat + length.toNat ≤ pre.memory.size)
    (padding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (inside : start + count ≤ pre.memory.size) (below : start + count ≤ dest.toNat) :
    (NativeSourceSecondCopy.copied cost pre length dest finish source tail).memory.readWithPadding start count =
      pre.memory.readWithPadding start count := by
  rw [NativeSourceFirstCopyProvenance.second_copied_memory]
  exact read_below pre.memory dest.toNat source.toNat length.toNat start count
    sourceInside padding positive bounded inside below

end Compiler.Proofs.IRGeneration.NativeSourceTotalCopyFrame
