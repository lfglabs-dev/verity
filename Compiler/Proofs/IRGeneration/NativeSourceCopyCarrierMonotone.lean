import Compiler.Proofs.IRGeneration.NativeSourceSizewordCarrier

namespace Compiler.Proofs.IRGeneration.NativeSourceCopyCarrierMonotone
open EvmYul

theorem write_monotone (memory : ByteArray) (dest source count : Nat)
    (inside : source + count ≤ memory.size)
    (padding : dest - memory.size < 2 ^ System.Platform.numBits) :
    memory.size ≤ (memory.write source memory dest count).size := by
  by_cases zero : count = 0
  · subst count
    simp [ByteArray.write]
  · have positive : 0 < count := by omega
    rw [NativeSourceMcopyGrowth.write_snapshot memory dest source count positive inside padding]
    have snapshot : (memory.extract source (source + count)).size = count := by
      rw [ByteArray.size_extract]
      omega
    rw [ByteArray.size_write _ memory dest count positive snapshot padding]
    exact Nat.le_max_left _ _

theorem first_monotone (pre : EVM.State) (cost1 cost2 cost3 cost4 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256)
    (inside : a.toNat + length.toNat ≤ pre.memory.size)
    (padding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    pre.memory.size ≤ (NativeSourceFirstCopy.copied pre cost1 cost2 cost3 cost4 length a b c d e f g dest tail).memory.size := by
  rw [NativeSourceFirstCopyProvenance.copied_memory]
  exact write_monotone pre.memory dest.toNat a.toNat length.toNat inside padding

end Compiler.Proofs.IRGeneration.NativeSourceCopyCarrierMonotone
