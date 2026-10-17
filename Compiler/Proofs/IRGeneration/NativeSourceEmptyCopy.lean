import Compiler.Proofs.IRGeneration.NativeSourceActualCopyFrames

namespace Compiler.Proofs.IRGeneration.NativeSourceEmptyCopy
open EvmYul

theorem write_zero (memory : ByteArray) (dest source : Nat) :
    memory.write source memory dest 0 = memory := by
  simp [ByteArray.write]

theorem first_memory (pre : EVM.State) (cost1 cost2 cost3 cost4 : Nat)
    (a b c d e f g dest : UInt256) (tail : Stack UInt256) :
    (NativeSourceFirstCopy.copied pre cost1 cost2 cost3 cost4 (UInt256.ofNat 0)
      a b c d e f g dest tail).memory = pre.memory := by
  rw [NativeSourceFirstCopyProvenance.copied_memory]
  exact write_zero pre.memory dest.toNat a.toNat

theorem second_memory (cost : Nat) (pre : EVM.State) (dest finish source : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceSecondCopy.copied cost pre (UInt256.ofNat 0) dest finish source tail).memory = pre.memory := by
  rw [NativeSourceFirstCopyProvenance.second_copied_memory]
  exact write_zero pre.memory dest.toNat source.toNat

end Compiler.Proofs.IRGeneration.NativeSourceEmptyCopy
