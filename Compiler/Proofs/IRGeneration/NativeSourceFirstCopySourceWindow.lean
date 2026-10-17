import Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadOriginalTotal
import Compiler.Proofs.IRGeneration.NativeSourceCopyWindowFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstCopySourceWindow
open EvmYul

theorem preserving_read_below (memory : ByteArray) (dest source size start length : Nat)
    (sourceInside : source + size ≤ memory.size)
    (padding : dest - memory.size < 2 ^ System.Platform.numBits)
    (bounded : length < 2 ^ 64)
    (inside : start + length ≤ memory.size) (below : start + length ≤ dest) :
    (memory.write source memory dest size).readWithPadding start length = memory.readWithPadding start length := by
  by_cases zeroRead : length = 0
  · rw [zeroRead, NativeSourceEmptyPayload.read_zero, NativeSourceEmptyPayload.read_zero]
  by_cases zeroCopy : size = 0
  · rw [zeroCopy, NativeSourceEmptyCopy.write_zero]
  exact NativeSourceCopyWindowFrame.preserving_read_below memory dest source size start length
    (by omega) sourceInside padding (by omega) bounded inside below

theorem first_read_below (cost : Nat) (pre : EVM.State)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256) (start count : Nat)
    (sourceInside : a.toNat + length.toNat ≤ pre.memory.size)
    (padding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (bounded : count < 2 ^ 64) (inside : start + count ≤ pre.memory.size)
    (below : start + count ≤ dest.toNat) :
    (NativeSourceFirstPayloadSurvival.first cost pre length a b c d e f g dest tail).memory.readWithPadding start count =
      pre.memory.readWithPadding start count := by
  unfold NativeSourceFirstPayloadSurvival.first
  rw [NativeSourceFirstCopyProvenance.copied_memory]
  exact preserving_read_below pre.memory dest.toNat a.toNat length.toNat start count
    sourceInside padding bounded inside below

end Compiler.Proofs.IRGeneration.NativeSourceFirstCopySourceWindow
