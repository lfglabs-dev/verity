import Compiler.Proofs.IRGeneration.NativeSourceTotalOriginalReturn

namespace Compiler.Proofs.IRGeneration.NativeSourcePreludeCopySize
open EvmYul

theorem entry_memory (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256)
    (tail : Stack UInt256) :
    (NativeSourcePreludeCopy.entry cost cost pre free a b c d e f g h tail).memory = pre.memory := by
  rfl

theorem copied_size (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256)
    (tail : Stack UInt256)
    (positive : 0 < (NativeSourcePreludeCopy.length cost pre free a b c d e f g h tail).toNat)
    (source : c.toNat + (NativeSourcePreludeCopy.length cost pre free a b c d e f g h tail).toNat ≤ pre.memory.size)
    (padding : (free + b).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourcePreludeCopy.copied cost cost cost cost cost cost pre free a b c d e f g h tail).memory.size =
      max pre.memory.size ((free + b).toNat +
        (NativeSourcePreludeCopy.length cost pre free a b c d e f g h tail).toNat) := by
  have result := NativeSourceFirstPayloadSurvival.first_size cost
    (NativeSourcePreludeCopy.entry cost cost pre free a b c d e f g h tail)
    (NativeSourcePreludeCopy.length cost pre free a b c d e f g h tail)
    c e a b free d free (free + b) (g :: h :: tail) positive
  rw [entry_memory] at result
  exact result source padding

theorem loaded_memory (cost : Nat) (pre : EVM.State) :
    (NativeSourceFreePointer.loaded cost pre).memory = pre.memory := by
  rfl

theorem decoded_size (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256)
    (tail : Stack UInt256)
    (positive : 0 < (NativeSourceDecodedCopyProvenance.length cost pre a b c d e f g h tail).toNat)
    (source : c.toNat + (NativeSourceDecodedCopyProvenance.length cost pre a b c d e f g h tail).toNat ≤ pre.memory.size)
    (padding : (NativeSourceDecodedPackingStart.free cost pre + b).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail).memory.size =
      max pre.memory.size ((NativeSourceDecodedPackingStart.free cost pre + b).toNat +
        (NativeSourceDecodedCopyProvenance.length cost pre a b c d e f g h tail).toNat) := by
  have result := copied_size cost (NativeSourceFreePointer.loaded cost pre)
    (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h tail positive
  rw [loaded_memory] at result
  exact result source padding

end Compiler.Proofs.IRGeneration.NativeSourcePreludeCopySize

