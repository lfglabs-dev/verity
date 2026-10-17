import Compiler.Proofs.IRGeneration.NativeSourceDecodedCopyProvenance

namespace Compiler.Proofs.IRGeneration.NativeSourceActiveLength
open EvmYul NativeSourceDecodedCopyProvenance

theorem original_length (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256)
    (tail : Stack UInt256) (carrier : f.toNat < pre.memory.size)
    (beforeActive : ¬f ≥ pre.activeWords * ⟨32⟩)
    (afterActive : ¬f ≥ (NativeSourceFreePointer.loaded cost pre).activeWords * ⟨32⟩) :
    length cost pre a b c d e f g h tail = pre.toMachineState.lookupMemory f := by
  rw [length_value]
  apply NativeSourceMemoryFrame.lookup_of_read pre.toMachineState
    (NativeSourceFreePointer.loaded cost pre).toMachineState f carrier
  · exact carrier
  · exact beforeActive
  · exact afterActive
  · rfl

theorem loaded_active (cost : Nat) (pre : EVM.State)
    (allocated : 3 ≤ pre.activeWords.toNat) :
    (NativeSourceFreePointer.loaded cost pre).activeWords = pre.activeWords := by
  change UInt256.ofNat (max pre.activeWords.toNat 3) = pre.activeWords
  rw [max_eq_left allocated]
  apply congrArg UInt256.mk
  apply Fin.ext
  exact Nat.mod_eq_of_lt pre.activeWords.val.isLt

theorem allocated_length (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256)
    (tail : Stack UInt256) (carrier : f.toNat < pre.memory.size)
    (allocated : 3 ≤ pre.activeWords.toNat)
    (active : ¬f ≥ pre.activeWords * ⟨32⟩) :
    length cost pre a b c d e f g h tail = pre.toMachineState.lookupMemory f := by
  apply original_length cost pre a b c d e f g h tail carrier active
  rw [loaded_active cost pre allocated]
  exact active

end Compiler.Proofs.IRGeneration.NativeSourceActiveLength

