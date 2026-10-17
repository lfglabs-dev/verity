import Compiler.Proofs.IRGeneration.NativeSourceCopyLookupFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstCopyLookup
open EvmYul

theorem memory (pre : EVM.State) (cost1 cost2 cost3 cost4 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256) :
    (NativeSourceFirstCopy.copied pre cost1 cost2 cost3 cost4 length a b c d e f g dest tail).toMachineState.memory =
      (pre.toMachineState.mcopy dest a length).memory := by
  rfl

theorem lookup (pre : EVM.State) (cost1 cost2 cost3 cost4 : Nat)
    (length a b c d e f g dest query : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (destBound : dest.toNat < 2 ^ 64) (sourceBound : a.toNat < 2 ^ 64)
    (countBound : length.toNat < 2 ^ 64)
    (sourceInside : a.toNat + length.toNat ≤ pre.memory.size)
    (padding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (inside : query.toNat + 32 ≤ pre.memory.size)
    (below : query.toNat + 32 ≤ dest.toNat)
    (active : ¬query ≥ pre.activeWords * ⟨32⟩) :
    (NativeSourceFirstCopy.copied pre cost1 cost2 cost3 cost4 length a b c d e f g dest tail).toMachineState.lookupMemory query =
      pre.toMachineState.lookupMemory query := by
  have result := NativeSourceCopyLookupFrame.lookup pre.toMachineState dest a length query
    upper destBound sourceBound countBound sourceInside padding inside below active
  unfold MachineState.lookupMemory
  rw [memory, NativeSourceFirstCopyActive.extent]
  exact result

end Compiler.Proofs.IRGeneration.NativeSourceFirstCopyLookup
