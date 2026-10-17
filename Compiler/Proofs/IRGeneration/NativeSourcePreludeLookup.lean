import Compiler.Proofs.IRGeneration.NativeSourceFirstCopyLookup

namespace Compiler.Proofs.IRGeneration.NativeSourcePreludeLookup
open EvmYul

theorem load_lookup (machine : MachineState) (address query : UInt256)
    (upper : machine.activeWords.toNat < 2 ^ 251) (bounded : address.toNat < 2 ^ 64)
    (inside : query.toNat < machine.memory.size)
    (active : ¬query ≥ machine.activeWords * ⟨32⟩) :
    (machine.mload address).2.lookupMemory query = machine.lookupMemory query := by
  apply NativeSourceLookupFrame.lookup_eq
  · exact inside
  · exact inside
  · exact active
  · exact NativeSourceLoadActiveGuard.guard_preserved machine address query upper bounded active
  · rfl

theorem entry_lookup (cost : Nat) (pre : EVM.State)
    (free a b c d e f g h query : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251) (address : f.toNat < 2 ^ 64)
    (inside : query.toNat < pre.memory.size)
    (active : ¬query ≥ pre.activeWords * ⟨32⟩) :
    (NativeSourcePreludeCopy.entry cost cost pre free a b c d e f g h tail).toMachineState.lookupMemory query =
      pre.toMachineState.lookupMemory query := by
  have result := load_lookup pre.toMachineState f query upper address inside active
  unfold MachineState.lookupMemory
  rw [NativeSourcePreludeCopySize.entry_memory, NativeSourcePreludeActive.entry_extent]
  exact result

theorem copied_lookup (cost : Nat) (pre : EVM.State)
    (free a b c d e f g h query : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251) (address : f.toNat < 2 ^ 64)
    (destBound : (free + b).toNat < 2 ^ 64) (sourceBound : c.toNat < 2 ^ 64)
    (countBound : (NativeSourcePreludeCopy.length cost pre free a b c d e f g h tail).toNat < 2 ^ 64)
    (sourceInside : c.toNat + (NativeSourcePreludeCopy.length cost pre free a b c d e f g h tail).toNat ≤ pre.memory.size)
    (padding : (free + b).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (inside : query.toNat + 32 ≤ pre.memory.size) (below : query.toNat + 32 ≤ (free + b).toNat)
    (active : ¬query ≥ pre.activeWords * ⟨32⟩) :
    (NativeSourcePreludeCopy.copied cost cost cost cost cost cost pre free a b c d e f g h tail).toMachineState.lookupMemory query =
      pre.toMachineState.lookupMemory query := by
  have copied := NativeSourceFirstCopyLookup.lookup
    (NativeSourcePreludeCopy.entry cost cost pre free a b c d e f g h tail) cost cost cost cost
    (NativeSourcePreludeCopy.length cost pre free a b c d e f g h tail)
    c e a b free d free (free + b) query (g :: h :: tail)
    (NativeSourcePreludeActive.entry_bound cost cost pre free a b c d e f g h tail upper address)
    destBound sourceBound countBound
  rw [NativeSourcePreludeCopySize.entry_memory] at copied
  exact (copied sourceInside padding inside below
    (NativeSourcePreludeActiveGuard.entry_guard cost pre free a b c d e f g h query tail upper address active)).trans
    (entry_lookup cost pre free a b c d e f g h query tail upper address (by omega) active)

end Compiler.Proofs.IRGeneration.NativeSourcePreludeLookup
