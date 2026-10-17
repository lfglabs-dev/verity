import Compiler.Proofs.IRGeneration.NativeSourcePreludeLookup

namespace Compiler.Proofs.IRGeneration.NativeSourceDecodedLookup
open EvmYul

theorem loaded_lookup (cost : Nat) (pre : EVM.State) (query : UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (inside : query.toNat < pre.memory.size)
    (active : ¬query ≥ pre.activeWords * ⟨32⟩) :
    (NativeSourceFreePointer.loaded cost pre).toMachineState.lookupMemory query =
      pre.toMachineState.lookupMemory query := by
  have result := NativeSourcePreludeLookup.load_lookup pre.toMachineState (UInt256.ofNat 64)
    query upper (by decide) inside active
  unfold MachineState.lookupMemory
  rw [NativeSourcePreludeCopySize.loaded_memory, NativeSourceDecodedCopyActive.loaded_extent]
  exact result

theorem copied_lookup (cost : Nat) (pre : EVM.State)
    (a b c d e f g h query : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251) (address : f.toNat < 2 ^ 64)
    (destBound : (NativeSourceDecodedPackingStart.free cost pre + b).toNat < 2 ^ 64)
    (sourceBound : c.toNat < 2 ^ 64)
    (countBound : (NativeSourceDecodedCopyProvenance.length cost pre a b c d e f g h tail).toNat < 2 ^ 64)
    (sourceInside : c.toNat + (NativeSourceDecodedCopyProvenance.length cost pre a b c d e f g h tail).toNat ≤ pre.memory.size)
    (padding : (NativeSourceDecodedPackingStart.free cost pre + b).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (inside : query.toNat + 32 ≤ pre.memory.size)
    (below : query.toNat + 32 ≤ (NativeSourceDecodedPackingStart.free cost pre + b).toNat)
    (active : ¬query ≥ pre.activeWords * ⟨32⟩) :
    (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail).toMachineState.lookupMemory query =
      pre.toMachineState.lookupMemory query := by
  have copied := NativeSourcePreludeLookup.copied_lookup cost (NativeSourceFreePointer.loaded cost pre)
    (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h query tail
    (NativeSourceDecodedCopyActive.loaded_bound cost pre upper) address destBound sourceBound countBound
  rw [NativeSourcePreludeCopySize.loaded_memory] at copied
  exact (copied sourceInside padding inside below
    (NativeSourceDecodedActiveGuard.loaded_guard cost pre query upper active)).trans
    (loaded_lookup cost pre query upper (by omega) active)

end Compiler.Proofs.IRGeneration.NativeSourceDecodedLookup
