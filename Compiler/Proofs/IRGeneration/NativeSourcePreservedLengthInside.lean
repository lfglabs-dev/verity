import Compiler.Proofs.IRGeneration.NativeSourceIntercopyActiveLookup

namespace Compiler.Proofs.IRGeneration.NativeSourcePreservedLengthInside
open EvmYul

theorem inside (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (wordInside : b.toNat + 32 ≤ pre.memory.size)
    (below : b.toNat + 32 ≤ ((e + length) + d).toNat)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (address : ((e + length) + d).toNat < 2 ^ 64)
    (active : ¬b ≥ pre.activeWords * ⟨32⟩)
    (source : c.toNat + (pre.toMachineState.lookupMemory b).toNat ≤ pre.memory.size) :
    c.toNat + (NativeSourcePackedRequested.amount cost pre length b c d e f g dest x y tail).toNat ≤
      (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size := by
  apply NativeSourceSecondSourceContainment.inside cost pre length b c d e f g dest x y tail padding
  rw [NativeSourceIntercopyActiveLookup.amount cost pre length b c d e f g dest x y tail
    wordInside below padding upper address active]
  exact source

end Compiler.Proofs.IRGeneration.NativeSourcePreservedLengthInside
