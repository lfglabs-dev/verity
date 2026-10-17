import Compiler.Proofs.IRGeneration.NativeSourceStoreActiveGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceIntercopyActiveLookup
open EvmYul

theorem stored_words (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).activeWords =
      (pre.toMachineState.mstore ((e + length) + d) x).activeWords := by
  rfl

theorem amount (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (inside : b.toNat + 32 ≤ pre.memory.size)
    (below : b.toNat + 32 ≤ ((e + length) + d).toNat)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (address : ((e + length) + d).toNat < 2 ^ 64)
    (active : ¬b ≥ pre.activeWords * ⟨32⟩) :
    NativeSourcePackedRequested.amount cost pre length b c d e f g dest x y tail =
      pre.toMachineState.lookupMemory b := by
  apply NativeSourceLookupFrame.intercopy_amount cost pre length b c d e f g dest x y tail
    inside below padding active
  rw [stored_words]
  exact NativeSourceStoreActiveGuard.guard_preserved pre.toMachineState ((e + length) + d) x b
    upper address active

end Compiler.Proofs.IRGeneration.NativeSourceIntercopyActiveLookup
