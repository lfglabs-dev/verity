import Compiler.Proofs.IRGeneration.NativeSourceSecondSourceContainment

namespace Compiler.Proofs.IRGeneration.NativeSourceLookupFrame
open EvmYul

theorem lookup_eq (before after : MachineState) (address : UInt256)
    (beforeInside : address.toNat < before.memory.size)
    (afterInside : address.toNat < after.memory.size)
    (beforeActive : ¬address ≥ before.activeWords * ⟨32⟩)
    (afterActive : ¬address ≥ after.activeWords * ⟨32⟩)
    (bytes : after.memory.readWithPadding address.toNat 32 = before.memory.readWithPadding address.toNat 32) :
    after.lookupMemory address = before.lookupMemory address := by
  unfold MachineState.lookupMemory
  rw [if_neg (not_or_intro (by omega) afterActive), if_neg (not_or_intro (by omega) beforeActive), bytes]

theorem intercopy_amount (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (inside : b.toNat + 32 ≤ pre.memory.size)
    (below : b.toNat + 32 ≤ ((e + length) + d).toNat)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (beforeActive : ¬b ≥ pre.activeWords * ⟨32⟩)
    (afterActive : ¬b ≥ (NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).activeWords * ⟨32⟩) :
    NativeSourcePackedRequested.amount cost pre length b c d e f g dest x y tail =
      pre.toMachineState.lookupMemory b := by
  apply lookup_eq
  · omega
  · have growth := NativeSourceIntercopyCarrier.stored_monotone cost pre length b c d e f g dest x y tail padding
    omega
  · exact beforeActive
  · exact afterActive
  · exact NativeSourceIntercopyStoreFrame.read_below cost pre length b c d e f g dest x y tail
      b.toNat 32 padding (by decide) (by decide) inside below

end Compiler.Proofs.IRGeneration.NativeSourceLookupFrame
