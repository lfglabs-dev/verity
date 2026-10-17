import Compiler.Proofs.IRGeneration.NativeSourceLengthwordGeometry
import Compiler.Proofs.IRGeneration.NativeSourceLookupFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondAmountGeometry
open EvmYul

theorem natural_length (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y finish base : UInt256) (tail : Stack UInt256)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (inside : b.toNat + 32 ≤ pre.memory.size) (below : b.toNat + 32 ≤ ((e + length) + d).toNat)
    (beforeActive : ¬b ≥ pre.activeWords * ⟨32⟩)
    (afterActive : ¬b ≥ (NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).activeWords * ⟨32⟩)
    (word : pre.toMachineState.lookupMemory b = (finish - base) + UInt256.lnot (UInt256.ofNat 31))
    (ordered : base.toNat + 32 ≤ finish.toNat) :
    (NativeSourcePackedRequested.amount cost pre length b c d e f g dest x y tail).toNat = finish.toNat - base.toNat - 32 := by
  rw [NativeSourceLookupFrame.intercopy_amount cost pre length b c d e f g dest x y tail inside below padding beforeActive afterActive, word]
  exact NativeSourceLengthwordGeometry.length_toNat finish base ordered

end Compiler.Proofs.IRGeneration.NativeSourceSecondAmountGeometry
