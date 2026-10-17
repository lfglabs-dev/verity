import Compiler.Proofs.IRGeneration.NativeSourceCopyActiveExtent

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstCopyActive
open EvmYul

theorem extent (pre : EVM.State) (cost1 cost2 cost3 cost4 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256) :
    (NativeSourceFirstCopy.copied pre cost1 cost2 cost3 cost4 length a b c d e f g dest tail).activeWords =
      (pre.toMachineState.mcopy dest a length).activeWords := by
  rfl

theorem bound (pre : EVM.State) (cost1 cost2 cost3 cost4 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251) (destBound : dest.toNat < 2 ^ 64)
    (sourceBound : a.toNat < 2 ^ 64) (countBound : length.toNat < 2 ^ 64) :
    (NativeSourceFirstCopy.copied pre cost1 cost2 cost3 cost4 length a b c d e f g dest tail).activeWords.toNat < 2 ^ 251 := by
  rw [extent]
  exact NativeSourceCopyActiveExtent.copy_bound pre.toMachineState dest a length upper destBound sourceBound countBound

theorem guard (pre : EVM.State) (cost1 cost2 cost3 cost4 : Nat)
    (length a b c d e f g dest query : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251) (destBound : dest.toNat < 2 ^ 64)
    (sourceBound : a.toNat < 2 ^ 64) (countBound : length.toNat < 2 ^ 64)
    (active : ¬query ≥ pre.activeWords * ⟨32⟩) :
    ¬query ≥ (NativeSourceFirstCopy.copied pre cost1 cost2 cost3 cost4 length a b c d e f g dest tail).activeWords * ⟨32⟩ := by
  rw [extent]
  exact NativeSourceCopyActiveExtent.guard_preserved pre.toMachineState dest a length query upper destBound sourceBound countBound active

end Compiler.Proofs.IRGeneration.NativeSourceFirstCopyActive
