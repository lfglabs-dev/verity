import Compiler.Proofs.IRGeneration.NativeSourceAllocatorActiveGuard

namespace Compiler.Proofs.IRGeneration.NativeSourcePreludeActiveGuard
open EvmYul

theorem entry_guard (cost : Nat) (pre : EVM.State)
    (free a b c d e f g h query : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251) (address : f.toNat < 2 ^ 64)
    (active : ¬query ≥ pre.activeWords * ⟨32⟩) :
    ¬query ≥ (NativeSourcePreludeCopy.entry cost cost pre free a b c d e f g h tail).activeWords * ⟨32⟩ := by
  rw [NativeSourcePreludeActive.entry_extent]
  exact NativeSourceLoadActiveGuard.guard_preserved pre.toMachineState f query upper address active

theorem copied_guard (cost : Nat) (pre : EVM.State)
    (free a b c d e f g h query : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251) (address : f.toNat < 2 ^ 64)
    (destBound : (free + b).toNat < 2 ^ 64) (sourceBound : c.toNat < 2 ^ 64)
    (countBound : (NativeSourcePreludeCopy.length cost pre free a b c d e f g h tail).toNat < 2 ^ 64)
    (active : ¬query ≥ pre.activeWords * ⟨32⟩) :
    ¬query ≥ (NativeSourcePreludeCopy.copied cost cost cost cost cost cost pre free a b c d e f g h tail).activeWords * ⟨32⟩ := by
  exact NativeSourceFirstCopyActive.guard _ cost cost cost cost _ c e a b free d free (free + b)
    query (g :: h :: tail)
    (NativeSourcePreludeActive.entry_bound cost cost pre free a b c d e f g h tail upper address)
    destBound sourceBound countBound
    (entry_guard cost pre free a b c d e f g h query tail upper address active)

end Compiler.Proofs.IRGeneration.NativeSourcePreludeActiveGuard
