import Compiler.Proofs.IRGeneration.NativeSourcePreludeActiveGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceDecodedActiveGuard
open EvmYul

theorem loaded_guard (cost : Nat) (pre : EVM.State) (query : UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (active : ¬query ≥ pre.activeWords * ⟨32⟩) :
    ¬query ≥ (NativeSourceFreePointer.loaded cost pre).activeWords * ⟨32⟩ := by
  rw [NativeSourceDecodedCopyActive.loaded_extent]
  exact NativeSourceLoadActiveGuard.guard_preserved pre.toMachineState (UInt256.ofNat 64)
    query upper (by decide) active

theorem copied_guard (cost : Nat) (pre : EVM.State)
    (a b c d e f g h query : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251) (address : f.toNat < 2 ^ 64)
    (destBound : (NativeSourceDecodedPackingStart.free cost pre + b).toNat < 2 ^ 64)
    (sourceBound : c.toNat < 2 ^ 64)
    (countBound : (NativeSourceDecodedCopyProvenance.length cost pre a b c d e f g h tail).toNat < 2 ^ 64)
    (active : ¬query ≥ pre.activeWords * ⟨32⟩) :
    ¬query ≥ (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail).activeWords * ⟨32⟩ := by
  exact NativeSourcePreludeActiveGuard.copied_guard cost (NativeSourceFreePointer.loaded cost pre)
    (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h query tail
    (NativeSourceDecodedCopyActive.loaded_bound cost pre upper) address destBound sourceBound countBound
    (loaded_guard cost pre query upper active)

end Compiler.Proofs.IRGeneration.NativeSourceDecodedActiveGuard
