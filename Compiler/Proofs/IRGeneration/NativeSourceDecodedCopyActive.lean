import Compiler.Proofs.IRGeneration.NativeSourcePreludeActive

namespace Compiler.Proofs.IRGeneration.NativeSourceDecodedCopyActive
open EvmYul

theorem loaded_extent (cost : Nat) (pre : EVM.State) :
    (NativeSourceFreePointer.loaded cost pre).activeWords =
      (pre.toMachineState.mload (UInt256.ofNat 64)).2.activeWords := by
  rfl

theorem loaded_bound (cost : Nat) (pre : EVM.State)
    (upper : pre.activeWords.toNat < 2 ^ 251) :
    (NativeSourceFreePointer.loaded cost pre).activeWords.toNat < 2 ^ 251 := by
  rw [loaded_extent]
  exact NativeSourceWordAccessExtent.load_bound pre.toMachineState (UInt256.ofNat 64) upper (by decide)

theorem copied_bound (cost : Nat) (pre : EVM.State)
    (a b c d e f g h : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251) (address : f.toNat < 2 ^ 64)
    (destBound : (NativeSourceDecodedPackingStart.free cost pre + b).toNat < 2 ^ 64)
    (sourceBound : c.toNat < 2 ^ 64)
    (countBound : (NativeSourceDecodedCopyProvenance.length cost pre a b c d e f g h tail).toNat < 2 ^ 64) :
    (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail).activeWords.toNat < 2 ^ 251 := by
  exact NativeSourcePreludeActive.copied_bound cost (NativeSourceFreePointer.loaded cost pre)
    (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h tail
    (loaded_bound cost pre upper) address destBound sourceBound countBound

end Compiler.Proofs.IRGeneration.NativeSourceDecodedCopyActive
