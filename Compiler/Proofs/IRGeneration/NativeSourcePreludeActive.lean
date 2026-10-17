import Compiler.Proofs.IRGeneration.NativeSourceFirstCopyActive

namespace Compiler.Proofs.IRGeneration.NativeSourcePreludeActive
open EvmYul

theorem entry_extent (cost loadCost : Nat) (pre : EVM.State)
    (free a b c d e f g h : UInt256) (tail : Stack UInt256) :
    (NativeSourcePreludeCopy.entry cost loadCost pre free a b c d e f g h tail).activeWords =
      (pre.toMachineState.mload f).2.activeWords := by
  rfl

theorem entry_bound (cost loadCost : Nat) (pre : EVM.State)
    (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251) (address : f.toNat < 2 ^ 64) :
    (NativeSourcePreludeCopy.entry cost loadCost pre free a b c d e f g h tail).activeWords.toNat < 2 ^ 251 := by
  rw [entry_extent]
  exact NativeSourceWordAccessExtent.load_bound pre.toMachineState f upper address

theorem copied_bound (cost : Nat) (pre : EVM.State)
    (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251) (address : f.toNat < 2 ^ 64)
    (destBound : (free + b).toNat < 2 ^ 64) (sourceBound : c.toNat < 2 ^ 64)
    (countBound : (NativeSourcePreludeCopy.length cost pre free a b c d e f g h tail).toNat < 2 ^ 64) :
    (NativeSourcePreludeCopy.copied cost cost cost cost cost cost pre free a b c d e f g h tail).activeWords.toNat < 2 ^ 251 := by
  exact NativeSourceFirstCopyActive.bound _ cost cost cost cost _ c e a b free d free (free + b)
    (g :: h :: tail) (entry_bound cost cost pre free a b c d e f g h tail upper address)
    destBound sourceBound countBound

end Compiler.Proofs.IRGeneration.NativeSourcePreludeActive
