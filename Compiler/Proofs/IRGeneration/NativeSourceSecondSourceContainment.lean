import Compiler.Proofs.IRGeneration.NativeSourceGuardedOriginalReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondSourceContainment
open EvmYul

theorem inside (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (source : c.toNat + (NativeSourcePackedRequested.amount cost pre length b c d e f g dest x y tail).toNat ≤ pre.memory.size) :
    c.toNat + (NativeSourcePackedRequested.amount cost pre length b c d e f g dest x y tail).toNat ≤
      (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size := by
  exact source.trans (NativeSourceSecondPackingFrame.loaded_monotone cost pre length b c d e f g dest x y tail padding)

theorem inside_from_bound (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (count : Nat)
    (padding : ((e + length) + d).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (source : c.toNat + count ≤ pre.memory.size)
    (amount : (NativeSourcePackedRequested.amount cost pre length b c d e f g dest x y tail).toNat ≤ count) :
    c.toNat + (NativeSourcePackedRequested.amount cost pre length b c d e f g dest x y tail).toNat ≤
      (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).memory.size := by
  exact inside cost pre length b c d e f g dest x y tail padding (by omega)

end Compiler.Proofs.IRGeneration.NativeSourceSecondSourceContainment
