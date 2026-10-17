import Compiler.Proofs.IRGeneration.NativeSourceSecondAllocatorFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceRoundedCarrier
open EvmYul

theorem store_size (cost : Nat) (pre : EVM.State) (mask size a b c : UInt256) (tail : Stack UInt256)
    (padding : b.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceRoundingStore.s4 cost pre mask size a b c tail).memory.size =
      max pre.memory.size (b.toNat + 32) := by
  rw [NativeSourceFinalRoundingFrame.stored_memory]
  exact MachineState.size_memory_mstore_of_pad pre.toMachineState b (size + mask) padding

theorem rounded_size (cost : Nat) (pre : EVM.State) (size a b c : UInt256) (tail : Stack UInt256)
    (padding : b.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceRounding.rounded cost pre size a b c tail).memory.size =
      max pre.memory.size (b.toNat + 32) := by
  have result := store_size cost (NativeSourceRoundingEntry.masked cost pre)
    (UInt256.lnot (UInt256.ofNat 31)) size a b c tail
  rw [NativeSourceFinalRoundingFrame.masked_memory] at result
  exact result padding

theorem context_size (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (padding : g.toNat - (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail).memory.size <
      2 ^ System.Platform.numBits) :
    (NativeSourceRoundedSecondCopy.rounded cost pre length b c d e f g dest x y tail).memory.size =
      max (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail).memory.size (g.toNat + 32) := by
  exact rounded_size cost (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail)
    _ f g dest (x :: y :: tail) padding

theorem context_fits (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (start count : Nat)
    (above : g.toNat + 32 ≤ start)
    (inside : start + count ≤ (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail).memory.size) :
    (NativeSourceRoundedSecondCopy.rounded cost pre length b c d e f g dest x y tail).memory.size =
      (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail).memory.size := by
  have fits : g.toNat + 32 ≤ (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail).memory.size := by omega
  have padding : g.toNat - (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail).memory.size <
      2 ^ System.Platform.numBits := by
    rw [Nat.sub_eq_zero_of_le (by omega)]
    exact Nat.two_pow_pos _
  rw [context_size cost pre length b c d e f g dest x y tail padding, Nat.max_eq_left fits]

end Compiler.Proofs.IRGeneration.NativeSourceRoundedCarrier
