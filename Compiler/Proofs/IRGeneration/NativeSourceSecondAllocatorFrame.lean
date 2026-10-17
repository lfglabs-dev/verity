import Compiler.Proofs.IRGeneration.NativeSourceFinalSizeContext

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondAllocatorFrame
open EvmYul

theorem entered_memory (cost : Nat) (pre : EVM.State) (size target base : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorJump.entered cost pre size target base tail).memory = pre.memory := by
  rfl

theorem read_above (cost : Nat) (pre : EVM.State) (size target base : UInt256)
    (tail : Stack UInt256) (start count : Nat)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (above : 96 ≤ start) (inside : start + count ≤ pre.memory.size) :
    (NativeSourceAllocatorCaller.returned cost pre size target base tail).memory.readWithPadding start count =
      pre.memory.readWithPadding start count := by
  have frame := NativeSourceAllocatorPrefixMemory.success_read_above cost
    (NativeSourceAllocatorJump.entered cost pre size target base tail)
    base size target (base :: tail) start count positive bounded above
  rw [entered_memory] at frame
  exact frame inside

theorem packed_read_above (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (start count : Nat)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (above : 96 ≤ start)
    (inside : start + count ≤ (NativeSourceRoundedSecondCopy.rounded cost pre length b c d e f g dest x y tail).memory.size) :
    (NativeSourcePackedAllocation.returned cost pre length b c d e f g dest x y tail).memory.readWithPadding start count =
      (NativeSourceRoundedSecondCopy.rounded cost pre length b c d e f g dest x y tail).memory.readWithPadding start count := by
  unfold NativeSourcePackedAllocation.returned
  exact read_above cost (NativeSourceRoundedSecondCopy.rounded cost pre length b c d e f g dest x y tail)
    _ f g (dest :: x :: y :: tail) start count positive bounded above inside

end Compiler.Proofs.IRGeneration.NativeSourceSecondAllocatorFrame
