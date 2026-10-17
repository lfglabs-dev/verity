import Compiler.Proofs.IRGeneration.NativeSourceAllocatorReturnFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorPrefixMemory
open EvmYul

theorem start (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorStart.s3 cost pre a b tail).memory = pre.memory := by
  rfl

theorem rounding (cost : Nat) (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorRounding.s5 cost pre a b c tail).memory = pre.memory := by
  rfl

theorem pointer (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorPointer.s5 cost pre a b tail).memory = pre.memory := by
  rfl

theorem limit (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorLimit.guarded cost pre a b tail).memory = pre.memory := by
  rfl

theorem branch (cost : Nat) (pre : EVM.State) (a : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorBranch.branched cost pre a tail).memory = pre.memory := by
  rfl

theorem rounded (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorRoundedEntry.rounded cost pre base size tail).memory = pre.memory := by
  unfold NativeSourceAllocatorRoundedEntry.rounded
  rw [rounding, start]

theorem tested (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorOverflowEntry.tested cost pre base size tail).memory = pre.memory := by
  unfold NativeSourceAllocatorOverflowEntry.tested
  rw [pointer, rounded]

theorem guarded (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorGuard.guarded cost pre base size tail).memory = pre.memory := by
  unfold NativeSourceAllocatorGuard.guarded
  rw [limit, tested]

theorem decided (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorDecision.decided cost pre base size tail).memory = pre.memory := by
  unfold NativeSourceAllocatorDecision.decided
  rw [branch, guarded]

theorem success_read_above (cost : Nat) (pre : EVM.State) (base size target : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (above : 96 ≤ start) (inside : start + length ≤ pre.memory.size) :
    (NativeSourceAllocatorSuccess.returned cost pre base size target tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  have frame := NativeSourceAllocatorReturnFrame.read_above cost
    (NativeSourceAllocatorDecision.decided cost pre base size (target :: tail))
    (base + NativeSourceAllocatorOverflowEntry.amount size) target tail start length positive bounded above
  rw [decided] at frame
  exact frame inside

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorPrefixMemory
