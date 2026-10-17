import Compiler.Proofs.IRGeneration.NativeSourceAllocatorPrefixMemory

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstAllocatorFrame
open EvmYul

theorem entered_memory (cost : Nat) (pre : EVM.State) (a b c d e f g : UInt256) (tail : Stack UInt256) :
    (NativeSourceFirstAllocatorJump.entered cost pre a b c d e f g tail).memory = pre.memory := by
  rfl

theorem read_above (cost : Nat) (pre : EVM.State) (size target a b c d base : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (above : 96 ≤ start) (inside : start + length ≤ pre.memory.size) :
    (NativeSourceFirstAllocatorCaller.returned cost pre size target a b c d base tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  have frame := NativeSourceAllocatorPrefixMemory.success_read_above cost
    (NativeSourceFirstAllocatorJump.entered cost pre size target a b c d base tail)
    base size target (a :: b :: c :: d :: base :: tail) start length positive bounded above
  rw [entered_memory] at frame
  exact frame inside

theorem context_read_above (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (above : 96 ≤ start)
    (inside : start + length ≤ (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory.size) :
    (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).memory.readWithPadding start length =
      (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory.readWithPadding start length := by
  unfold NativeSourceFieldsAllocation.returned
  exact read_above cost (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail)
    (b - c) (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j
    (k :: UInt256.ofNat 0 :: tail) start length positive bounded above inside

end Compiler.Proofs.IRGeneration.NativeSourceFirstAllocatorFrame
