import Compiler.Proofs.IRGeneration.NativeSourceActiveLength

namespace Compiler.Proofs.IRGeneration.NativeSourcePointerActive
open EvmYul

theorem stored_words (machine : MachineState) (value : UInt256) :
    (machine.mstore (UInt256.ofNat 64) value).activeWords.toNat = max machine.activeWords.toNat 3 := by
  change max machine.activeWords.toNat 3 % UInt256.size = _
  apply Nat.mod_eq_of_lt
  exact max_lt machine.activeWords.val.isLt (by decide)

theorem stored_allocated (machine : MachineState) (value : UInt256) :
    3 ≤ (machine.mstore (UInt256.ofNat 64) value).activeWords.toNat := by
  rw [stored_words]
  exact Nat.le_max_right _ _

theorem allocator_returned (cost : Nat) (pre : EVM.State) (pointer target : UInt256)
    (tail : Stack UInt256) :
    3 ≤ (NativeSourceAllocatorReturn.returned cost pre pointer target tail).activeWords.toNat := by
  exact stored_allocated (EVM.Proof.stepPre cost (NativeSourceAllocatorReturn.pushed cost pre)).toMachineState pointer

theorem success_allocated (cost : Nat) (pre : EVM.State) (base size target : UInt256)
    (tail : Stack UInt256) :
    3 ≤ (NativeSourceAllocatorSuccess.returned cost pre base size target tail).activeWords.toNat := by
  exact allocator_returned cost (NativeSourceAllocatorDecision.decided cost pre base size (target :: tail))
    (base + NativeSourceAllocatorOverflowEntry.amount size) target tail

theorem caller_allocated (cost : Nat) (pre : EVM.State) (size target a b c d base : UInt256)
    (tail : Stack UInt256) :
    3 ≤ (NativeSourceFirstAllocatorCaller.returned cost pre size target a b c d base tail).activeWords.toNat := by
  exact success_allocated cost (NativeSourceFirstAllocatorJump.entered cost pre size target a b c d base tail)
    base size target (a :: b :: c :: d :: base :: tail)

theorem context_allocated (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) :
    3 ≤ (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).activeWords.toNat := by
  exact caller_allocated cost (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail)
    (b - c) (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j (k :: UInt256.ofNat 0 :: tail)

end Compiler.Proofs.IRGeneration.NativeSourcePointerActive




