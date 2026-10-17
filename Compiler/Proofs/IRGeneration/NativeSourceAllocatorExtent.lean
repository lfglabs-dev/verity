import Compiler.Proofs.IRGeneration.NativeSourcePointerExtent

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorExtent
open EvmYul

theorem start (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorStart.s3 cost pre a b tail).activeWords = pre.activeWords := by
  rfl

theorem rounding (cost : Nat) (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorRounding.s5 cost pre a b c tail).activeWords = pre.activeWords := by
  rfl

theorem pointer (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorPointer.s5 cost pre a b tail).activeWords = pre.activeWords := by
  rfl

theorem limit (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorLimit.guarded cost pre a b tail).activeWords = pre.activeWords := by
  rfl

theorem branch (cost : Nat) (pre : EVM.State) (a : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorBranch.branched cost pre a tail).activeWords = pre.activeWords := by
  rfl

theorem rounded (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorRoundedEntry.rounded cost pre base size tail).activeWords = pre.activeWords := by
  unfold NativeSourceAllocatorRoundedEntry.rounded
  rw [rounding, start]

theorem tested (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorOverflowEntry.tested cost pre base size tail).activeWords = pre.activeWords := by
  unfold NativeSourceAllocatorOverflowEntry.tested
  rw [pointer, rounded]

theorem guarded (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorGuard.guarded cost pre base size tail).activeWords = pre.activeWords := by
  unfold NativeSourceAllocatorGuard.guarded
  rw [limit, tested]

theorem decided (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorDecision.decided cost pre base size tail).activeWords = pre.activeWords := by
  unfold NativeSourceAllocatorDecision.decided
  rw [branch, guarded]

theorem returned_words (cost : Nat) (pre : EVM.State) (pointer target : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceAllocatorReturn.returned cost pre pointer target tail).activeWords.toNat =
      max pre.activeWords.toNat 3 := by
  exact NativeSourcePointerActive.stored_words
    (EVM.Proof.stepPre cost (NativeSourceAllocatorReturn.pushed cost pre)).toMachineState pointer

theorem success_words (cost : Nat) (pre : EVM.State) (base size target : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceAllocatorSuccess.returned cost pre base size target tail).activeWords.toNat =
      max pre.activeWords.toNat 3 := by
  unfold NativeSourceAllocatorSuccess.returned
  rw [returned_words, decided]

theorem entered_words (cost : Nat) (pre : EVM.State) (a b c d e f g : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceFirstAllocatorJump.entered cost pre a b c d e f g tail).activeWords = pre.activeWords := by
  rfl

theorem caller_words (cost : Nat) (pre : EVM.State) (size target a b c d base : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceFirstAllocatorCaller.returned cost pre size target a b c d base tail).activeWords.toNat =
      max pre.activeWords.toNat 3 := by
  unfold NativeSourceFirstAllocatorCaller.returned
  rw [success_words, entered_words]

theorem context_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).activeWords.toNat =
      max (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).activeWords.toNat 3 := by
  exact caller_words cost _ (b - c) (UInt256.ofNat 632) h (UInt256.ofNat 32) i
    (UInt256.ofNat 681) j (k :: UInt256.ofNat 0 :: tail)

theorem context_bound (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (upper : (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251) :
    (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251 := by
  rw [context_words]
  exact max_lt upper (by decide)

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorExtent
