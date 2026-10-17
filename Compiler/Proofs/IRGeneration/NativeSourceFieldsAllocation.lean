import Compiler.Proofs.IRGeneration.NativeSourceFirstAllocatorCaller

namespace Compiler.Proofs.IRGeneration.NativeSourceFieldsAllocation
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def returned (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :=
  NativeSourceFirstAllocatorCaller.returned cost (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail)
    (b - c) (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j
    (k :: UInt256.ofNat 0 :: tail)

theorem entry_pc (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 573) :
    (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 627 := by
  change (((((((NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).pc +
    UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [NativeSourceSizedFields.entry_pc cost pre a b c d e f g h i j k tail pc]
  decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (guard : NativeSourceAllocatorDecision.flag j (b - c) = ⟨0⟩) :
    run fuel cost 25 (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail) =
      .ok (returned cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceFirstAllocatorCaller.execute fuel cost _ (b - c) (UInt256.ofNat 632)
    h (UInt256.ofNat 32) i (UInt256.ofNat 681) j (k :: UInt256.ofNat 0 :: tail)
    code (entry_pc cost pre a b c d e f g h i j k tail pc)
    (NativeSourceSizedFields.stack cost pre a b c d e f g h i j k tail) guard

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail)
    (guard : NativeSourceAllocatorDecision.flag j (b - c) = ⟨0⟩) :
    run fuel cost 67 pre = .ok (returned cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 42 25 pre _ _
    (NativeSourceSizedFields.execute fuel cost pre a b c d e f g h i j k tail code pc stack)
    (finish fuel cost pre a b c d e f g h i j k tail code pc guard)

theorem target (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (returned cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 632 := by rfl

theorem stack (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (returned cost pre a b c d e f g h i j k tail).stack =
      h :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail := by rfl

end Compiler.Proofs.IRGeneration.NativeSourceFieldsAllocation
