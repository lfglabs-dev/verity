import Compiler.Proofs.IRGeneration.NativeSourceFieldSize

namespace Compiler.Proofs.IRGeneration.NativeSourceSizedFields
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def stored (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :=
  NativeSourceFieldSize.stored cost (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail)
    b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k
    (UInt256.ofNat 0 :: tail)

theorem entry_pc (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 573) :
    (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 619 := by
  change ((((NativeSourceFourthContext.ready cost pre a b c d e f g h i j k tail).pc +
    UInt256.ofNat 3) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [NativeSourceFourthField.entry_pc cost pre a b c d e f g h i j k tail pc]
  decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573) :
    run fuel cost 7 (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail) =
      .ok (stored cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceFieldSize.execute fuel cost _ b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k
    (UInt256.ofNat 0 :: tail) code (entry_pc cost pre a b c d e f g h i j k tail pc)
    (NativeSourceFourthField.stack cost pre a b c d e f g h i j k tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    run fuel cost 42 pre = .ok (stored cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 35 7 pre _ _
    (NativeSourceFourthField.execute fuel cost pre a b c d e f g h i j k tail code pc stack)
    (finish fuel cost pre a b c d e f g h i j k tail code pc)

theorem stack (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (stored cost pre a b c d e f g h i j k tail).stack =
      (b - c) :: UInt256.ofNat 632 :: h :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 ::
      j :: k :: UInt256.ofNat 0 :: tail := by rfl

end Compiler.Proofs.IRGeneration.NativeSourceSizedFields
