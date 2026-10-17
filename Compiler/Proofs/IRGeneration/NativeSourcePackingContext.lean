import Compiler.Proofs.IRGeneration.NativeSourceReturnShuffles

namespace Compiler.Proofs.IRGeneration.NativeSourcePackingContext
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def prepared (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :=
  NativeSourceReturnShuffles.s7 cost (NativeSourceZeroShuffles.s6 cost pre a b c d e f g h i j k tail)
    a g a b c d e f i h j (k :: UInt256.ofNat 0 :: tail)

theorem entry_pc (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 573) :
    (NativeSourceZeroShuffles.s6 cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 579 := by
  change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
    UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [pc]; decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573) :
    run fuel cost 7 (NativeSourceZeroShuffles.s6 cost pre a b c d e f g h i j k tail) =
      .ok (prepared cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceReturnShuffles.execute fuel cost
    (NativeSourceZeroShuffles.s6 cost pre a b c d e f g h i j k tail)
    a g a b c d e f i h j (k :: UInt256.ofNat 0 :: tail) code
    (entry_pc cost pre a b c d e f g h i j k tail pc)
    (NativeSourceZeroShuffles.stack cost pre a b c d e f g h i j k tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    run fuel cost 13 pre = .ok (prepared cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 6 7 pre _ _
    (NativeSourceZeroShuffles.execute fuel cost pre a b c d e f g h i j k tail code pc stack)
    (finish fuel cost pre a b c d e f g h i j k tail code pc)

theorem stack (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (prepared cost pre a b c d e f g h i j k tail).stack =
      d :: e :: f :: a :: g :: a :: b :: c :: UInt256.ofNat 632 :: h :: UInt256.ofNat 32 ::
      i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourcePackingContext
