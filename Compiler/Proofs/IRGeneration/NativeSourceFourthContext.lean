import Compiler.Proofs.IRGeneration.NativeSourceFourthFieldLoad

namespace Compiler.Proofs.IRGeneration.NativeSourceFourthContext
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def ready (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :=
  NativeSourceFourthFieldLoad.masked cost (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail) g a
    (b :: c :: UInt256.ofNat 632 :: h :: UInt256.ofNat 32 ::
      i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail)

theorem entry_pc (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 573) :
    (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 611 := by
  change ((((NativeSourceMaskedContext.ready cost pre a b c d e f g h i j k tail).pc +
    UInt256.ofNat 3) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [NativeSourceThirdField.entry_pc cost pre a b c d e f g h i j k tail pc]
  decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573) :
    run fuel cost 2 (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail) =
      .ok (ready cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceFourthFieldLoad.execute fuel cost _ g a _ code
    (entry_pc cost pre a b c d e f g h i j k tail pc)
    (NativeSourceThirdField.stack cost pre a b c d e f g h i j k tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    run fuel cost 31 pre = .ok (ready cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 29 2 pre _ _
    (NativeSourceThirdField.execute fuel cost pre a b c d e f g h i j k tail code pc stack)
    (finish fuel cost pre a b c d e f g h i j k tail code pc)

theorem stack (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (ready cost pre a b c d e f g h i j k tail).stack =
      ((NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory g).land a ::
      b :: c :: UInt256.ofNat 632 :: h :: UInt256.ofNat 32 ::
      i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail := by rfl

end Compiler.Proofs.IRGeneration.NativeSourceFourthContext
