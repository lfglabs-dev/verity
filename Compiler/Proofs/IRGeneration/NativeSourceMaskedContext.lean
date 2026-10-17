import Compiler.Proofs.IRGeneration.NativeSourceMaskedFieldLoad

namespace Compiler.Proofs.IRGeneration.NativeSourceMaskedContext
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def ready (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :=
  NativeSourceMaskedFieldLoad.masked cost (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail) f a
    (g :: a :: b :: c :: UInt256.ofNat 632 :: h :: UInt256.ofNat 32 ::
      i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail)

theorem entry_pc (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 573) :
    (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 603 := by
  change ((((NativeSourceSecondFieldLoad.loaded cost pre a b c d e f g h i j k tail).pc +
    UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [NativeSourceSecondField.entry_pc cost pre a b c d e f g h i j k tail pc]
  decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573) :
    run fuel cost 2 (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail) =
      .ok (ready cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceMaskedFieldLoad.execute fuel cost _ f a _ code
    (entry_pc cost pre a b c d e f g h i j k tail pc)
    (NativeSourceSecondField.stack cost pre a b c d e f g h i j k tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    run fuel cost 25 pre = .ok (ready cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 23 2 pre _ _
    (NativeSourceSecondField.execute fuel cost pre a b c d e f g h i j k tail code pc stack)
    (finish fuel cost pre a b c d e f g h i j k tail code pc)

theorem stack (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (ready cost pre a b c d e f g h i j k tail).stack =
      ((NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory f).land a ::
      g :: a :: b :: c :: UInt256.ofNat 632 :: h :: UInt256.ofNat 32 ::
      i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail := by rfl

end Compiler.Proofs.IRGeneration.NativeSourceMaskedContext
