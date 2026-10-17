import Compiler.Proofs.IRGeneration.NativeSourceMaskedContext
import Compiler.Proofs.IRGeneration.NativeSourceMaskedFieldStore

namespace Compiler.Proofs.IRGeneration.NativeSourceThirdField
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def stored (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :=
  NativeSourceMaskedFieldStore.s4 cost (NativeSourceMaskedContext.ready cost pre a b c d e f g h i j k tail)
    (((NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory f).land a)
    g a b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i
    (UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail)

theorem entry_pc (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 573) :
    (NativeSourceMaskedContext.ready cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 605 := by
  change ((NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).pc +
    UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [NativeSourceMaskedContext.entry_pc cost pre a b c d e f g h i j k tail pc]
  decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573) :
    run fuel cost 4 (NativeSourceMaskedContext.ready cost pre a b c d e f g h i j k tail) =
      .ok (stored cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceMaskedFieldStore.execute fuel cost _ _ g a b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i
    (UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail)
    code (entry_pc cost pre a b c d e f g h i j k tail pc)
    (NativeSourceMaskedContext.stack cost pre a b c d e f g h i j k tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    run fuel cost 29 pre = .ok (stored cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 25 4 pre _ _
    (NativeSourceMaskedContext.execute fuel cost pre a b c d e f g h i j k tail code pc stack)
    (finish fuel cost pre a b c d e f g h i j k tail code pc)

theorem stack (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (stored cost pre a b c d e f g h i j k tail).stack =
      g :: a :: b :: c :: UInt256.ofNat 632 :: h :: UInt256.ofNat 32 ::
      i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail := by rfl

end Compiler.Proofs.IRGeneration.NativeSourceThirdField
