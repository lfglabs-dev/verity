import Compiler.Proofs.IRGeneration.NativeSourceSecondFieldLoad
import Compiler.Proofs.IRGeneration.NativeSourceSecondFieldStore

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondField
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def stored (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :=
  NativeSourceSecondFieldStore.s4 cost (NativeSourceSecondFieldLoad.loaded cost pre a b c d e f g h i j k tail)
    ((NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory e)
    f a g a b c (UInt256.ofNat 632) h
    (UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail)

theorem entry_pc (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 573) :
    (NativeSourceSecondFieldLoad.loaded cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 598 := by
  change (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).pc + UInt256.ofNat 1 = _
  rw [NativeSourceSecondFieldLoad.entry_pc cost pre a b c d e f g h i j k tail pc]
  decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573) :
    run fuel cost 4 (NativeSourceSecondFieldLoad.loaded cost pre a b c d e f g h i j k tail) =
      .ok (stored cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceSecondFieldStore.execute fuel cost _ _ f a g a b c (UInt256.ofNat 632) h
    (UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail)
    code (entry_pc cost pre a b c d e f g h i j k tail pc)
    (NativeSourceSecondFieldLoad.stack cost pre a b c d e f g h i j k tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    run fuel cost 23 pre = .ok (stored cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 19 4 pre _ _
    (NativeSourceSecondFieldLoad.execute fuel cost pre a b c d e f g h i j k tail code pc stack)
    (finish fuel cost pre a b c d e f g h i j k tail code pc)

theorem stack (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (stored cost pre a b c d e f g h i j k tail).stack =
      f :: a :: g :: a :: b :: c :: UInt256.ofNat 632 :: h :: UInt256.ofNat 32 ::
      i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail := by rfl

end Compiler.Proofs.IRGeneration.NativeSourceSecondField
