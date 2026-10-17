import Compiler.Proofs.IRGeneration.NativeSourceFieldStore

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstField
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def stored (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :=
  NativeSourceFieldStore.s4 cost (NativeSourceFieldLoad.loaded cost pre a b c d e f g h i j k tail)
    ((NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory d)
    e f a g a b c (UInt256.ofNat 632)
    (h :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail)

theorem entry_pc (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 573) :
    (NativeSourceFieldLoad.loaded cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 592 := by
  change (NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).pc + UInt256.ofNat 1 = _
  rw [NativeSourceFieldLoad.entry_pc cost pre a b c d e f g h i j k tail pc]
  decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573) :
    run fuel cost 4 (NativeSourceFieldLoad.loaded cost pre a b c d e f g h i j k tail) =
      .ok (stored cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceFieldStore.execute fuel cost _ _ e f a g a b c (UInt256.ofNat 632)
    (h :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail)
    code (entry_pc cost pre a b c d e f g h i j k tail pc)
    (NativeSourceFieldLoad.stack cost pre a b c d e f g h i j k tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    run fuel cost 18 pre = .ok (stored cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 14 4 pre _ _
    (NativeSourceFieldLoad.execute fuel cost pre a b c d e f g h i j k tail code pc stack)
    (finish fuel cost pre a b c d e f g h i j k tail code pc)

theorem stack (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (stored cost pre a b c d e f g h i j k tail).stack =
      e :: f :: a :: g :: a :: b :: c :: UInt256.ofNat 632 :: h :: UInt256.ofNat 32 ::
      i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail := by rfl

end Compiler.Proofs.IRGeneration.NativeSourceFirstField
