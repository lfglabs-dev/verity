import Compiler.Proofs.IRGeneration.NativeSourceFieldRoundingStore

namespace Compiler.Proofs.IRGeneration.NativeSourceFieldSize
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def ready (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) :=
  NativeSourceFieldRoundingEntry.masked cost (NativeSourceFieldSizeEntry.sized cost pre a b
    (c :: d :: e :: f :: g :: h :: i :: tail))

def stored (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) :=
  NativeSourceFieldRoundingStore.s4 cost (ready cost pre a b c d e f g h i tail)
    (UInt256.lnot (UInt256.ofNat 31)) (a - b) c d e f g h i tail

theorem sub_run (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 619)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: tail) :
    run fuel cost 1 pre = .ok (NativeSourceFieldSizeEntry.sized cost pre a b
      (c :: d :: e :: f :: g :: h :: i :: tail)) := by
  apply NativeSourceFieldLoad.run_one
  exact NativeSourceFieldSizeEntry.step fuel cost pre a b _ code pc stack

theorem rounding (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 619) :
    run fuel cost 2 (NativeSourceFieldSizeEntry.sized cost pre a b
      (c :: d :: e :: f :: g :: h :: i :: tail)) = .ok (ready cost pre a b c d e f g h i tail) := by
  apply NativeSourceFieldRoundingEntry.execute fuel cost
    (NativeSourceFieldSizeEntry.sized cost pre a b (c :: d :: e :: f :: g :: h :: i :: tail)) (by exact code)
  change pre.pc + UInt256.ofNat 1 = _
  rw [pc]; decide

theorem store (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 619) :
    run fuel cost 4 (ready cost pre a b c d e f g h i tail) = .ok (stored cost pre a b c d e f g h i tail) := by
  apply NativeSourceFieldRoundingStore.execute fuel cost (ready cost pre a b c d e f g h i tail) _ _ c d e f g h i tail (by exact code)
  · change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1 = _
    rw [pc]; decide
  · rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 619)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: tail) :
    run fuel cost 7 pre = .ok (stored cost pre a b c d e f g h i tail) := by
  apply NativeSourceSizedPacking.compose fuel cost 1 6 pre _ _ (sub_run fuel cost pre a b c d e f g h i tail code pc stack)
  exact NativeSourceSizedPacking.compose fuel cost 2 4 _ _ _
    (rounding fuel cost pre a b c d e f g h i tail code pc)
    (store fuel cost pre a b c d e f g h i tail code pc)

end Compiler.Proofs.IRGeneration.NativeSourceFieldSize
