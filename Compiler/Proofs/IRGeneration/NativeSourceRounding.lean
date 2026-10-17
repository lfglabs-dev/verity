import Compiler.Proofs.IRGeneration.NativeSourceRoundingStore

namespace Compiler.Proofs.IRGeneration.NativeSourceRounding
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def rounded (cost : Nat) (pre : EVM.State) (size a b c : UInt256) (tail : Stack UInt256) :=
  NativeSourceRoundingStore.s4 cost (NativeSourceRoundingEntry.masked cost pre)
    (UInt256.lnot (UInt256.ofNat 31)) size a b c tail

theorem entry_pc (cost : Nat) (pre : EVM.State) (pc : pre.pc = UInt256.ofNat 669) :
    (NativeSourceRoundingEntry.masked cost pre).pc = UInt256.ofNat 672 := by
  change (pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1 = _
  rw [pc]; decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (size a b c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 669)
    (stack : pre.stack = size :: a :: b :: c :: tail) :
    run fuel cost 4 (NativeSourceRoundingEntry.masked cost pre) = .ok (rounded cost pre size a b c tail) := by
  have shape : (NativeSourceRoundingEntry.masked cost pre).stack =
      UInt256.lnot (UInt256.ofNat 31) :: size :: a :: b :: c :: tail := by
    change UInt256.lnot (UInt256.ofNat 31) :: pre.stack = _
    rw [stack]
  exact NativeSourceRoundingStore.execute fuel cost (NativeSourceRoundingEntry.masked cost pre)
    (UInt256.lnot (UInt256.ofNat 31)) size a b c tail code (entry_pc cost pre pc) shape

theorem execute (fuel cost : Nat) (pre : EVM.State) (size a b c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 669)
    (stack : pre.stack = size :: a :: b :: c :: tail) :
    run fuel cost 6 pre = .ok (rounded cost pre size a b c tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 2 4 pre _ _
    (NativeSourceRoundingEntry.execute fuel cost pre code pc)
    (finish fuel cost pre size a b c tail code pc stack)

theorem stack (cost : Nat) (pre : EVM.State) (size a b c : UInt256) (tail : Stack UInt256) :
    (rounded cost pre size a b c tail).stack = size :: a :: b :: c :: tail := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceRounding
