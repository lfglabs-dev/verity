import Compiler.Proofs.IRGeneration.NativeSourceAllocatorRounding

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorRoundedEntry
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def rounded (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :=
  NativeSourceAllocatorRounding.s5 cost (NativeSourceAllocatorStart.s3 cost pre base size tail)
    (UInt256.ofNat 31) size base tail

theorem entry_pc (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 910) :
    (NativeSourceAllocatorStart.s3 cost pre base size tail).pc = UInt256.ofNat 914 := by
  change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2 = _
  rw [pc]; decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910) :
    run fuel cost 5 (NativeSourceAllocatorStart.s3 cost pre base size tail) =
      .ok (rounded cost pre base size tail) := by
  exact NativeSourceAllocatorRounding.execute fuel cost
    (NativeSourceAllocatorStart.s3 cost pre base size tail) (UInt256.ofNat 31) size base tail
    code (entry_pc cost pre base size tail pc) (by rfl)

theorem execute (fuel cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (stack : pre.stack = base :: size :: tail) :
    run fuel cost 8 pre = .ok (rounded cost pre base size tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 3 5 pre _ _
    (NativeSourceAllocatorStart.execute fuel cost pre base size tail code pc stack)
    (finish fuel cost pre base size tail code pc)

theorem stack (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (rounded cost pre base size tail).stack =
      UInt256.land (size + UInt256.ofNat 31) (UInt256.lnot (UInt256.ofNat 31)) :: base :: tail := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorRoundedEntry
