import Compiler.Proofs.IRGeneration.NativeSourceAllocatorLimit

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorGuard
open EvmYul EVM.Proof NativeSourcePreludeDecoded NativeSourceAllocatorOverflowEntry

def guarded (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :=
  NativeSourceAllocatorLimit.guarded cost (tested cost pre base size tail)
    (UInt256.lt (base + amount size) base) (base + amount size) tail

theorem entry_pc (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 910) :
    (tested cost pre base size tail).pc = UInt256.ofNat 924 := by
  change (((((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910) :
    run fuel cost 4 (tested cost pre base size tail) = .ok (guarded cost pre base size tail) := by
  exact NativeSourceAllocatorLimit.full fuel cost (tested cost pre base size tail)
    (UInt256.lt (base + amount size) base) (base + amount size) tail code
    (entry_pc cost pre base size tail pc) (NativeSourceAllocatorOverflowEntry.stack cost pre base size tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (stack : pre.stack = base :: size :: tail) :
    run fuel cost 17 pre = .ok (guarded cost pre base size tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 13 4 pre _ _
    (NativeSourceAllocatorOverflowEntry.execute fuel cost pre base size tail code pc stack)
    (finish fuel cost pre base size tail code pc)

theorem stack (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (guarded cost pre base size tail).stack =
      UInt256.lor (UInt256.gt (base + amount size) (UInt256.ofNat (2^64-1)))
        (UInt256.lt (base + amount size) base) :: (base + amount size) :: tail := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorGuard
