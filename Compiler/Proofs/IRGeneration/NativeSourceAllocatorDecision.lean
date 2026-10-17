import Compiler.Proofs.IRGeneration.NativeSourceAllocatorBranch

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorDecision
open EvmYul EVM.Proof NativeSourcePreludeDecoded NativeSourceAllocatorOverflowEntry

def flag (base size : UInt256) :=
  UInt256.lor (UInt256.gt (base + amount size) (UInt256.ofNat (2^64-1)))
    (UInt256.lt (base + amount size) base)
def decided (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :=
  NativeSourceAllocatorBranch.branched cost (NativeSourceAllocatorGuard.guarded cost pre base size tail)
    (flag base size) ((base + amount size) :: tail)

theorem entry_pc (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 910) :
    (NativeSourceAllocatorGuard.guarded cost pre base size tail).pc = UInt256.ofNat 936 := by
  change (((((((((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 9) +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910) :
    run fuel cost 2 (NativeSourceAllocatorGuard.guarded cost pre base size tail) =
      .ok (decided cost pre base size tail) := by
  exact NativeSourceAllocatorBranch.execute fuel cost
    (NativeSourceAllocatorGuard.guarded cost pre base size tail) (flag base size) ((base + amount size) :: tail)
    code (entry_pc cost pre base size tail pc) (NativeSourceAllocatorGuard.stack cost pre base size tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (stack : pre.stack = base :: size :: tail) :
    run fuel cost 19 pre = .ok (decided cost pre base size tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 17 2 pre _ _
    (NativeSourceAllocatorGuard.execute fuel cost pre base size tail code pc stack)
    (finish fuel cost pre base size tail code pc)

theorem destinations (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 910) :
    (decided cost pre base size tail).pc =
      if flag base size != ⟨0⟩ then UInt256.ofNat 786 else UInt256.ofNat 940 := by
  exact NativeSourceAllocatorBranch.destinations cost _ (flag base size) _ (entry_pc cost pre base size tail pc)

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorDecision
