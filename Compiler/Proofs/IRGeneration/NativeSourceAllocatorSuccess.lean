import Compiler.Proofs.IRGeneration.NativeSourceAllocatorReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorSuccess
open EvmYul EVM.Proof NativeSourcePreludeDecoded NativeSourceAllocatorOverflowEntry

def returned (cost : Nat) (pre : EVM.State) (base size target : UInt256) (tail : Stack UInt256) :=
  NativeSourceAllocatorReturn.returned cost (NativeSourceAllocatorDecision.decided cost pre base size (target :: tail))
    (base + amount size) target tail

theorem entry_pc (cost : Nat) (pre : EVM.State) (base size target : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 910) (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩) :
    (NativeSourceAllocatorDecision.decided cost pre base size (target :: tail)).pc = UInt256.ofNat 940 := by
  rw [NativeSourceAllocatorDecision.destinations cost pre base size (target :: tail) pc, guard]
  decide

theorem entry_stack (cost : Nat) (pre : EVM.State) (base size target : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorDecision.decided cost pre base size (target :: tail)).stack =
      (base + amount size) :: target :: tail := by
  rfl

theorem finish (fuel cost : Nat) (pre : EVM.State) (base size target : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩) :
    run fuel cost 3 (NativeSourceAllocatorDecision.decided cost pre base size (target :: tail)) =
      .ok (returned cost pre base size target tail) := by
  exact NativeSourceAllocatorReturn.execute fuel cost
    (NativeSourceAllocatorDecision.decided cost pre base size (target :: tail)) (base + amount size) target tail
    code (entry_pc cost pre base size target tail pc guard) (entry_stack cost pre base size target tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (base size target : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (stack : pre.stack = base :: size :: target :: tail)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩) :
    run fuel cost 22 pre = .ok (returned cost pre base size target tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 19 3 pre _ _
    (NativeSourceAllocatorDecision.execute fuel cost pre base size (target :: tail) code pc stack)
    (finish fuel cost pre base size target tail code pc guard)

theorem target (cost : Nat) (pre : EVM.State) (base size address : UInt256) (tail : Stack UInt256) :
    (returned cost pre base size address tail).pc = address := by
  rfl

theorem stack (cost : Nat) (pre : EVM.State) (base size address : UInt256) (tail : Stack UInt256) :
    (returned cost pre base size address tail).stack = tail := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorSuccess
