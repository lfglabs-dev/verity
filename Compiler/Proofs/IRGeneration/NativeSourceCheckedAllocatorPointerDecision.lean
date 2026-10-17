import Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorDecision

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorPointerDecision
open EvmYul EVM EVM.Proof

def pointed (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256) :=
  NativeSourceAllocatorPointer.s5 3 pre size base tail

def overflow (size base : UInt256) := UInt256.lt (base + size) base

def decided (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256) :=
  NativeSourceCheckedAllocatorDecision.decided (pointed pre size base tail)
    (overflow size base) (base + size) tail

theorem pointed_pc (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 919) : (pointed pre size base tail).pc = UInt256.ofNat 924 := by
  change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [pc]; decide

theorem pointed_stack (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256) :
    (pointed pre size base tail).stack = overflow size base :: (base + size) :: tail := by
  rfl

theorem execute (fuel : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 919)
    (stack : pre.stack = size :: base :: tail)
    (gas : 40 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 12) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (decided pre size base tail) := by
  have charged := (NativeSourceCheckedAllocatorPointer.gas_chain pre size base tail (by omega)).2.2.2.2
  change (pointed pre size base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 15 at charged
  rw [NativeSourceCheckedAllocatorPointer.execute (fuel + 6) _ pre size base tail code pc stack (by omega) depth]
  exact NativeSourceCheckedAllocatorDecision.execute fuel (pointed pre size base tail)
    (overflow size base) (base + size) tail code (pointed_pc pre size base tail pc)
    (pointed_stack pre size base tail) (by omega) depth

theorem gas_exact (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256)
    (gas : 40 ≤ pre.gasAvailable.toNat) :
    (decided pre size base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 40 := by
  have charged := (NativeSourceCheckedAllocatorPointer.gas_chain pre size base tail (by omega)).2.2.2.2
  change (pointed pre size base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 15 at charged
  have final := NativeSourceCheckedAllocatorDecision.gas_exact (pointed pre size base tail)
    (overflow size base) (base + size) tail (by omega)
  change (decided pre size base tail).gasAvailable.toNat = _ at final
  omega

theorem destinations (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 919) :
    (decided pre size base tail).pc =
      if NativeSourceCheckedAllocatorDecision.condition (overflow size base) (base + size) != ⟨0⟩
      then UInt256.ofNat 786 else UInt256.ofNat 940 := by
  exact NativeSourceCheckedAllocatorDecision.destinations (pointed pre size base tail)
    (overflow size base) (base + size) tail (pointed_pc pre size base tail pc)

end Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorPointerDecision
