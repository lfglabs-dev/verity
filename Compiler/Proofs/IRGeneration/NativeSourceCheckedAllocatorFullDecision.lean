import Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorPointerDecision

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorFullDecision
open EvmYul EVM EVM.Proof

def amount (size : UInt256) :=
  UInt256.land (size + UInt256.ofNat 31) (UInt256.lnot (UInt256.ofNat 31))

def decided (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :=
  NativeSourceCheckedAllocatorPointerDecision.decided (NativeSourceCheckedAllocatorEntry.rounded pre base size tail)
    (amount size) base tail

def condition (base size : UInt256) :=
  NativeSourceCheckedAllocatorDecision.condition
    (NativeSourceCheckedAllocatorPointerDecision.overflow (amount size) base) (base + amount size)

theorem execute (fuel : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (stack : pre.stack = base :: size :: tail)
    (gas : 62 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 20) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (decided pre base size tail) := by
  have charged := NativeSourceCheckedAllocatorEntry.gas_exact pre base size tail (by omega)
  rw [NativeSourceCheckedAllocatorEntry.execute (fuel + 11) _ pre base size tail code pc stack (by omega) depth]
  exact NativeSourceCheckedAllocatorPointerDecision.execute fuel (NativeSourceCheckedAllocatorEntry.rounded pre base size tail)
    (amount size) base tail code (NativeSourceCheckedAllocatorEntry.output_pc pre base size tail pc)
    (NativeSourceCheckedAllocatorEntry.frame pre base size tail).1 (by omega) depth

theorem gas_exact (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (gas : 62 ≤ pre.gasAvailable.toNat) :
    (decided pre base size tail).gasAvailable.toNat = pre.gasAvailable.toNat - 62 := by
  have charged := NativeSourceCheckedAllocatorEntry.gas_exact pre base size tail (by omega)
  have final := NativeSourceCheckedAllocatorPointerDecision.gas_exact
    (NativeSourceCheckedAllocatorEntry.rounded pre base size tail) (amount size) base tail (by omega)
  change (decided pre base size tail).gasAvailable.toNat = _ at final
  omega

theorem destinations (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 910) :
    (decided pre base size tail).pc =
      if condition base size != ⟨0⟩ then UInt256.ofNat 786 else UInt256.ofNat 940 := by
  exact NativeSourceCheckedAllocatorPointerDecision.destinations
    (NativeSourceCheckedAllocatorEntry.rounded pre base size tail) (amount size) base tail
    (NativeSourceCheckedAllocatorEntry.output_pc pre base size tail pc)

theorem pointer_frame (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256) :
    (NativeSourceCheckedAllocatorPointerDecision.decided pre size base tail).stack = (base + size) :: tail ∧
    (NativeSourceCheckedAllocatorPointerDecision.decided pre size base tail).memory = pre.memory ∧
    (NativeSourceCheckedAllocatorPointerDecision.decided pre size base tail).toState = pre.toState := by
  exact ⟨rfl, rfl, rfl⟩

theorem frame (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (decided pre base size tail).stack = (base + amount size) :: tail ∧
    (decided pre base size tail).memory = pre.memory ∧
    (decided pre base size tail).toState = pre.toState := by
  have afterPointer := pointer_frame (NativeSourceCheckedAllocatorEntry.rounded pre base size tail)
    (amount size) base tail
  have afterEntry := NativeSourceCheckedAllocatorEntry.frame pre base size tail
  exact ⟨afterPointer.1, afterPointer.2.1.trans afterEntry.2.1, afterPointer.2.2.trans afterEntry.2.2⟩

end Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorFullDecision
