import Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorRounding

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorEntry
open EvmYul EVM EVM.Proof

def rounded (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :=
  NativeSourceAllocatorRounding.s5 3 (NativeSourceCheckedAllocatorStart.s3 pre base size tail)
    (UInt256.ofNat 31) size base tail

theorem entry_pc (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 910) :
    (NativeSourceCheckedAllocatorStart.s3 pre base size tail).pc = UInt256.ofNat 914 := by
  change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2 = _
  rw [pc]; decide

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (stack : pre.stack = base :: size :: tail)
    (gas : 22 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 9) jumps pre = EVM.X (fuel + 1) jumps (rounded pre base size tail) := by
  have charged := (NativeSourceCheckedAllocatorStart.gas_chain pre base size tail (by omega)).2.2
  rw [NativeSourceCheckedAllocatorStart.execute (fuel + 5) jumps pre base size tail code pc stack (by omega) (by omega)]
  exact NativeSourceCheckedAllocatorRounding.execute fuel jumps _ (UInt256.ofNat 31) size base tail
    code (entry_pc pre base size tail pc) rfl (by omega) depth

theorem gas_exact (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (gas : 22 ≤ pre.gasAvailable.toNat) :
    (rounded pre base size tail).gasAvailable.toNat = pre.gasAvailable.toNat - 22 := by
  have first := (NativeSourceCheckedAllocatorStart.gas_chain pre base size tail (by omega)).2.2
  have second := (NativeSourceCheckedAllocatorRounding.gas_chain
    (NativeSourceCheckedAllocatorStart.s3 pre base size tail) (UInt256.ofNat 31) size base tail (by omega)).2.2.2.2
  change (rounded pre base size tail).gasAvailable.toNat = _ at second
  omega

theorem frame (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (rounded pre base size tail).stack =
      UInt256.land (size + UInt256.ofNat 31) (UInt256.lnot (UInt256.ofNat 31)) :: base :: tail ∧
    (rounded pre base size tail).memory = pre.memory ∧ (rounded pre base size tail).toState = pre.toState := by
  exact ⟨rfl, rfl, rfl⟩

theorem output_pc (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 910) : (rounded pre base size tail).pc = UInt256.ofNat 919 := by
  change (((((NativeSourceCheckedAllocatorStart.s3 pre base size tail).pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [entry_pc pre base size tail pc]; decide

end Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorEntry
