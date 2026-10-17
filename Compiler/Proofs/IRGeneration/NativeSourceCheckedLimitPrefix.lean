import Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorLimit

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedLimitPrefix
open EvmYul EVM EVM.Proof NativeSourceAllocatorLimit

theorem gas_chain (pre : EVM.State) (limit overflow pointer : UInt256) (tail : Stack UInt256)
    (gas : 9 ≤ pre.gasAvailable.toNat) :
    (s1 3 pre limit overflow pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 ∧
      (s2 3 pre limit overflow pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 6 ∧
      (s3 3 pre limit overflow pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 := by
  have g1 : (s1 3 pre limit overflow pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (s2 3 pre limit overflow pointer tail).gasAvailable.toNat = (s1 3 pre limit overflow pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 3 pre limit overflow pointer tail).gasAvailable.toNat = (s2 3 pre limit overflow pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute_inner (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (limit overflow pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 933)
    (stack : pre.stack = limit :: overflow :: pointer :: tail)
    (gas : 9 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 4) jumps pre = EVM.X (fuel + 1) jumps (s3 3 pre limit overflow pointer tail) := by
  obtain ⟨g1, g2, g3⟩ := gas_chain pre limit overflow pointer tail gas
  rw [NativeSourceCheckedAllocatorLimit.continue1 (fuel + 2) jumps pre limit overflow pointer tail code pc stack (by omega) depth]
  rw [NativeSourceCheckedAllocatorLimit.continue2 (fuel + 1) jumps pre limit overflow pointer tail code pc stack (by omega) depth]
  rw [NativeSourceCheckedAllocatorLimit.continue3 fuel jumps pre limit overflow pointer tail code pc stack (by omega) depth]

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (overflow pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 924)
    (stack : pre.stack = overflow :: pointer :: tail)
    (gas : 12 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 5) jumps pre = EVM.X (fuel + 1) jumps (guarded 3 pre overflow pointer tail) := by
  have charged : (pushed 3 pre).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have atPC : (pushed 3 pre).pc = UInt256.ofNat 933 := by
    change pre.pc + UInt256.ofNat 9 = _; rw [pc]; decide
  rw [NativeSourceCheckedAllocatorLimit.push_continue (fuel + 3) jumps pre code pc (by omega)
    (by simp only [stack, List.length_cons]; omega)]
  exact execute_inner fuel jumps _ (UInt256.ofNat (2^64-1)) overflow pointer tail code atPC
    (by change UInt256.ofNat (2^64-1) :: pre.stack = _; rw [stack]) (by omega) depth

theorem gas_exact (pre : EVM.State) (overflow pointer : UInt256) (tail : Stack UInt256)
    (gas : 12 ≤ pre.gasAvailable.toNat) :
    (guarded 3 pre overflow pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 12 := by
  have pushedGas : (pushed 3 pre).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have final := (gas_chain (pushed 3 pre) (UInt256.ofNat (2^64-1)) overflow pointer tail (by omega)).2.2
  change (guarded 3 pre overflow pointer tail).gasAvailable.toNat = _ at final
  omega

theorem output_pc (pre : EVM.State) (overflow pointer : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 924) : (guarded 3 pre overflow pointer tail).pc = UInt256.ofNat 936 := by
  change (((pre.pc + UInt256.ofNat 9) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [pc]; decide

end Compiler.Proofs.IRGeneration.NativeSourceCheckedLimitPrefix
