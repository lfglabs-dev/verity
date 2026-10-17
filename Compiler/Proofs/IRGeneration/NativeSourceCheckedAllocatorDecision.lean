import Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorExit

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorDecision
open EvmYul EVM EVM.Proof

def guarded (pre : EVM.State) (overflow pointer : UInt256) (tail : Stack UInt256) :=
  NativeSourceAllocatorLimit.guarded 3 pre overflow pointer tail

def condition (overflow pointer : UInt256) :=
  UInt256.lor (UInt256.gt pointer (UInt256.ofNat (2^64-1))) overflow

def decided (pre : EVM.State) (overflow pointer : UInt256) (tail : Stack UInt256) :=
  NativeSourceCheckedAllocatorBranch.branched (guarded pre overflow pointer tail)
    (condition overflow pointer) (pointer :: tail)

theorem guarded_stack (pre : EVM.State) (overflow pointer : UInt256) (tail : Stack UInt256) :
    (guarded pre overflow pointer tail).stack = condition overflow pointer :: pointer :: tail := by
  rfl

theorem execute (fuel : Nat) (pre : EVM.State) (overflow pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 924)
    (stack : pre.stack = overflow :: pointer :: tail)
    (gas : 25 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 7) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (decided pre overflow pointer tail) := by
  have charged := NativeSourceCheckedLimitPrefix.gas_exact pre overflow pointer tail (by omega)
  change (guarded pre overflow pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 12 at charged
  rw [NativeSourceCheckedLimitPrefix.execute (fuel + 2) _ pre overflow pointer tail code pc stack (by omega) depth]
  exact NativeSourceCheckedAllocatorBranch.execute fuel (guarded pre overflow pointer tail)
    (condition overflow pointer) (pointer :: tail) code
    (NativeSourceCheckedLimitPrefix.output_pc pre overflow pointer tail pc)
    (guarded_stack pre overflow pointer tail) (by omega) (by simp only [List.length_cons]; omega)

theorem gas_exact (pre : EVM.State) (overflow pointer : UInt256) (tail : Stack UInt256)
    (gas : 25 ≤ pre.gasAvailable.toNat) :
    (decided pre overflow pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 25 := by
  have charged := NativeSourceCheckedLimitPrefix.gas_exact pre overflow pointer tail (by omega)
  change (guarded pre overflow pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 12 at charged
  have final := NativeSourceCheckedAllocatorBranch.gas_exact (guarded pre overflow pointer tail)
    (condition overflow pointer) (pointer :: tail) (by omega)
  change (decided pre overflow pointer tail).gasAvailable.toNat = _ at final
  omega

theorem destinations (pre : EVM.State) (overflow pointer : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 924) :
    (decided pre overflow pointer tail).pc =
      if condition overflow pointer != ⟨0⟩ then UInt256.ofNat 786 else UInt256.ofNat 940 := by
  exact NativeSourceCheckedAllocatorBranch.destinations (guarded pre overflow pointer tail)
    (condition overflow pointer) (pointer :: tail)
    (NativeSourceCheckedLimitPrefix.output_pc pre overflow pointer tail pc)

end Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorDecision
