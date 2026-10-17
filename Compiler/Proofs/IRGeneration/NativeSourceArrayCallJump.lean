import Compiler.Proofs.IRGeneration.NativeSourceArrayCallPrefix

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayCallJump
open EvmYul EVM EVM.Proof NativeSourceArrayCallPrefix

def operands (array n x pointer : UInt256) (tail : Stack UInt256) :=
  pointer :: ((n <<< UInt256.ofNat 5) + UInt256.ofNat 32) :: UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail

def called (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256) :=
  NativeSourceArrayAllocatorJump.jumped (s8 pre array n x pointer tail) (operands array n x pointer tail)

theorem prefix_pc (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 277) : (s8 pre array n x pointer tail).pc = UInt256.ofNat 291 := by
  simp only [s8, s7, s6, s5, s4, s3, s2, s1, stepPre,
    EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  rw [pc]; decide

theorem execute (fuel : Nat) (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 277)
    (stack : pre.stack = array :: n :: x :: pointer :: tail)
    (gas : 32 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 10) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (called pre array n x pointer tail) := by
  have charged := (gas_chain pre array n x pointer tail (by omega)).2.2.2.2.2.2.2
  rw [execute_prefix (fuel + 1) _ pre array n x pointer tail code pc stack (by omega) depth]
  exact NativeSourceArrayAllocatorJump.jump_continue fuel _ (operands array n x pointer tail)
    code (prefix_pc pre array n x pointer tail pc) rfl (by omega)
    (by simp only [operands, List.length_cons]; omega)

theorem gas_exact (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256)
    (gas : 32 ≤ pre.gasAvailable.toNat) :
    (called pre array n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 32 := by
  have charged := (gas_chain pre array n x pointer tail (by omega)).2.2.2.2.2.2.2
  have jump := NativeSourceArrayAllocatorJump.jump_gas (s8 pre array n x pointer tail)
    (operands array n x pointer tail) (by omega)
  change (called pre array n x pointer tail).gasAvailable.toNat = _ at jump
  omega

theorem frame (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256) :
    (called pre array n x pointer tail).pc = UInt256.ofNat 910 ∧
    (called pre array n x pointer tail).stack = operands array n x pointer tail ∧
    (called pre array n x pointer tail).memory = pre.memory ∧
    (called pre array n x pointer tail).toState = pre.toState := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Compiler.Proofs.IRGeneration.NativeSourceArrayCallJump
