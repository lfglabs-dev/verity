import Compiler.Proofs.IRGeneration.NativeSourceArrayAllocatorJump

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayCallPrefix
open EvmYul EVM EVM.Proof

def s1 (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail) 3

def s2 (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre array n x pointer tail)).replaceStackAndIncrPC (UInt256.ofNat 32 :: UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail) 2

def s3 (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre array n x pointer tail)).replaceStackAndIncrPC (n :: UInt256.ofNat 32 :: UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail) 1

def s4 (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s3 pre array n x pointer tail)).replaceStackAndIncrPC (UInt256.ofNat 5 :: n :: UInt256.ofNat 32 :: UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail) 2

def s5 (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s4 pre array n x pointer tail)).replaceStackAndIncrPC ((n <<< UInt256.ofNat 5) :: UInt256.ofNat 32 :: UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail) 1

def s6 (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s5 pre array n x pointer tail)).replaceStackAndIncrPC (((n <<< UInt256.ofNat 5) + UInt256.ofNat 32) :: UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail) 1

def s7 (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s6 pre array n x pointer tail)).replaceStackAndIncrPC (pointer :: ((n <<< UInt256.ofNat 5) + UInt256.ofNat 32) :: UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail) 1

def s8 (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s7 pre array n x pointer tail)).replaceStackAndIncrPC (UInt256.ofNat 910 :: pointer :: ((n <<< UInt256.ofNat 5) + UInt256.ofNat 32) :: UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail) 3

theorem continue1 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (array n x pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 277)
    (stack : pre.stack = array :: n :: x :: pointer :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (s1 pre array n x pointer tail) := by
  have atPC : pre.pc = UInt256.ofNat 277 := by
    exact pc
  exact NativeSourceArrayOperandChecks.continue277 fuel jumps pre (array :: n :: x :: pointer :: tail)
    code atPC stack gas (by simp only [List.length_cons]; omega)

theorem continue2 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (array n x pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 277)
    (_stack : pre.stack = array :: n :: x :: pointer :: tail)
    (gas : 3 ≤ (s1 pre array n x pointer tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s1 pre array n x pointer tail) = EVM.X (fuel + 1) jumps (s2 pre array n x pointer tail) := by
  have atPC : (s1 pre array n x pointer tail).pc = UInt256.ofNat 280 := by
    simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  exact NativeSourceArrayOperandChecks.continue280 fuel jumps (s1 pre array n x pointer tail) (UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail)
    code atPC rfl gas (by simp only [List.length_cons]; omega)

theorem continue3 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (array n x pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 277)
    (_stack : pre.stack = array :: n :: x :: pointer :: tail)
    (gas : 3 ≤ (s2 pre array n x pointer tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s2 pre array n x pointer tail) = EVM.X (fuel + 1) jumps (s3 pre array n x pointer tail) := by
  have atPC : (s2 pre array n x pointer tail).pc = UInt256.ofNat 282 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  exact NativeSourceArrayOperandChecks.continue282 fuel jumps (s2 pre array n x pointer tail) (UInt256.ofNat 32) (UInt256.ofNat 292) array n (x :: pointer :: tail)
    code atPC rfl gas (by simp only [List.length_cons]; omega)

theorem continue4 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (array n x pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 277)
    (_stack : pre.stack = array :: n :: x :: pointer :: tail)
    (gas : 3 ≤ (s3 pre array n x pointer tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s3 pre array n x pointer tail) = EVM.X (fuel + 1) jumps (s4 pre array n x pointer tail) := by
  have atPC : (s3 pre array n x pointer tail).pc = UInt256.ofNat 283 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  exact NativeSourceArrayOperandChecks.continue283 fuel jumps (s3 pre array n x pointer tail) (n :: UInt256.ofNat 32 :: UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail)
    code atPC rfl gas (by simp only [List.length_cons]; omega)

theorem continue5 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (array n x pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 277)
    (_stack : pre.stack = array :: n :: x :: pointer :: tail)
    (gas : 3 ≤ (s4 pre array n x pointer tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s4 pre array n x pointer tail) = EVM.X (fuel + 1) jumps (s5 pre array n x pointer tail) := by
  have atPC : (s4 pre array n x pointer tail).pc = UInt256.ofNat 285 := by
    simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  exact NativeSourceArrayOperandChecks.continue285 fuel jumps (s4 pre array n x pointer tail) (UInt256.ofNat 5) n (UInt256.ofNat 32 :: UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail)
    code atPC rfl gas (by simp only [List.length_cons]; omega)

theorem continue6 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (array n x pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 277)
    (_stack : pre.stack = array :: n :: x :: pointer :: tail)
    (gas : 3 ≤ (s5 pre array n x pointer tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s5 pre array n x pointer tail) = EVM.X (fuel + 1) jumps (s6 pre array n x pointer tail) := by
  have atPC : (s5 pre array n x pointer tail).pc = UInt256.ofNat 286 := by
    simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  exact NativeSourceArrayOperandChecks.continue286 fuel jumps (s5 pre array n x pointer tail) (n <<< UInt256.ofNat 5) (UInt256.ofNat 32) (UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail)
    code atPC rfl gas (by simp only [List.length_cons]; omega)

theorem continue7 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (array n x pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 277)
    (_stack : pre.stack = array :: n :: x :: pointer :: tail)
    (gas : 3 ≤ (s6 pre array n x pointer tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s6 pre array n x pointer tail) = EVM.X (fuel + 1) jumps (s7 pre array n x pointer tail) := by
  have atPC : (s6 pre array n x pointer tail).pc = UInt256.ofNat 287 := by
    simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  exact NativeSourceArrayOperandChecks.continue287 fuel jumps (s6 pre array n x pointer tail) ((n <<< UInt256.ofNat 5) + UInt256.ofNat 32) (UInt256.ofNat 292) array n x pointer tail
    code atPC rfl gas (by omega)

theorem continue8 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (array n x pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 277)
    (_stack : pre.stack = array :: n :: x :: pointer :: tail)
    (gas : 3 ≤ (s7 pre array n x pointer tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s7 pre array n x pointer tail) = EVM.X (fuel + 1) jumps (s8 pre array n x pointer tail) := by
  have atPC : (s7 pre array n x pointer tail).pc = UInt256.ofNat 288 := by
    simp only [s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  exact NativeSourceArrayOperandChecks.continue288 fuel jumps (s7 pre array n x pointer tail) (pointer :: ((n <<< UInt256.ofNat 5) + UInt256.ofNat 32) :: UInt256.ofNat 292 :: array :: n :: x :: pointer :: tail)
    code atPC rfl gas (by simp only [List.length_cons]; omega)

theorem gas_chain (pre : EVM.State) (array n x pointer : UInt256) (tail : Stack UInt256)
    (gas : 24 ≤ pre.gasAvailable.toNat) :
    (s1 pre array n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 ∧
      (s2 pre array n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 6 ∧
      (s3 pre array n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 ∧
      (s4 pre array n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 12 ∧
      (s5 pre array n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 15 ∧
      (s6 pre array n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 18 ∧
      (s7 pre array n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 21 ∧
      (s8 pre array n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 24 := by
  have g1 : (s1 pre array n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (s2 pre array n x pointer tail).gasAvailable.toNat = (s1 pre array n x pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre array n x pointer tail).gasAvailable.toNat = (s2 pre array n x pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre array n x pointer tail).gasAvailable.toNat = (s3 pre array n x pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g5 : (s5 pre array n x pointer tail).gasAvailable.toNat = (s4 pre array n x pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g6 : (s6 pre array n x pointer tail).gasAvailable.toNat = (s5 pre array n x pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g7 : (s7 pre array n x pointer tail).gasAvailable.toNat = (s6 pre array n x pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g8 : (s8 pre array n x pointer tail).gasAvailable.toNat = (s7 pre array n x pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute_prefix (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (array n x pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 277)
    (stack : pre.stack = array :: n :: x :: pointer :: tail)
    (gas : 24 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 9) jumps pre = EVM.X (fuel + 1) jumps (s8 pre array n x pointer tail) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := gas_chain pre array n x pointer tail gas
  rw [continue1 (fuel + 7) jumps pre array n x pointer tail code pc stack (by omega) depth]
  rw [continue2 (fuel + 6) jumps pre array n x pointer tail code pc stack (by omega) depth]
  rw [continue3 (fuel + 5) jumps pre array n x pointer tail code pc stack (by omega) depth]
  rw [continue4 (fuel + 4) jumps pre array n x pointer tail code pc stack (by omega) depth]
  rw [continue5 (fuel + 3) jumps pre array n x pointer tail code pc stack (by omega) depth]
  rw [continue6 (fuel + 2) jumps pre array n x pointer tail code pc stack (by omega) depth]
  rw [continue7 (fuel + 1) jumps pre array n x pointer tail code pc stack (by omega) depth]
  rw [continue8 (fuel + 0) jumps pre array n x pointer tail code pc stack (by omega) depth]

end Compiler.Proofs.IRGeneration.NativeSourceArrayCallPrefix
