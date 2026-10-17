import Compiler.Proofs.IRGeneration.NativeSourceArrayLoopSetupChecks

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayLoopSetupPrefix
open EvmYul EVM EVM.Proof

def s1 (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 32 :: a :: n :: x :: pointer :: tail) 2

def s2 (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre a n x pointer tail)).replaceStackAndIncrPC (UInt256.ofNat 4 :: UInt256.ofNat 32 :: a :: n :: x :: pointer :: tail) 2

def s3 (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre a n x pointer tail)).replaceStackAndIncrPC (UInt256.ofNat 32 :: UInt256.ofNat 4 :: UInt256.ofNat 32 :: a :: n :: x :: pointer :: tail) 1

def s4 (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s3 pre a n x pointer tail)).replaceStackAndIncrPC (pointer :: UInt256.ofNat 32 :: UInt256.ofNat 4 :: UInt256.ofNat 32 :: a :: n :: x :: pointer :: tail) 1

def s5 (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s4 pre a n x pointer tail)).replaceStackAndIncrPC ((pointer + UInt256.ofNat 32) :: UInt256.ofNat 4 :: UInt256.ofNat 32 :: a :: n :: x :: pointer :: tail) 1

def s6 (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s5 pre a n x pointer tail)).replaceStackAndIncrPC (n :: UInt256.ofNat 4 :: UInt256.ofNat 32 :: a :: (pointer + UInt256.ofNat 32) :: x :: pointer :: tail) 1

theorem pcs (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 296) :
    (s1 pre a n x pointer tail).pc = UInt256.ofNat 298 ∧
    (s2 pre a n x pointer tail).pc = UInt256.ofNat 300 ∧
    (s3 pre a n x pointer tail).pc = UInt256.ofNat 301 ∧
    (s4 pre a n x pointer tail).pc = UInt256.ofNat 302 ∧
    (s5 pre a n x pointer tail).pc = UInt256.ofNat 303 ∧
    (s6 pre a n x pointer tail).pc = UInt256.ofNat 304 := by
  simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  rw [pc]; decide

theorem gas_chain (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256)
    (gas : 18 ≤ pre.gasAvailable.toNat) :
    (s1 pre a n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 ∧
    (s2 pre a n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 6 ∧
    (s3 pre a n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 ∧
    (s4 pre a n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 12 ∧
    (s5 pre a n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 15 ∧
    (s6 pre a n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 18 := by
  have g1 : (s1 pre a n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (s2 pre a n x pointer tail).gasAvailable.toNat = (s1 pre a n x pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre a n x pointer tail).gasAvailable.toNat = (s2 pre a n x pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre a n x pointer tail).gasAvailable.toNat = (s3 pre a n x pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g5 : (s5 pre a n x pointer tail).gasAvailable.toNat = (s4 pre a n x pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g6 : (s6 pre a n x pointer tail).gasAvailable.toNat = (s5 pre a n x pointer tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (a n x pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 296)
    (stack : pre.stack = a :: n :: x :: pointer :: tail)
    (gas : 18 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1012) :
    EVM.X (fuel + 7) jumps pre = EVM.X (fuel + 1) jumps (s6 pre a n x pointer tail) := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := gas_chain pre a n x pointer tail gas
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := pcs pre a n x pointer tail pc
  have c1 := NativeSourceArrayLoopSetupChecks.continue296 (fuel + 5) jumps pre
    (a :: n :: x :: pointer :: tail) code pc stack (by omega) (by first | omega | (simp only [List.length_cons]; omega))
  rw [c1]
  have c2 := NativeSourceArrayLoopSetupChecks.continue298 (fuel + 4) jumps (s1 pre a n x pointer tail)
    (UInt256.ofNat 32 :: a :: n :: x :: pointer :: tail) code p1 rfl (by omega) (by first | omega | (simp only [List.length_cons]; omega))
  change EVM.X ((fuel + 4) + 2) jumps (s1 pre a n x pointer tail) = _
  rw [c2]
  have c3 := NativeSourceArrayLoopSetupChecks.continue300 (fuel + 3) jumps (s2 pre a n x pointer tail)
    (UInt256.ofNat 4) (UInt256.ofNat 32) (a :: n :: x :: pointer :: tail) code p2 rfl (by omega) (by first | omega | (simp only [List.length_cons]; omega))
  change EVM.X ((fuel + 3) + 2) jumps (s2 pre a n x pointer tail) = _
  rw [c3]
  have c4 := NativeSourceArrayLoopSetupChecks.continue301 (fuel + 2) jumps (s3 pre a n x pointer tail)
    (UInt256.ofNat 32) (UInt256.ofNat 4) (UInt256.ofNat 32) a n x pointer tail code p3 rfl (by omega) (by omega)
  change EVM.X ((fuel + 2) + 2) jumps (s3 pre a n x pointer tail) = _
  rw [c4]
  have c5 := NativeSourceArrayLoopSetupChecks.continue302 (fuel + 1) jumps (s4 pre a n x pointer tail)
    pointer (UInt256.ofNat 32) (UInt256.ofNat 4 :: UInt256.ofNat 32 :: a :: n :: x :: pointer :: tail) code p4 rfl (by omega) (by first | omega | (simp only [List.length_cons]; omega))
  change EVM.X ((fuel + 1) + 2) jumps (s4 pre a n x pointer tail) = _
  rw [c5]
  have c6 := NativeSourceArrayLoopSetupChecks.continue303 fuel jumps (s5 pre a n x pointer tail)
    (pointer + UInt256.ofNat 32) (UInt256.ofNat 4) (UInt256.ofNat 32) a n (x :: pointer :: tail) code p5 rfl (by omega) (by first | omega | (simp only [List.length_cons]; omega))
  change EVM.X (fuel + 2) jumps (s5 pre a n x pointer tail) = _
  rw [c6]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceArrayLoopSetupPrefix
