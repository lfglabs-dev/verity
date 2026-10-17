import Compiler.Proofs.IRGeneration.NativeSourceArrayEndChecks

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayEndPrefix
open EvmYul EVM EVM.Proof

def s1 (pre : EVM.State) (n a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 7 :: n :: a :: b :: c :: d :: e :: f :: tail) 2

def s2 (pre : EVM.State) (n a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre n a b c d e f tail)).replaceStackAndIncrPC ((n <<< UInt256.ofNat 7) :: a :: b :: c :: d :: e :: f :: tail) 1

def s3 (pre : EVM.State) (n a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre n a b c d e f tail)).replaceStackAndIncrPC (c :: (n <<< UInt256.ofNat 7) :: a :: b :: c :: d :: e :: f :: tail) 1

def s4 (pre : EVM.State) (n a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s3 pre n a b c d e f tail)).replaceStackAndIncrPC ((c + (n <<< UInt256.ofNat 7)) :: a :: b :: c :: d :: e :: f :: tail) 1

def s5 (pre : EVM.State) (n a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s4 pre n a b c d e f tail)).replaceStackAndIncrPC (((c + (n <<< UInt256.ofNat 7)) + a) :: b :: c :: d :: e :: f :: tail) 1

def s6 (pre : EVM.State) (n a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s5 pre n a b c d e f tail)).replaceStackAndIncrPC ((((c + (n <<< UInt256.ofNat 7)) + a) + b) :: c :: d :: e :: f :: tail) 1

def s7 (pre : EVM.State) (n a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s6 pre n a b c d e f tail)).replaceStackAndIncrPC (c :: (((c + (n <<< UInt256.ofNat 7)) + a) + b) :: d :: e :: f :: tail) 1

theorem pcs (pre : EVM.State) (n a b c d e f : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 304) :
    (s1 pre n a b c d e f tail).pc = UInt256.ofNat 306 ∧
    (s2 pre n a b c d e f tail).pc = UInt256.ofNat 307 ∧
    (s3 pre n a b c d e f tail).pc = UInt256.ofNat 308 ∧
    (s4 pre n a b c d e f tail).pc = UInt256.ofNat 309 ∧
    (s5 pre n a b c d e f tail).pc = UInt256.ofNat 310 ∧
    (s6 pre n a b c d e f tail).pc = UInt256.ofNat 311 ∧
    (s7 pre n a b c d e f tail).pc = UInt256.ofNat 312 := by
  simp only [s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  rw [pc]; decide

theorem gas_chain (pre : EVM.State) (n a b c d e f : UInt256) (tail : Stack UInt256)
    (gas : 21 ≤ pre.gasAvailable.toNat) :
    (s1 pre n a b c d e f tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 ∧
    (s2 pre n a b c d e f tail).gasAvailable.toNat = pre.gasAvailable.toNat - 6 ∧
    (s3 pre n a b c d e f tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 ∧
    (s4 pre n a b c d e f tail).gasAvailable.toNat = pre.gasAvailable.toNat - 12 ∧
    (s5 pre n a b c d e f tail).gasAvailable.toNat = pre.gasAvailable.toNat - 15 ∧
    (s6 pre n a b c d e f tail).gasAvailable.toNat = pre.gasAvailable.toNat - 18 ∧
    (s7 pre n a b c d e f tail).gasAvailable.toNat = pre.gasAvailable.toNat - 21 := by
  have g1 : (s1 pre n a b c d e f tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (s2 pre n a b c d e f tail).gasAvailable.toNat = (s1 pre n a b c d e f tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre n a b c d e f tail).gasAvailable.toNat = (s2 pre n a b c d e f tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre n a b c d e f tail).gasAvailable.toNat = (s3 pre n a b c d e f tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g5 : (s5 pre n a b c d e f tail).gasAvailable.toNat = (s4 pre n a b c d e f tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g6 : (s6 pre n a b c d e f tail).gasAvailable.toNat = (s5 pre n a b c d e f tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g7 : (s7 pre n a b c d e f tail).gasAvailable.toNat = (s6 pre n a b c d e f tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (n a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 304)
    (stack : pre.stack = n :: a :: b :: c :: d :: e :: f :: tail)
    (gas : 21 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1015) :
    EVM.X (fuel + 8) jumps pre = EVM.X (fuel + 1) jumps (s7 pre n a b c d e f tail) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := gas_chain pre n a b c d e f tail gas
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pcs pre n a b c d e f tail pc
  have c1 := NativeSourceArrayEndChecks.continue304 (fuel + 6) jumps pre
    (n :: a :: b :: c :: d :: e :: f :: tail) code pc stack (by omega) (by simp only [List.length_cons]; omega)
  rw [c1]
  have c2 := NativeSourceArrayEndChecks.continue306 (fuel + 5) jumps (s1 pre n a b c d e f tail)
    (UInt256.ofNat 7) n (a :: b :: c :: d :: e :: f :: tail) code p1 rfl (by omega) (by simp only [List.length_cons]; omega)
  change EVM.X ((fuel + 5) + 2) jumps (s1 pre n a b c d e f tail) = _
  rw [c2]
  have c3 := NativeSourceArrayEndChecks.continue307 (fuel + 4) jumps (s2 pre n a b c d e f tail)
    (n <<< UInt256.ofNat 7) a b c (d :: e :: f :: tail) code p2 rfl (by omega) (by simp only [List.length_cons]; omega)
  change EVM.X ((fuel + 4) + 2) jumps (s2 pre n a b c d e f tail) = _
  rw [c3]
  have c4 := NativeSourceArrayEndChecks.continue308 (fuel + 3) jumps (s3 pre n a b c d e f tail)
    c (n <<< UInt256.ofNat 7) (a :: b :: c :: d :: e :: f :: tail) code p3 rfl (by omega) (by simp only [List.length_cons]; omega)
  change EVM.X ((fuel + 3) + 2) jumps (s3 pre n a b c d e f tail) = _
  rw [c4]
  have c5 := NativeSourceArrayEndChecks.continue309 (fuel + 2) jumps (s4 pre n a b c d e f tail)
    (c + (n <<< UInt256.ofNat 7)) a (b :: c :: d :: e :: f :: tail) code p4 rfl (by omega) (by simp only [List.length_cons]; omega)
  change EVM.X ((fuel + 2) + 2) jumps (s4 pre n a b c d e f tail) = _
  rw [c5]
  have c6 := NativeSourceArrayEndChecks.continue310 (fuel + 1) jumps (s5 pre n a b c d e f tail)
    ((c + (n <<< UInt256.ofNat 7)) + a) b (c :: d :: e :: f :: tail) code p5 rfl (by omega) (by simp only [List.length_cons]; omega)
  change EVM.X ((fuel + 1) + 2) jumps (s5 pre n a b c d e f tail) = _
  rw [c6]
  have c7 := NativeSourceArrayEndChecks.continue311 fuel jumps (s6 pre n a b c d e f tail)
    (((c + (n <<< UInt256.ofNat 7)) + a) + b) c (d :: e :: f :: tail) code p6 rfl (by omega) (by simp only [List.length_cons]; omega)
  change EVM.X (fuel + 2) jumps (s6 pre n a b c d e f tail) = _
  rw [c7]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceArrayEndPrefix
