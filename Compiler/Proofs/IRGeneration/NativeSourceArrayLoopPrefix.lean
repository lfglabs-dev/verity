import Compiler.Proofs.IRGeneration.NativeSourceArrayLoopEntry

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayLoopPrefix
open EvmYul EVM EVM.Proof

def s1 (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 36 :: a :: b :: c :: tail) 2

def s2 (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre a b c tail)).replaceStackAndIncrPC ((UInt256.ofNat 36 + a) :: b :: c :: tail)

def s3 (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre a b c tail)).replaceStackAndIncrPC (c :: b :: (UInt256.ofNat 36 + a) :: tail)

def s4 (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256) :=
  (stepPre 1 (s3 pre a b c tail)).incrPC

theorem pcs (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 319) :
    (s1 pre a b c tail).pc = UInt256.ofNat 321 ∧ (s2 pre a b c tail).pc = UInt256.ofNat 322 ∧
    (s3 pre a b c tail).pc = UInt256.ofNat 323 ∧ (s4 pre a b c tail).pc = UInt256.ofNat 324 := by
  simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  rw [pc]; decide

theorem gas_chain (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256)
    (gas : 10 ≤ pre.gasAvailable.toNat) :
    (s1 pre a b c tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 ∧
    (s2 pre a b c tail).gasAvailable.toNat = pre.gasAvailable.toNat - 6 ∧
    (s3 pre a b c tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 ∧
    (s4 pre a b c tail).gasAvailable.toNat = pre.gasAvailable.toNat - 10 := by
  have g1 : (s1 pre a b c tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (s2 pre a b c tail).gasAvailable.toNat = (s1 pre a b c tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre a b c tail).gasAvailable.toNat = (s2 pre a b c tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre a b c tail).gasAvailable.toNat = (s3 pre a b c tail).gasAvailable.toNat - 1 :=
    NativeSourceCheckedRejection.gas_sub _ 1 (by decide) (by omega)
  omega

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 319)
    (stack : pre.stack = a :: b :: c :: tail) (gas : 10 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 5) jumps pre = EVM.X (fuel + 1) jumps (s4 pre a b c tail) := by
  obtain ⟨p1, p2, p3, p4⟩ := pcs pre a b c tail pc
  obtain ⟨g1, g2, g3, g4⟩ := gas_chain pre a b c tail gas
  rw [NativeSourceArrayLoopEntry.continue319 (fuel + 3) jumps pre (a :: b :: c :: tail) code pc stack
    (by omega) (by simp only [List.length_cons]; omega)]
  change EVM.X ((fuel + 2) + 2) jumps (s1 pre a b c tail) = _
  rw [NativeSourceArrayLoopEntry.continue321 (fuel + 2) jumps (s1 pre a b c tail) (UInt256.ofNat 36) a (b :: c :: tail)
    code p1 rfl (by omega) (by simp only [List.length_cons]; omega)]
  change EVM.X ((fuel + 1) + 2) jumps (s2 pre a b c tail) = _
  rw [NativeSourceArrayLoopEntry.continue322 (fuel + 1) jumps (s2 pre a b c tail) (UInt256.ofNat 36 + a) b c tail
    code p2 rfl (by omega) (by omega)]
  change EVM.X (fuel + 2) jumps (s3 pre a b c tail) = _
  exact NativeSourceArrayLoopEntry.continue323 fuel jumps (s3 pre a b c tail) code p3 (by omega)
    (by change (c :: b :: (UInt256.ofNat 36 + a) :: tail).length ≤ 1024; simp only [List.length_cons]; omega)

end Compiler.Proofs.IRGeneration.NativeSourceArrayLoopPrefix
