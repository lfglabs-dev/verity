import Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataBranch

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataGuard
open EvmYul EVM EVM.Proof

def size (pre : EVM.State) := UInt256.ofNat pre.executionEnv.calldata.size

def flag (pre : EVM.State) (end_ : UInt256) := UInt256.gt end_ (size pre)

def s1 (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256) :=
  (stepPre 2 pre).replaceStackAndIncrPC (size pre :: a :: end_ :: tail)

def s2 (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre a end_ tail)).replaceStackAndIncrPC (end_ :: size pre :: a :: end_ :: tail)

def s3 (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre a end_ tail)).replaceStackAndIncrPC (flag pre end_ :: a :: end_ :: tail)

def s4 (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s3 pre a end_ tail)).replaceStackAndIncrPC (UInt256.ofNat 91 :: flag pre end_ :: a :: end_ :: tail) 3

def decided (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256) :=
  NativeSourceArrayCalldataBranch.branched (s4 pre a end_ tail) (flag pre end_) (a :: end_ :: tail)

theorem pcs (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 312) :
    (s1 pre a end_ tail).pc = UInt256.ofNat 313 ∧ (s2 pre a end_ tail).pc = UInt256.ofNat 314 ∧
    (s3 pre a end_ tail).pc = UInt256.ofNat 315 ∧ (s4 pre a end_ tail).pc = UInt256.ofNat 318 := by
  simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  rw [pc]; decide

theorem gas_chain (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256)
    (gas : 21 ≤ pre.gasAvailable.toNat) :
    (s1 pre a end_ tail).gasAvailable.toNat = pre.gasAvailable.toNat - 2 ∧
    (s2 pre a end_ tail).gasAvailable.toNat = pre.gasAvailable.toNat - 5 ∧
    (s3 pre a end_ tail).gasAvailable.toNat = pre.gasAvailable.toNat - 8 ∧
    (s4 pre a end_ tail).gasAvailable.toNat = pre.gasAvailable.toNat - 11 := by
  have g1 : (s1 pre a end_ tail).gasAvailable.toNat = pre.gasAvailable.toNat - 2 :=
    NativeSourceCheckedRejection.gas_sub _ 2 (by decide) (by omega)
  have g2 : (s2 pre a end_ tail).gasAvailable.toNat = (s1 pre a end_ tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre a end_ tail).gasAvailable.toNat = (s2 pre a end_ tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre a end_ tail).gasAvailable.toNat = (s3 pre a end_ tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute (fuel : Nat) (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 312)
    (stack : pre.stack = a :: end_ :: tail) (gas : 21 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 6) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (decided pre a end_ tail) := by
  obtain ⟨g1, g2, g3, g4⟩ := gas_chain pre a end_ tail gas
  obtain ⟨p1, p2, p3, p4⟩ := pcs pre a end_ tail pc
  rw [NativeSourceArrayCalldataSteps.continue312 (fuel + 4) _ pre (a :: end_ :: tail) code pc stack
    (by omega) (by simp only [List.length_cons]; omega)]
  change EVM.X ((fuel + 3) + 2) _ (s1 pre a end_ tail) = _
  rw [NativeSourceArrayCalldataSteps.continue313 (fuel + 3) _ (s1 pre a end_ tail) (size pre) a end_ tail code p1 rfl
    (by omega) depth]
  change EVM.X ((fuel + 2) + 2) _ (s2 pre a end_ tail) = _
  rw [NativeSourceArrayCalldataSteps.continue314 (fuel + 2) _ (s2 pre a end_ tail) end_ (size pre) (a :: end_ :: tail)
    code p2 rfl (by omega) (by simp only [List.length_cons]; omega)]
  change EVM.X ((fuel + 1) + 2) _ (s3 pre a end_ tail) = _
  rw [NativeSourceArrayCalldataSteps.continue315 (fuel + 1) _ (s3 pre a end_ tail) (flag pre end_ :: a :: end_ :: tail)
    code p3 rfl (by omega) (by simp only [List.length_cons]; omega)]
  change EVM.X (fuel + 2) _ (s4 pre a end_ tail) = _
  exact NativeSourceArrayCalldataBranch.jump_continue fuel (s4 pre a end_ tail) (flag pre end_) (a :: end_ :: tail)
    code p4 rfl (by omega) (by simp only [List.length_cons]; omega)

theorem gas_exact (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256)
    (gas : 21 ≤ pre.gasAvailable.toNat) :
    (decided pre a end_ tail).gasAvailable.toNat = pre.gasAvailable.toNat - 21 := by
  have charged := (gas_chain pre a end_ tail gas).2.2.2
  have final := NativeSourceArrayCalldataBranch.gas_exact (s4 pre a end_ tail) (flag pre end_) (a :: end_ :: tail) (by omega)
  change (decided pre a end_ tail).gasAvailable.toNat = _ at final
  omega

end Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataGuard
