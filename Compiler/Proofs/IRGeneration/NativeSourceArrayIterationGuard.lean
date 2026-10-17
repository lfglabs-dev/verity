import Compiler.Proofs.IRGeneration.NativeSourceArrayIterationBranch

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayIterationGuard
open EvmYul EVM EVM.Proof

def flag (end_ cursor : UInt256) := UInt256.lt cursor end_

def s1 (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 pre).replaceStackAndIncrPC (end_ :: a :: end_ :: cursor :: tail)

def s2 (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre a end_ cursor tail)).replaceStackAndIncrPC (cursor :: end_ :: a :: end_ :: cursor :: tail)

def s3 (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre a end_ cursor tail)).replaceStackAndIncrPC (flag end_ cursor :: a :: end_ :: cursor :: tail)

def s4 (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s3 pre a end_ cursor tail)).replaceStackAndIncrPC (UInt256.ofNat 806 :: flag end_ cursor :: a :: end_ :: cursor :: tail) 3

def decided (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :=
  NativeSourceArrayIterationBranch.branched (s4 pre a end_ cursor tail) (flag end_ cursor) (a :: end_ :: cursor :: tail)

theorem pcs (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 324) :
    (s1 pre a end_ cursor tail).pc = UInt256.ofNat 325 ∧ (s2 pre a end_ cursor tail).pc = UInt256.ofNat 326 ∧
    (s3 pre a end_ cursor tail).pc = UInt256.ofNat 327 ∧ (s4 pre a end_ cursor tail).pc = UInt256.ofNat 330 := by
  simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  rw [pc]; decide

theorem gas_chain (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (gas : 22 ≤ pre.gasAvailable.toNat) :
    (s1 pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 ∧
    (s2 pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 6 ∧
    (s3 pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 ∧
    (s4 pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 12 := by
  have g1 : (s1 pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (s2 pre a end_ cursor tail).gasAvailable.toNat = (s1 pre a end_ cursor tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre a end_ cursor tail).gasAvailable.toNat = (s2 pre a end_ cursor tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre a end_ cursor tail).gasAvailable.toNat = (s3 pre a end_ cursor tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute (fuel : Nat) (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 324)
    (stack : pre.stack = a :: end_ :: cursor :: tail) (gas : 22 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 6) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (decided pre a end_ cursor tail) := by
  obtain ⟨g1, g2, g3, g4⟩ := gas_chain pre a end_ cursor tail gas
  obtain ⟨p1, p2, p3, p4⟩ := pcs pre a end_ cursor tail pc
  rw [NativeSourceArrayIterationSteps.continue324 (fuel + 4) _ pre a end_ (cursor :: tail) code pc stack
    (by omega) (by simp only [List.length_cons]; omega)]
  change EVM.X ((fuel + 3) + 2) _ (s1 pre a end_ cursor tail) = _
  rw [NativeSourceArrayIterationSteps.continue325 (fuel + 3) _ (s1 pre a end_ cursor tail) end_ a end_ cursor tail code p1 rfl
    (by omega) depth]
  change EVM.X ((fuel + 2) + 2) _ (s2 pre a end_ cursor tail) = _
  rw [NativeSourceArrayIterationSteps.continue326 (fuel + 2) _ (s2 pre a end_ cursor tail) cursor end_ (a :: end_ :: cursor :: tail)
    code p2 rfl (by omega) (by simp only [List.length_cons]; omega)]
  change EVM.X ((fuel + 1) + 2) _ (s3 pre a end_ cursor tail) = _
  rw [NativeSourceArrayIterationSteps.continue327 (fuel + 1) _ (s3 pre a end_ cursor tail) (flag end_ cursor :: a :: end_ :: cursor :: tail)
    code p3 rfl (by omega) (by simp only [List.length_cons]; omega)]
  change EVM.X (fuel + 2) _ (s4 pre a end_ cursor tail) = _
  exact NativeSourceArrayIterationBranch.jump_continue fuel (s4 pre a end_ cursor tail) (flag end_ cursor) (a :: end_ :: cursor :: tail)
    code p4 rfl (by omega) (by simp only [List.length_cons]; omega)

theorem gas_exact (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (gas : 22 ≤ pre.gasAvailable.toNat) :
    (decided pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 22 := by
  have charged := (gas_chain pre a end_ cursor tail gas).2.2.2
  have final := NativeSourceArrayIterationBranch.gas_exact (s4 pre a end_ cursor tail) (flag end_ cursor) (a :: end_ :: cursor :: tail) (by omega)
  change (decided pre a end_ cursor tail).gasAvailable.toNat = _ at final
  omega

end Compiler.Proofs.IRGeneration.NativeSourceArrayIterationGuard
