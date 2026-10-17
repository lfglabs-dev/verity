import Compiler.Proofs.IRGeneration.NativeSourceArrayElementBranch

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayElementGuard
open EvmYul EVM EVM.Proof

def size (pre : EVM.State) := UInt256.ofNat pre.executionEnv.calldata.size
def flag (pre : EVM.State) (cursor : UInt256) := UInt256.slt (size pre - cursor) (UInt256.ofNat 128)

def s1 (pre : EVM.State) (_a _end_ _cursor : UInt256) (_tail : Stack UInt256) :=
  (stepPre 1 pre).incrPC

def s2 (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre a end_ cursor tail)).replaceStackAndIncrPC (UInt256.ofNat 128 :: a :: end_ :: cursor :: tail) 2

def s3 (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre a end_ cursor tail)).replaceStackAndIncrPC (cursor :: UInt256.ofNat 128 :: a :: end_ :: cursor :: tail) 1

def s4 (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :=
  (stepPre 2 (s3 pre a end_ cursor tail)).replaceStackAndIncrPC (size pre :: cursor :: UInt256.ofNat 128 :: a :: end_ :: cursor :: tail) 1

def s5 (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s4 pre a end_ cursor tail)).replaceStackAndIncrPC ((size pre - cursor) :: UInt256.ofNat 128 :: a :: end_ :: cursor :: tail) 1

def s6 (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s5 pre a end_ cursor tail)).replaceStackAndIncrPC (flag pre cursor :: a :: end_ :: cursor :: tail) 1

def s7 (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s6 pre a end_ cursor tail)).replaceStackAndIncrPC (UInt256.ofNat 91 :: flag pre cursor :: a :: end_ :: cursor :: tail) 3

def decided (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :=
  NativeSourceArrayElementBranch.branched (s7 pre a end_ cursor tail) (flag pre cursor) (a :: end_ :: cursor :: tail)

theorem pcs (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 806) :
    (s1 pre a end_ cursor tail).pc = UInt256.ofNat 807 ∧
    (s2 pre a end_ cursor tail).pc = UInt256.ofNat 809 ∧
    (s3 pre a end_ cursor tail).pc = UInt256.ofNat 810 ∧
    (s4 pre a end_ cursor tail).pc = UInt256.ofNat 811 ∧
    (s5 pre a end_ cursor tail).pc = UInt256.ofNat 812 ∧
    (s6 pre a end_ cursor tail).pc = UInt256.ofNat 813 ∧
    (s7 pre a end_ cursor tail).pc = UInt256.ofNat 816 := by
  simp only [s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  rw [pc]; decide

theorem gas_chain (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (gas : 28 ≤ pre.gasAvailable.toNat) :
    (s1 pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 1 ∧
    (s2 pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 4 ∧
    (s3 pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 7 ∧
    (s4 pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 ∧
    (s5 pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 12 ∧
    (s6 pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 15 ∧
    (s7 pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 18 := by
  have g1 : (s1 pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 1 :=
    NativeSourceCheckedRejection.gas_sub _ 1 (by decide) (by omega)
  have g2 : (s2 pre a end_ cursor tail).gasAvailable.toNat = (s1 pre a end_ cursor tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre a end_ cursor tail).gasAvailable.toNat = (s2 pre a end_ cursor tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre a end_ cursor tail).gasAvailable.toNat = (s3 pre a end_ cursor tail).gasAvailable.toNat - 2 :=
    NativeSourceCheckedRejection.gas_sub _ 2 (by decide) (by omega)
  have g5 : (s5 pre a end_ cursor tail).gasAvailable.toNat = (s4 pre a end_ cursor tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g6 : (s6 pre a end_ cursor tail).gasAvailable.toNat = (s5 pre a end_ cursor tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g7 : (s7 pre a end_ cursor tail).gasAvailable.toNat = (s6 pre a end_ cursor tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute (fuel : Nat) (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 806)
    (stack : pre.stack = a :: end_ :: cursor :: tail) (gas : 28 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 9) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (decided pre a end_ cursor tail) := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pcs pre a end_ cursor tail pc
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := gas_chain pre a end_ cursor tail gas
  rw [NativeSourceArrayElementSteps.continue806 (fuel + 7) _ pre code pc (by omega)
    (by simp only [stack, List.length_cons]; omega)]
  change EVM.X ((fuel + 6) + 2) _ (s1 pre a end_ cursor tail) = _
  rw [NativeSourceArrayElementSteps.continue807 (fuel + 6) _ (s1 pre a end_ cursor tail) (a :: end_ :: cursor :: tail)
    code p1 (by change pre.stack = _; exact stack) (by omega) (by first | omega | (simp only [List.length_cons]; omega))]
  change EVM.X ((fuel + 5) + 2) _ (s2 pre a end_ cursor tail) = _
  rw [NativeSourceArrayElementSteps.continue809 (fuel + 5) _ (s2 pre a end_ cursor tail) (UInt256.ofNat 128) a end_ cursor tail
    code p2 rfl (by omega) (by omega)]
  change EVM.X ((fuel + 4) + 2) _ (s3 pre a end_ cursor tail) = _
  rw [NativeSourceArrayElementSteps.continue810 (fuel + 4) _ (s3 pre a end_ cursor tail) (cursor :: UInt256.ofNat 128 :: a :: end_ :: cursor :: tail)
    code p3 rfl (by omega) (by first | omega | (simp only [List.length_cons]; omega))]
  change EVM.X ((fuel + 3) + 2) _ (s4 pre a end_ cursor tail) = _
  rw [NativeSourceArrayElementSteps.continue811 (fuel + 3) _ (s4 pre a end_ cursor tail) (size pre) cursor (UInt256.ofNat 128 :: a :: end_ :: cursor :: tail)
    code p4 rfl (by omega) (by first | omega | (simp only [List.length_cons]; omega))]
  change EVM.X ((fuel + 2) + 2) _ (s5 pre a end_ cursor tail) = _
  rw [NativeSourceArrayElementSteps.continue812 (fuel + 2) _ (s5 pre a end_ cursor tail) (size pre - cursor) (UInt256.ofNat 128) (a :: end_ :: cursor :: tail)
    code p5 rfl (by omega) (by first | omega | (simp only [List.length_cons]; omega))]
  change EVM.X ((fuel + 1) + 2) _ (s6 pre a end_ cursor tail) = _
  rw [NativeSourceArrayElementSteps.continue813 (fuel + 1) _ (s6 pre a end_ cursor tail) (flag pre cursor :: a :: end_ :: cursor :: tail)
    code p6 rfl (by omega) (by first | omega | (simp only [List.length_cons]; omega))]
  change EVM.X (fuel + 2) _ (s7 pre a end_ cursor tail) = _
  exact NativeSourceArrayElementBranch.jump_continue fuel (s7 pre a end_ cursor tail) (flag pre cursor)
    (a :: end_ :: cursor :: tail) code p7 rfl (by omega) (by first | omega | (simp only [List.length_cons]; omega))

theorem gas_exact (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (gas : 28 ≤ pre.gasAvailable.toNat) :
    (decided pre a end_ cursor tail).gasAvailable.toNat = pre.gasAvailable.toNat - 28 := by
  have charged := (gas_chain pre a end_ cursor tail gas).2.2.2.2.2.2
  have final := NativeSourceArrayElementBranch.gas_exact (s7 pre a end_ cursor tail) (flag pre cursor)
    (a :: end_ :: cursor :: tail) (by omega)
  change (decided pre a end_ cursor tail).gasAvailable.toNat = _ at final
  omega

end Compiler.Proofs.IRGeneration.NativeSourceArrayElementGuard
