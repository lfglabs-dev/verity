import Compiler.Proofs.IRGeneration.NativeSourceCollateralLengthGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedLengthGuard
open EvmYul EVM EVM.Proof NativeSourceCollateralLengthGuard

theorem push8_check (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 0 ≤ pre.stack.length ∧ pre.stack.length ≤ 1023) :
    Z jumps (.Push .PUSH8) pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state (.Push .PUSH8) = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [depth.2]

theorem gt_check (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 2 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024) :
    Z jumps .GT pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .GT = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 2 by omega, show ¬pre.stack.length - 2 + 1 > 1024 by omega]

theorem continue1 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 258)
    (stack : pre.stack = offset :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (s1 pre offset tail) := by
  have atPC : pre.pc = UInt256.ofNat 258 := by
    exact pc
  have decoded : decodeAt pre = (.Push .PUSH8, some (limit, 8)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode258]; rfl
  have check := push8_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition1 fuel pre offset tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue2 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 258)
    (stack : pre.stack = offset :: tail)
    (gas : 3 ≤ (s1 pre offset tail).gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 2) jumps (s1 pre offset tail) = EVM.X (fuel + 1) jumps (s2 pre offset tail) := by
  have atPC : (s1 pre offset tail).pc = UInt256.ofNat 267 := by
    simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 pre offset tail) = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre offset tail).pc).getD _ = _
    rw [code, atPC, decode267]; rfl
  have check := NativeSourceFieldStoreChecks.dup2 jumps (s1 pre offset tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition2 fuel pre offset tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue3 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 258)
    (stack : pre.stack = offset :: tail)
    (gas : 3 ≤ (s2 pre offset tail).gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 2) jumps (s2 pre offset tail) = EVM.X (fuel + 1) jumps (s3 pre offset tail) := by
  have atPC : (s2 pre offset tail).pc = UInt256.ofNat 268 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 pre offset tail) = (.GT, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre offset tail).pc).getD _ = _
    rw [code, atPC, decode268]; rfl
  have check := gt_check jumps (s2 pre offset tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition3 fuel pre offset tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue4 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 258)
    (stack : pre.stack = offset :: tail)
    (gas : 3 ≤ (s3 pre offset tail).gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 2) jumps (s3 pre offset tail) = EVM.X (fuel + 1) jumps (s4 pre offset tail) := by
  have atPC : (s3 pre offset tail).pc = UInt256.ofNat 269 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 pre offset tail) = (.Push .PUSH2, some (UInt256.ofNat 786, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 pre offset tail).pc).getD _ = _
    rw [code, atPC, decode269]; rfl
  have check := NativeSourceCheckedPushRejection.push2_check jumps (s3 pre offset tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition4 fuel pre offset tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem gas_chain (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (gas : 12 ≤ pre.gasAvailable.toNat) :
    (s1 pre offset tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 ∧
      (s2 pre offset tail).gasAvailable.toNat = pre.gasAvailable.toNat - 6 ∧
      (s3 pre offset tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 ∧
      (s4 pre offset tail).gasAvailable.toNat = pre.gasAvailable.toNat - 12 := by
  have g1 : (s1 pre offset tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (s2 pre offset tail).gasAvailable.toNat = (s1 pre offset tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre offset tail).gasAvailable.toNat = (s2 pre offset tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre offset tail).gasAvailable.toNat = (s3 pre offset tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute_prefix (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 258)
    (stack : pre.stack = offset :: tail)
    (gas : 12 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 5) jumps pre = EVM.X (fuel + 1) jumps (s4 pre offset tail) := by
  obtain ⟨g1, g2, g3, g4⟩ := gas_chain pre offset tail gas
  rw [continue1 (fuel + 3) jumps pre offset tail code pc stack (by omega) depth]
  rw [continue2 (fuel + 2) jumps pre offset tail code pc stack (by omega) depth]
  rw [continue3 (fuel + 1) jumps pre offset tail code pc stack (by omega) depth]
  rw [continue4 (fuel + 0) jumps pre offset tail code pc stack (by omega) depth]

theorem prefix_frame (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 258) :
    (s4 pre offset tail).pc = UInt256.ofNat 272 ∧
      (s4 pre offset tail).stack = UInt256.ofNat 786 :: flag offset :: offset :: tail ∧
      (s4 pre offset tail).executionEnv.code = pre.executionEnv.code := by
  refine ⟨?_, rfl, rfl⟩
  simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  rw [pc]; decide

end Compiler.Proofs.IRGeneration.NativeSourceCheckedLengthGuard
