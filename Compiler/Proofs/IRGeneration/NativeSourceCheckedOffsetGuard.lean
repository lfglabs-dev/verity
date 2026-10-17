import Compiler.Proofs.IRGeneration.NativeSourceCollateralOffsetGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedOffsetGuard
open EvmYul EVM EVM.Proof NativeSourceCollateralOffsetGuard

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
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 224)
    (stack : pre.stack = offset :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (s1 pre offset tail) := by
  have atPC : pre.pc = UInt256.ofNat 224 := by
    exact pc
  have decoded : decodeAt pre = (.Push .PUSH8, some (limit, 8)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode224]; rfl
  have check := push8_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition1 fuel pre offset tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue2 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 224)
    (stack : pre.stack = offset :: tail)
    (gas : 3 ≤ (s1 pre offset tail).gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 2) jumps (s1 pre offset tail) = EVM.X (fuel + 1) jumps (s2 pre offset tail) := by
  have atPC : (s1 pre offset tail).pc = UInt256.ofNat 233 := by
    simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 pre offset tail) = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre offset tail).pc).getD _ = _
    rw [code, atPC, decode233]; rfl
  have check := NativeSourceFieldStoreChecks.dup2 jumps (s1 pre offset tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition2 fuel pre offset tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue3 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 224)
    (stack : pre.stack = offset :: tail)
    (gas : 3 ≤ (s2 pre offset tail).gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 2) jumps (s2 pre offset tail) = EVM.X (fuel + 1) jumps (s3 pre offset tail) := by
  have atPC : (s2 pre offset tail).pc = UInt256.ofNat 234 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 pre offset tail) = (.GT, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre offset tail).pc).getD _ = _
    rw [code, atPC, decode234]; rfl
  have check := gt_check jumps (s2 pre offset tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition3 fuel pre offset tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue4 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 224)
    (stack : pre.stack = offset :: tail)
    (gas : 3 ≤ (s3 pre offset tail).gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 2) jumps (s3 pre offset tail) = EVM.X (fuel + 1) jumps (s4 pre offset tail) := by
  have atPC : (s3 pre offset tail).pc = UInt256.ofNat 235 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 pre offset tail) = (.Push .PUSH2, some (UInt256.ofNat 91, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 pre offset tail).pc).getD _ = _
    rw [code, atPC, decode235]; rfl
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
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 224)
    (stack : pre.stack = offset :: tail)
    (gas : 12 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 5) jumps pre = EVM.X (fuel + 1) jumps (s4 pre offset tail) := by
  obtain ⟨g1, g2, g3, g4⟩ := gas_chain pre offset tail gas
  rw [continue1 (fuel + 3) jumps pre offset tail code pc stack (by omega) depth]
  rw [continue2 (fuel + 2) jumps pre offset tail code pc stack (by omega) depth]
  rw [continue3 (fuel + 1) jumps pre offset tail code pc stack (by omega) depth]
  rw [continue4 (fuel + 0) jumps pre offset tail code pc stack (by omega) depth]

theorem zero_jump (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 238)
    (stack : pre.stack = UInt256.ofNat 91 :: UInt256.ofNat 0 :: tail)
    (gas : 10 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedReturn.fallthrough pre tail) := by
  have decoded : decodeAt pre = (.JUMPI, none) := by
    unfold decodeAt; rw [code, pc, decode238]; rfl
  have check := NativeSourceJumpChecks.rejection_jumpi pre (UInt256.ofNat 0) tail stack
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) depth
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  exact X_succ_of_continue decoded check (NativeSourceCheckedReturn.zero_transition fuel pre tail stack) rfl

theorem nonzero_jump (fuel : Nat) (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 238)
    (stack : pre.stack = UInt256.ofNat 91 :: condition :: tail) (nonzero : condition ≠ UInt256.ofNat 0)
    (gas : 10 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedJumpRejection.afterJump pre tail) := by
  have decoded : decodeAt pre = (.JUMPI, none) := by
    unfold decodeAt; rw [code, pc, decode238]; rfl
  have check := NativeSourceJumpChecks.rejection_jumpi pre condition tail stack
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) depth
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  exact X_succ_of_continue decoded check (NativeSourceCheckedJumpRejection.transition fuel pre condition tail stack nonzero) rfl

theorem prefix_frame (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 224) :
    (s4 pre offset tail).pc = UInt256.ofNat 238 ∧
      (s4 pre offset tail).stack = UInt256.ofNat 91 :: flag offset :: offset :: tail ∧
      (s4 pre offset tail).executionEnv.code = pre.executionEnv.code := by
  refine ⟨?_, rfl, rfl⟩
  simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  rw [pc]; decide

theorem reject_exact (fuel : Nat) (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 224)
    (stack : pre.stack = offset :: tail) (invalid : 2^64-1 < offset.toNat)
    (gas : 28 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 10) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      .ok (.revert (UInt256.ofNat (pre.gasAvailable.toNat - 28)) ByteArray.empty) := by
  have charged := (gas_chain pre offset tail (by omega)).2.2.2
  have shape := prefix_frame pre offset tail pc
  have jumpGas := NativeSourceCheckedJumpRejection.remaining_gas (s4 pre offset tail) (offset :: tail) (by omega)
  rw [execute_prefix (fuel + 5) _ pre offset tail code pc stack (by omega) depth]
  rw [nonzero_jump (fuel + 4) _ (flag offset) (offset :: tail) (shape.2.2.trans code) shape.1
    shape.2.1 (flag_nonzero offset invalid) (by omega) (by simp only [List.length_cons]; omega)]
  rw [NativeSourceCheckedRejection.execute_exact fuel _
    (NativeSourceCheckedJumpRejection.afterJump (s4 pre offset tail) (offset :: tail)) (shape.2.2.trans code) rfl
    (by omega) (by change (offset :: tail).length ≤ 1022; simp only [List.length_cons]; omega), jumpGas, charged]
  congr 3

theorem accept (fuel : Nat) (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 224)
    (stack : pre.stack = offset :: tail) (valid : offset.toNat ≤ 2^64-1)
    (gas : 22 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 6) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)) := by
  have charged := (gas_chain pre offset tail (by omega)).2.2.2
  have shape := prefix_frame pre offset tail pc
  rw [execute_prefix (fuel + 1) _ pre offset tail code pc stack (by omega) depth]
  exact zero_jump fuel _ (offset :: tail) (shape.2.2.trans code) shape.1
    (by rw [shape.2.1, flag_zero offset valid]) (by omega) (by simp only [List.length_cons]; omega)

theorem accepted_gas (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (gas : 22 ≤ pre.gasAvailable.toNat) :
    (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)).gasAvailable.toNat =
      pre.gasAvailable.toNat - 22 := by
  have charged := (gas_chain pre offset tail (by omega)).2.2.2
  have final : (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)).gasAvailable.toNat =
      (s4 pre offset tail).gasAvailable.toNat - 10 :=
    NativeSourceCheckedRejection.gas_sub _ 10 (by decide) (by omega)
  omega

theorem accepted_frame (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 224) :
    (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)).pc = UInt256.ofNat 239 ∧
      (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)).stack = offset :: tail ∧
      (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)).toState = pre.toState ∧
      (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)).memory = pre.memory := by
  refine ⟨?_, rfl, rfl, rfl⟩
  change (s4 pre offset tail).pc + UInt256.ofNat 1 = _
  rw [(prefix_frame pre offset tail pc).1]; decide

end Compiler.Proofs.IRGeneration.NativeSourceCheckedOffsetGuard


