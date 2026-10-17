import Compiler.Proofs.IRGeneration.NativeSourceArrayElementDecodes

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayElementSteps
open EvmYul EVM EVM.Proof

theorem continue806 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 806)
    (gas : 1 ≤ pre.gasAvailable.toNat) (depth : pre.stack.length ≤ 1024) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps ((stepPre 1 pre).incrPC) := by
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayElementDecodes.decode806]; rfl
  have check := Z_JUMPDEST jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word, GasConstants.Gjumpdest] using gas) depth
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  exact X_succ_of_continue decoded check (step_JUMPDEST fuel 1 pre) (H_JUMPDEST _)

theorem continue807 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 807)
    (stack : pre.stack = tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 128 :: tail) 2) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 128, 1)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayElementDecodes.decode807]; rfl
  have check := NativeSourceGuardChecks.push1 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.Push .PUSH1, some (UInt256.ofNat 128, 1))) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 128 :: tail) 2) := by
    change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (_ :: pre.stack) _) = _
    rw [stack]
  exact X_succ_of_continue decoded check step rfl

theorem continue809 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b c d : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 809)
    (stack : pre.stack = a :: b :: c :: d :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (d :: a :: b :: c :: d :: tail) 1) := by
  have decoded : decodeAt pre = (.DUP4, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayElementDecodes.decode809]; rfl
  have check := NativeSourceFieldStoreChecks.dup4 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.DUP4, none)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (d :: a :: b :: c :: d :: tail) 1) := by
    change EvmYul.dup 4 (stepPre 3 pre) = _
    unfold EvmYul.dup
    simp only [stepPre, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem continue810 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 810)
    (stack : pre.stack = tail) (gas : 2 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 2 pre).replaceStackAndIncrPC (UInt256.ofNat pre.executionEnv.calldata.size :: tail) 1) := by
  have decoded : decodeAt pre = (.CALLDATASIZE, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayElementDecodes.decode810]; rfl
  have check := NativeSourceSpanChecks.calldatasize jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 2 (some (.CALLDATASIZE, none)) pre =
      .ok ((stepPre 2 pre).replaceStackAndIncrPC (UInt256.ofNat pre.executionEnv.calldata.size :: tail) 1) := by
    change EvmYul.step (τ := .EVM) .CALLDATASIZE none (stepPre 2 pre) = _
    unfold EvmYul.step
    simp only [stepPre, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem continue811 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 811)
    (stack : pre.stack = a :: b :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.sub a b :: tail) 1) := by
  have decoded : decodeAt pre = (.SUB, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayElementDecodes.decode811]; rfl
  have check := NativeSourceGuardChecks.sub jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.SUB, none)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.sub a b :: tail) 1) := by
    change EVM.execBinOp UInt256.sub (stepPre 3 pre) = _
    unfold EVM.execBinOp
    simp only [stepPre, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem continue812 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 812)
    (stack : pre.stack = a :: b :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.slt a b :: tail) 1) := by
  have decoded : decodeAt pre = (.SLT, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayElementDecodes.decode812]; rfl
  have check := NativeSourceSpanChecks.slt jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.SLT, none)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.slt a b :: tail) 1) := by
    change EVM.execBinOp UInt256.slt (stepPre 3 pre) = _
    unfold EVM.execBinOp
    simp only [stepPre, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem continue813 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 813)
    (stack : pre.stack = tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 91 :: tail) 3) := by
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 91, 2)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayElementDecodes.decode813]; rfl
  have check := NativeSourceCheckedPushRejection.push2_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simpa only [stack] using (show tail.length < 1024 by omega))
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.Push .PUSH2, some (UInt256.ofNat 91, 2))) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 91 :: tail) 3) := by
    change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (_ :: pre.stack) _) = _
    rw [stack]
  exact X_succ_of_continue decoded check step rfl

end Compiler.Proofs.IRGeneration.NativeSourceArrayElementSteps
