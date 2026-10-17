import Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataDecodes

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataSteps
open EvmYul EVM EVM.Proof

theorem continue312 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 312)
    (stack : pre.stack = tail) (gas : 2 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 2 pre).replaceStackAndIncrPC (UInt256.ofNat pre.executionEnv.calldata.size :: tail) 1) := by
  have decoded : decodeAt pre = (.CALLDATASIZE, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayCalldataDecodes.decode312]; rfl
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

theorem continue313 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 313)
    (stack : pre.stack = a :: b :: c :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (c :: a :: b :: c :: tail) 1) := by
  have decoded : decodeAt pre = (.DUP3, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayCalldataDecodes.decode313]; rfl
  have check := NativeSourceGuardChecks.dup3 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.DUP3, none)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (c :: a :: b :: c :: tail) 1) := by
    change EvmYul.dup 3 (stepPre 3 pre) = _
    unfold EvmYul.dup
    simp only [stepPre, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem continue314 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 314)
    (stack : pre.stack = a :: b :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.gt a b :: tail) 1) := by
  have decoded : decodeAt pre = (.GT, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayCalldataDecodes.decode314]; rfl
  have check := NativeSourceCheckedOffsetGuard.gt_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.GT, none)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.gt a b :: tail) 1) := by
    change EVM.execBinOp UInt256.gt (stepPre 3 pre) = _
    unfold EVM.execBinOp
    simp only [stepPre, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem continue315 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 315)
    (stack : pre.stack = tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 91 :: tail) 3) := by
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 91, 2)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayCalldataDecodes.decode315]; rfl
  have check := NativeSourceCheckedPushRejection.push2_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simpa only [stack] using (show tail.length < 1024 by omega))
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.Push .PUSH2, some (UInt256.ofNat 91, 2))) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 91 :: tail) 3) := by
    change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (_ :: pre.stack) _) = _
    rw [stack]
  exact X_succ_of_continue decoded check step rfl

end Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataSteps
