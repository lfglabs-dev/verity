import Compiler.Proofs.IRGeneration.NativeSourceArrayIterationDecodes

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayIterationSteps
open EvmYul EVM EVM.Proof

theorem continue324 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 324)
    (stack : pre.stack = a :: b :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (b :: a :: b :: tail) 1) := by
  have decoded : decodeAt pre = (.DUP2, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayIterationDecodes.decode324]; rfl
  have check := NativeSourceFieldStoreChecks.dup2 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.DUP2, none)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (b :: a :: b :: tail) 1) := by
    change EvmYul.dup 2 (stepPre 3 pre) = _
    unfold EvmYul.dup
    simp only [stepPre, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem continue325 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b c d : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 325)
    (stack : pre.stack = a :: b :: c :: d :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (d :: a :: b :: c :: d :: tail) 1) := by
  have decoded : decodeAt pre = (.DUP4, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayIterationDecodes.decode325]; rfl
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

theorem continue326 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 326)
    (stack : pre.stack = a :: b :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.lt a b :: tail) 1) := by
  have decoded : decodeAt pre = (.LT, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayIterationDecodes.decode326]; rfl
  have check := NativeSourceCheckedAllocatorPointer.lt_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.LT, none)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.lt a b :: tail) 1) := by
    change EVM.execBinOp UInt256.lt (stepPre 3 pre) = _
    unfold EVM.execBinOp
    simp only [stepPre, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem continue327 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 327)
    (stack : pre.stack = tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 806 :: tail) 3) := by
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 806, 2)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayIterationDecodes.decode327]; rfl
  have check := NativeSourceCheckedPushRejection.push2_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simpa only [stack] using (show tail.length < 1024 by omega))
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.Push .PUSH2, some (UInt256.ofNat 806, 2))) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 806 :: tail) 3) := by
    change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (_ :: pre.stack) _) = _
    rw [stack]
  exact X_succ_of_continue decoded check step rfl

end Compiler.Proofs.IRGeneration.NativeSourceArrayIterationSteps
