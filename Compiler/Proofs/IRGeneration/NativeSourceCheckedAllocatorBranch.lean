import Compiler.Proofs.IRGeneration.NativeSourceCheckedLimitPrefix

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorBranch
open EvmYul EVM EVM.Proof NativeSourceAllocatorBranch

def branched (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256) : EVM.State :=
  { stepPre 10 (pushed 3 pre) with
    pc := if condition != ⟨0⟩ then UInt256.ofNat 786 else (pushed 3 pre).pc + UInt256.ofNat 1,
    stack := tail }

theorem push_continue (fuel : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 936)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : pre.stack.length ≤ 1023) :
    EVM.X (fuel + 2) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (pushed 3 pre) := by
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 786, 2)) := by
    unfold decodeAt; rw [code, pc, decode936]; rfl
  have check := NativeSourceCheckedPushRejection.push2_check (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) (by omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := push fuel 3 pre code pc
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem jump_continue (fuel : Nat) (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 936)
    (stack : pre.stack = condition :: tail)
    (gas : 10 ≤ (pushed 3 pre).gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (pushed 3 pre) =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (branched pre condition tail) := by
  have atPC : (pushed 3 pre).pc = UInt256.ofNat 939 := by
    change pre.pc + UInt256.ofNat 3 = _; rw [pc]; decide
  have decoded : decodeAt (pushed 3 pre) = (.JUMPI, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (pushed 3 pre).pc).getD _ = _
    rw [code, atPC, decode939]; rfl
  have lookup : EVM.X.notIn (pushed 3 pre).stack[0]? (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) = false := by
    change (!(EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)).contains (UInt256.ofNat 786)) = false
    rw [NativeSourceJumpChecks.contains_of_mem _ _ NativeSourceLengthAccept.panic_destination]; rfl
  have check := NativeSourceJumpChecks.jumpi _ (pushed 3 pre)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by change 2 ≤ (UInt256.ofNat 786 :: pre.stack).length ∧ (UInt256.ofNat 786 :: pre.stack).length ≤ 1024
        simp only [stack, List.length_cons]; omega) lookup
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 10 (some (.JUMPI, none)) (pushed 3 pre) = .ok (branched pre condition tail) := by
    change EvmYul.step (τ := .EVM) .JUMPI none (stepPre 10 (pushed 3 pre)) = _
    unfold EvmYul.step
    simp only [stepPre, pushed, EVM.State.replaceStackAndIncrPC, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem execute (fuel : Nat) (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 936)
    (stack : pre.stack = condition :: tail)
    (gas : 13 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 3) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (branched pre condition tail) := by
  have charged : (pushed 3 pre).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  rw [push_continue (fuel + 1) pre code pc (by omega) (by simp only [stack, List.length_cons]; omega)]
  exact jump_continue fuel pre condition tail code pc stack (by omega) depth

theorem gas_exact (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (gas : 13 ≤ pre.gasAvailable.toNat) :
    (branched pre condition tail).gasAvailable.toNat = pre.gasAvailable.toNat - 13 := by
  have charged : (pushed 3 pre).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have final : (branched pre condition tail).gasAvailable.toNat = (pushed 3 pre).gasAvailable.toNat - 10 :=
    NativeSourceCheckedRejection.gas_sub _ 10 (by decide) (by omega)
  omega

theorem destinations (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 936) :
    (branched pre condition tail).pc = if condition != ⟨0⟩ then UInt256.ofNat 786 else UInt256.ofNat 940 := by
  change (if condition != ⟨0⟩ then UInt256.ofNat 786 else (pre.pc + UInt256.ofNat 3) + UInt256.ofNat 1) = _
  rw [pc]; rfl

end Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorBranch
