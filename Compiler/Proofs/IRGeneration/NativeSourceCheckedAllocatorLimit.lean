import Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorPointer

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorLimit
open EvmYul EVM EVM.Proof NativeSourceAllocatorLimit

theorem or_check (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 2 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024) :
    Z jumps .OR pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .OR = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 2 by omega, show ¬pre.stack.length - 2 + 1 > 1024 by omega]

theorem push_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 924)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : pre.stack.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (pushed 3 pre) := by
  have decoded : decodeAt pre = (.Push .PUSH8, some (UInt256.ofNat (2^64-1), 8)) := by
    unfold decodeAt; rw [code, pc, decode924]; rfl
  have check := NativeSourceCheckedOffsetGuard.push8_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) ⟨by omega, depth⟩
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := push fuel 3 pre code pc
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue1 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (limit overflow pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 933)
    (stack : pre.stack = limit :: overflow :: pointer :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (s1 3 pre limit overflow pointer tail) := by
  have atPC : pre.pc = UInt256.ofNat 933 := by
    exact pc
  have decoded : decodeAt pre = (.DUP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode933]
    rfl
  have check := NativeSourceGuardChecks.dup3 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition1 fuel 3 pre limit overflow pointer tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue2 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (limit overflow pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 933)
    (stack : pre.stack = limit :: overflow :: pointer :: tail)
    (gas : 3 ≤ (s1 3 pre limit overflow pointer tail).gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 2) jumps (s1 3 pre limit overflow pointer tail) = EVM.X (fuel + 1) jumps (s2 3 pre limit overflow pointer tail) := by
  have atPC : (s1 3 pre limit overflow pointer tail).pc = UInt256.ofNat 934 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 3 pre limit overflow pointer tail) = (.GT, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 3 pre limit overflow pointer tail).pc).getD _ = _
    rw [code, atPC, decode934]
    rfl
  have check := NativeSourceCheckedOffsetGuard.gt_check jumps (s1 3 pre limit overflow pointer tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition2 fuel 3 pre limit overflow pointer tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue3 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (limit overflow pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 933)
    (stack : pre.stack = limit :: overflow :: pointer :: tail)
    (gas : 3 ≤ (s2 3 pre limit overflow pointer tail).gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 2) jumps (s2 3 pre limit overflow pointer tail) = EVM.X (fuel + 1) jumps (s3 3 pre limit overflow pointer tail) := by
  have atPC : (s2 3 pre limit overflow pointer tail).pc = UInt256.ofNat 935 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 3 pre limit overflow pointer tail) = (.OR, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 3 pre limit overflow pointer tail).pc).getD _ = _
    rw [code, atPC, decode935]
    rfl
  have check := or_check jumps (s2 3 pre limit overflow pointer tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition3 fuel 3 pre limit overflow pointer tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

end Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorLimit
