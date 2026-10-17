import Compiler.Proofs.IRGeneration.NativeSourceArrayCallOperands

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayOperandChecks
open EvmYul EVM EVM.Proof

theorem swap3 (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 4 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024) :
    Z jumps .SWAP3 pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .SWAP3 = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 4 by omega, show ¬pre.stack.length - 4 + 4 > 1024 by omega]

theorem dup6 (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 6 ≤ pre.stack.length ∧ pre.stack.length ≤ 1023) :
    Z jumps .DUP6 pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .DUP6 = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 6 by omega, show ¬pre.stack.length - 6 + 7 > 1024 by omega]

theorem continue277 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 277)
    (stack : pre.stack = tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 292 :: tail) 3) := by
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 292, 2)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode277]; rfl
  have check := NativeSourceCheckedPushRejection.push2_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayCallOperands.step277 fuel pre tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue280 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 280)
    (stack : pre.stack = tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 32 :: tail) 2) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode280]; rfl
  have check := NativeSourceGuardChecks.push1 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayCallOperands.step280 fuel pre tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue282 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b c d : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 282)
    (stack : pre.stack = a :: b :: c :: d :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (d :: a :: b :: c :: d :: tail) 1) := by
  have decoded : decodeAt pre = (.DUP4, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode282]; rfl
  have check := NativeSourceFieldStoreChecks.dup4 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayCallOperands.step282 fuel pre a b c d tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue283 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 283)
    (stack : pre.stack = tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 5 :: tail) 2) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 5, 1)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode283]; rfl
  have check := NativeSourceGuardChecks.push1 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayCallOperands.step283 fuel pre tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue285 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 285)
    (stack : pre.stack = a :: b :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC ((b <<< a) :: tail) 1) := by
  have decoded : decodeAt pre = (.SHL, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode285]; rfl
  have check := NativeSourceGuardChecks.shl jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayCallOperands.step285 fuel pre a b tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue286 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 286)
    (stack : pre.stack = a :: b :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC ((a + b) :: tail) 1) := by
  have decoded : decodeAt pre = (.ADD, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode286]; rfl
  have check := NativeSourceFieldStoreChecks.add jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayCallOperands.step286 fuel pre a b tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue287 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 287)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1017) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (f :: a :: b :: c :: d :: e :: f :: tail) 1) := by
  have decoded : decodeAt pre = (.DUP6, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode287]; rfl
  have check := dup6 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayCallOperands.step287 fuel pre a b c d e f tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue288 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 288)
    (stack : pre.stack = tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 910 :: tail) 3) := by
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 910, 2)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode288]; rfl
  have check := NativeSourceCheckedPushRejection.push2_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayCallOperands.step288 fuel pre tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

end Compiler.Proofs.IRGeneration.NativeSourceArrayOperandChecks
