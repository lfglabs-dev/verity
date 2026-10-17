import Compiler.Proofs.IRGeneration.NativeSourceArrayLoopSetupOperands

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayLoopSetupChecks
open EvmYul EVM EVM.Proof

theorem dup7 (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 7 ≤ pre.stack.length ∧ pre.stack.length ≤ 1023) :
    Z jumps .DUP7 pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .DUP7 = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 7 by omega, show ¬pre.stack.length - 7 + 8 > 1024 by omega]

theorem swap4 (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 5 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024) :
    Z jumps .SWAP4 pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .SWAP4 = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 5 by omega, show ¬pre.stack.length - 5 + 5 > 1024 by omega]

theorem continue296 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 296)
    (stack : pre.stack = tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 32 :: tail) 2) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLoopSetupDecodes.decode296]; rfl
  have check := NativeSourceGuardChecks.push1 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayLoopSetupOperands.step296 fuel pre  tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue298 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 298)
    (stack : pre.stack = tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 4 :: tail) 2) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 4, 1)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLoopSetupDecodes.decode298]; rfl
  have check := NativeSourceGuardChecks.push1 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayLoopSetupOperands.step298 fuel pre  tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue300 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 300)
    (stack : pre.stack = a :: b :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (b :: a :: b :: tail) 1) := by
  have decoded : decodeAt pre = (.DUP2, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLoopSetupDecodes.decode300]; rfl
  have check := NativeSourceFieldStoreChecks.dup2 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayLoopSetupOperands.step300 fuel pre a b tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue301 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b c d e f g : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 301)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (g :: a :: b :: c :: d :: e :: f :: g :: tail) 1) := by
  have decoded : decodeAt pre = (.DUP7, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLoopSetupDecodes.decode301]; rfl
  have check := dup7 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayLoopSetupOperands.step301 fuel pre a b c d e f g tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue302 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 302)
    (stack : pre.stack = a :: b :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC ((a + b) :: tail) 1) := by
  have decoded : decodeAt pre = (.ADD, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLoopSetupDecodes.decode302]; rfl
  have check := NativeSourceFieldStoreChecks.add jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayLoopSetupOperands.step302 fuel pre a b tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue303 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b c d e : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 303)
    (stack : pre.stack = a :: b :: c :: d :: e :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (e :: b :: c :: d :: a :: tail) 1) := by
  have decoded : decodeAt pre = (.SWAP4, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLoopSetupDecodes.decode303]; rfl
  have check := swap4 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayLoopSetupOperands.step303 fuel pre a b c d e tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

end Compiler.Proofs.IRGeneration.NativeSourceArrayLoopSetupChecks
