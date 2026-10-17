import Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorStart

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorRounding
open EvmYul EVM EVM.Proof NativeSourceAllocatorRounding

theorem not_check (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 1 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024) :
    Z jumps .NOT pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .NOT = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 1 by omega, show ¬pre.stack.length - 1 + 1 > 1024 by omega]

theorem continue1 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 914)
    (stack : pre.stack = word :: size :: base :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (s1 3 pre word size base tail) := by
  have atPC : pre.pc = UInt256.ofNat 914 := by
    exact pc
  have decoded : decodeAt pre = (.DUP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode914]
    rfl
  have check := NativeSourceRejectionChecks.dup1 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition1 fuel 3 pre word size base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue2 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 914)
    (stack : pre.stack = word :: size :: base :: tail)
    (gas : 3 ≤ (s1 3 pre word size base tail).gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 2) jumps (s1 3 pre word size base tail) = EVM.X (fuel + 1) jumps (s2 3 pre word size base tail) := by
  have atPC : (s1 3 pre word size base tail).pc = UInt256.ofNat 915 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 3 pre word size base tail) = (.NOT, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 3 pre word size base tail).pc).getD _ = _
    rw [code, atPC, decode915]
    rfl
  have check := not_check jumps (s1 3 pre word size base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition2 fuel 3 pre word size base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue3 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 914)
    (stack : pre.stack = word :: size :: base :: tail)
    (gas : 3 ≤ (s2 3 pre word size base tail).gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 2) jumps (s2 3 pre word size base tail) = EVM.X (fuel + 1) jumps (s3 3 pre word size base tail) := by
  have atPC : (s2 3 pre word size base tail).pc = UInt256.ofNat 916 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 3 pre word size base tail) = (.SWAP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 3 pre word size base tail).pc).getD _ = _
    rw [code, atPC, decode916]
    rfl
  have check := NativeSourceLoanFieldStore.swap2_check jumps (s2 3 pre word size base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition3 fuel 3 pre word size base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue4 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 914)
    (stack : pre.stack = word :: size :: base :: tail)
    (gas : 3 ≤ (s3 3 pre word size base tail).gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 2) jumps (s3 3 pre word size base tail) = EVM.X (fuel + 1) jumps (s4 3 pre word size base tail) := by
  have atPC : (s3 3 pre word size base tail).pc = UInt256.ofNat 917 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 3 pre word size base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 3 pre word size base tail).pc).getD _ = _
    rw [code, atPC, decode917]
    rfl
  have check := NativeSourceFieldStoreChecks.add jumps (s3 3 pre word size base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition4 fuel 3 pre word size base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue5 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 914)
    (stack : pre.stack = word :: size :: base :: tail)
    (gas : 3 ≤ (s4 3 pre word size base tail).gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 2) jumps (s4 3 pre word size base tail) = EVM.X (fuel + 1) jumps (s5 3 pre word size base tail) := by
  have atPC : (s4 3 pre word size base tail).pc = UInt256.ofNat 918 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 3 pre word size base tail) = (.AND, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 3 pre word size base tail).pc).getD _ = _
    rw [code, atPC, decode918]
    rfl
  have check := NativeSourceGuardChecks.land jumps (s4 3 pre word size base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition5 fuel 3 pre word size base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem gas_chain (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256)
    (gas : 15 ≤ pre.gasAvailable.toNat) :
    (s1 3 pre word size base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 ∧
      (s2 3 pre word size base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 6 ∧
      (s3 3 pre word size base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 ∧
      (s4 3 pre word size base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 12 ∧
      (s5 3 pre word size base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 15 := by
  have g1 : (s1 3 pre word size base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (s2 3 pre word size base tail).gasAvailable.toNat = (s1 3 pre word size base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 3 pre word size base tail).gasAvailable.toNat = (s2 3 pre word size base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 3 pre word size base tail).gasAvailable.toNat = (s3 3 pre word size base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g5 : (s5 3 pre word size base tail).gasAvailable.toNat = (s4 3 pre word size base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 914)
    (stack : pre.stack = word :: size :: base :: tail)
    (gas : 15 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 6) jumps pre = EVM.X (fuel + 1) jumps (s5 3 pre word size base tail) := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := gas_chain pre word size base tail gas
  rw [continue1 (fuel + 4) jumps pre word size base tail code pc stack (by omega) depth]
  rw [continue2 (fuel + 3) jumps pre word size base tail code pc stack (by omega) depth]
  rw [continue3 (fuel + 2) jumps pre word size base tail code pc stack (by omega) depth]
  rw [continue4 (fuel + 1) jumps pre word size base tail code pc stack (by omega) depth]
  rw [continue5 (fuel + 0) jumps pre word size base tail code pc stack (by omega) depth]

end Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorRounding
