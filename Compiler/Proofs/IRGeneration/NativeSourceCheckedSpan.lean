import Compiler.Proofs.IRGeneration.NativeSourceSpanChecks

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedSpan
open EvmYul EVM EVM.Proof NativeSourceCollateralSpan

theorem continue1 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (s1 pre offset x y a base tail) := by
  have atPC : pre.pc = UInt256.ofNat 239 := by
    exact pc
  have decoded : decodeAt pre = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode239]; rfl
  have check := NativeSourceFieldStoreChecks.dup4 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition1 fuel pre offset x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue2 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail)
    (gas : 3 ≤ (s1 pre offset x y a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s1 pre offset x y a base tail) = EVM.X (fuel + 1) jumps (s2 pre offset x y a base tail) := by
  have atPC : (s1 pre offset x y a base tail).pc = UInt256.ofNat 240 := by
    simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 pre offset x y a base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode240]; rfl
  have check := NativeSourceFieldStoreChecks.add jumps (s1 pre offset x y a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition2 fuel pre offset x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue3 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail)
    (gas : 3 ≤ (s2 pre offset x y a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s2 pre offset x y a base tail) = EVM.X (fuel + 1) jumps (s3 pre offset x y a base tail) := by
  have atPC : (s2 pre offset x y a base tail).pc = UInt256.ofNat 241 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 pre offset x y a base tail) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode241]; rfl
  have check := NativeSourceGuardChecks.swap1 jumps (s2 pre offset x y a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition3 fuel pre offset x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue4 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail)
    (gas : 2 ≤ (s3 pre offset x y a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s3 pre offset x y a base tail) = EVM.X (fuel + 1) jumps (s4 pre offset x y a base tail) := by
  have atPC : (s3 pre offset x y a base tail).pc = UInt256.ofNat 242 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 pre offset x y a base tail) = (.CALLDATASIZE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode242]; rfl
  have check := NativeSourceSpanChecks.calldatasize jumps (s3 pre offset x y a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition4 fuel pre offset x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue5 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail)
    (gas : 3 ≤ (s4 pre offset x y a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s4 pre offset x y a base tail) = EVM.X (fuel + 1) jumps (s5 pre offset x y a base tail) := by
  have atPC : (s4 pre offset x y a base tail).pc = UInt256.ofNat 243 := by
    simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s4 pre offset x y a base tail) = (.Push .PUSH1, some (UInt256.ofNat 35, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode243]; rfl
  have check := NativeSourceGuardChecks.push1 jumps (s4 pre offset x y a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition5 fuel pre offset x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue6 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail)
    (gas : 3 ≤ (s5 pre offset x y a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s5 pre offset x y a base tail) = EVM.X (fuel + 1) jumps (s6 pre offset x y a base tail) := by
  have atPC : (s5 pre offset x y a base tail).pc = UInt256.ofNat 245 := by
    simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s5 pre offset x y a base tail) = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode245]; rfl
  have check := NativeSourceFieldStoreChecks.dup4 jumps (s5 pre offset x y a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition6 fuel pre offset x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue7 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail)
    (gas : 3 ≤ (s6 pre offset x y a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s6 pre offset x y a base tail) = EVM.X (fuel + 1) jumps (s7 pre offset x y a base tail) := by
  have atPC : (s6 pre offset x y a base tail).pc = UInt256.ofNat 246 := by
    simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s6 pre offset x y a base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode246]; rfl
  have check := NativeSourceFieldStoreChecks.add jumps (s6 pre offset x y a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition7 fuel pre offset x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue8 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail)
    (gas : 3 ≤ (s7 pre offset x y a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s7 pre offset x y a base tail) = EVM.X (fuel + 1) jumps (s8 pre offset x y a base tail) := by
  have atPC : (s7 pre offset x y a base tail).pc = UInt256.ofNat 247 := by
    simp only [s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s7 pre offset x y a base tail) = (.SLT, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s7 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode247]; rfl
  have check := NativeSourceSpanChecks.slt jumps (s7 pre offset x y a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition8 fuel pre offset x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue9 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail)
    (gas : 3 ≤ (s8 pre offset x y a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s8 pre offset x y a base tail) = EVM.X (fuel + 1) jumps (s9 pre offset x y a base tail) := by
  have atPC : (s8 pre offset x y a base tail).pc = UInt256.ofNat 248 := by
    simp only [s8, s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s8 pre offset x y a base tail) = (.ISZERO, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s8 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode248]; rfl
  have check := NativeSourceSpanChecks.iszero jumps (s8 pre offset x y a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s8, s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition9 fuel pre offset x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue10 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail)
    (gas : 3 ≤ (s9 pre offset x y a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s9 pre offset x y a base tail) = EVM.X (fuel + 1) jumps (s10 pre offset x y a base tail) := by
  have atPC : (s9 pre offset x y a base tail).pc = UInt256.ofNat 249 := by
    simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s9 pre offset x y a base tail) = (.Push .PUSH2, some (UInt256.ofNat 91, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s9 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode249]; rfl
  have check := NativeSourceCheckedPushRejection.push2_check jumps (s9 pre offset x y a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition10 fuel pre offset x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem gas_chain (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (gas : 29 ≤ pre.gasAvailable.toNat) :
    (s1 pre offset x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 ∧
      (s2 pre offset x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 6 ∧
      (s3 pre offset x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 ∧
      (s4 pre offset x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 11 ∧
      (s5 pre offset x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 14 ∧
      (s6 pre offset x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 17 ∧
      (s7 pre offset x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 20 ∧
      (s8 pre offset x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 23 ∧
      (s9 pre offset x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 26 ∧
      (s10 pre offset x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 29 := by
  have g1 : (s1 pre offset x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (s2 pre offset x y a base tail).gasAvailable.toNat = (s1 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre offset x y a base tail).gasAvailable.toNat = (s2 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre offset x y a base tail).gasAvailable.toNat = (s3 pre offset x y a base tail).gasAvailable.toNat - 2 :=
    NativeSourceCheckedRejection.gas_sub _ 2 (by decide) (by omega)
  have g5 : (s5 pre offset x y a base tail).gasAvailable.toNat = (s4 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g6 : (s6 pre offset x y a base tail).gasAvailable.toNat = (s5 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g7 : (s7 pre offset x y a base tail).gasAvailable.toNat = (s6 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g8 : (s8 pre offset x y a base tail).gasAvailable.toNat = (s7 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g9 : (s9 pre offset x y a base tail).gasAvailable.toNat = (s8 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g10 : (s10 pre offset x y a base tail).gasAvailable.toNat = (s9 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute_prefix (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail)
    (gas : 29 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 11) jumps pre = EVM.X (fuel + 1) jumps (s10 pre offset x y a base tail) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := gas_chain pre offset x y a base tail gas
  rw [continue1 (fuel + 9) jumps pre offset x y a base tail code pc stack (by omega) depth]
  rw [continue2 (fuel + 8) jumps pre offset x y a base tail code pc stack (by omega) depth]
  rw [continue3 (fuel + 7) jumps pre offset x y a base tail code pc stack (by omega) depth]
  rw [continue4 (fuel + 6) jumps pre offset x y a base tail code pc stack (by omega) depth]
  rw [continue5 (fuel + 5) jumps pre offset x y a base tail code pc stack (by omega) depth]
  rw [continue6 (fuel + 4) jumps pre offset x y a base tail code pc stack (by omega) depth]
  rw [continue7 (fuel + 3) jumps pre offset x y a base tail code pc stack (by omega) depth]
  rw [continue8 (fuel + 2) jumps pre offset x y a base tail code pc stack (by omega) depth]
  rw [continue9 (fuel + 1) jumps pre offset x y a base tail code pc stack (by omega) depth]
  rw [continue10 (fuel + 0) jumps pre offset x y a base tail code pc stack (by omega) depth]

end Compiler.Proofs.IRGeneration.NativeSourceCheckedSpan
