import Compiler.Proofs.IRGeneration.NativeSourceGuardChecks
import Compiler.Proofs.IRGeneration.NativeSourceAddressHelper

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedGuard
open EvmYul EVM EVM.Proof NativeSourceAddressGuardExecution

theorem continue1 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (s1 3 pre word ret tail) := by
  have atPC : pre.pc = UInt256.ofNat 946 := by
    exact pc
  have decoded : decodeAt pre = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode946]; rfl
  have check := NativeSourceGuardChecks.swap1 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition1 fuel 3 pre word ret tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue2 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail)
    (gas : 3 ≤ (s1 3 pre word ret tail).gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps (s1 3 pre word ret tail) = EVM.X (fuel + 1) jumps (s2 3 pre word ret tail) := by
  have atPC : (s1 3 pre word ret tail).pc = UInt256.ofNat 947 := by
    simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 3 pre word ret tail) = ((.Push .PUSH1), some (UInt256.ofNat 1, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 3 pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode947]; rfl
  have check := NativeSourceGuardChecks.push1 jumps (s1 3 pre word ret tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition2 fuel 3 pre word ret tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue3 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail)
    (gas : 3 ≤ (s2 3 pre word ret tail).gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps (s2 3 pre word ret tail) = EVM.X (fuel + 1) jumps (s3 3 pre word ret tail) := by
  have atPC : (s2 3 pre word ret tail).pc = UInt256.ofNat 949 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 3 pre word ret tail) = ((.Push .PUSH1), some (UInt256.ofNat 1, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 3 pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode949]; rfl
  have check := NativeSourceGuardChecks.push1 jumps (s2 3 pre word ret tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition3 fuel 3 pre word ret tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue4 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail)
    (gas : 3 ≤ (s3 3 pre word ret tail).gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps (s3 3 pre word ret tail) = EVM.X (fuel + 1) jumps (s4 3 pre word ret tail) := by
  have atPC : (s3 3 pre word ret tail).pc = UInt256.ofNat 951 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 3 pre word ret tail) = ((.Push .PUSH1), some (UInt256.ofNat 160, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 3 pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode951]; rfl
  have check := NativeSourceGuardChecks.push1 jumps (s3 3 pre word ret tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition4 fuel 3 pre word ret tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue5 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail)
    (gas : 3 ≤ (s4 3 pre word ret tail).gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps (s4 3 pre word ret tail) = EVM.X (fuel + 1) jumps (s5 3 pre word ret tail) := by
  have atPC : (s4 3 pre word ret tail).pc = UInt256.ofNat 953 := by
    simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s4 3 pre word ret tail) = (.SHL, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 3 pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode953]; rfl
  have check := NativeSourceGuardChecks.shl jumps (s4 3 pre word ret tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition5 fuel 3 pre word ret tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue6 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail)
    (gas : 3 ≤ (s5 3 pre word ret tail).gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps (s5 3 pre word ret tail) = EVM.X (fuel + 1) jumps (s6 3 pre word ret tail) := by
  have atPC : (s5 3 pre word ret tail).pc = UInt256.ofNat 954 := by
    simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s5 3 pre word ret tail) = (.SUB, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 3 pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode954]; rfl
  have check := NativeSourceGuardChecks.sub jumps (s5 3 pre word ret tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition6 fuel 3 pre word ret tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue7 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail)
    (gas : 3 ≤ (s6 3 pre word ret tail).gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps (s6 3 pre word ret tail) = EVM.X (fuel + 1) jumps (s7 3 pre word ret tail) := by
  have atPC : (s6 3 pre word ret tail).pc = UInt256.ofNat 955 := by
    simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s6 3 pre word ret tail) = (.DUP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 3 pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode955]; rfl
  have check := NativeSourceGuardChecks.dup3 jumps (s6 3 pre word ret tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition7 fuel 3 pre word ret tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue8 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail)
    (gas : 3 ≤ (s7 3 pre word ret tail).gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps (s7 3 pre word ret tail) = EVM.X (fuel + 1) jumps (s8 3 pre word ret tail) := by
  have atPC : (s7 3 pre word ret tail).pc = UInt256.ofNat 956 := by
    simp only [s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s7 3 pre word ret tail) = (.AND, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s7 3 pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode956]; rfl
  have check := NativeSourceGuardChecks.land jumps (s7 3 pre word ret tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition8 fuel 3 pre word ret tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue9 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail)
    (gas : 3 ≤ (s8 3 pre word ret tail).gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps (s8 3 pre word ret tail) = EVM.X (fuel + 1) jumps (s9 3 pre word ret tail) := by
  have atPC : (s8 3 pre word ret tail).pc = UInt256.ofNat 957 := by
    simp only [s8, s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s8 3 pre word ret tail) = (.DUP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s8 3 pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode957]; rfl
  have check := NativeSourceGuardChecks.dup3 jumps (s8 3 pre word ret tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s8, s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition9 fuel 3 pre word ret tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue10 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail)
    (gas : 3 ≤ (s9 3 pre word ret tail).gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps (s9 3 pre word ret tail) = EVM.X (fuel + 1) jumps (s10 3 pre word ret tail) := by
  have atPC : (s9 3 pre word ret tail).pc = UInt256.ofNat 958 := by
    simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s9 3 pre word ret tail) = (.SUB, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s9 3 pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode958]; rfl
  have check := NativeSourceGuardChecks.sub jumps (s9 3 pre word ret tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition10 fuel 3 pre word ret tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem gas_chain (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (gas : 30 ≤ pre.gasAvailable.toNat) :
    (s1 3 pre word ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 ∧
      (s2 3 pre word ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 6 ∧
      (s3 3 pre word ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 ∧
      (s4 3 pre word ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 12 ∧
      (s5 3 pre word ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 15 ∧
      (s6 3 pre word ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 18 ∧
      (s7 3 pre word ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 21 ∧
      (s8 3 pre word ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 24 ∧
      (s9 3 pre word ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 27 ∧
      (s10 3 pre word ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 30 := by
  have g1 : (s1 3 pre word ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (s2 3 pre word ret tail).gasAvailable.toNat = (s1 3 pre word ret tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 3 pre word ret tail).gasAvailable.toNat = (s2 3 pre word ret tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 3 pre word ret tail).gasAvailable.toNat = (s3 3 pre word ret tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g5 : (s5 3 pre word ret tail).gasAvailable.toNat = (s4 3 pre word ret tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g6 : (s6 3 pre word ret tail).gasAvailable.toNat = (s5 3 pre word ret tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g7 : (s7 3 pre word ret tail).gasAvailable.toNat = (s6 3 pre word ret tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g8 : (s8 3 pre word ret tail).gasAvailable.toNat = (s7 3 pre word ret tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g9 : (s9 3 pre word ret tail).gasAvailable.toNat = (s8 3 pre word ret tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g10 : (s10 3 pre word ret tail).gasAvailable.toNat = (s9 3 pre word ret tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) (gas : 30 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 11) jumps pre = EVM.X (fuel + 1) jumps (s10 3 pre word ret tail) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := gas_chain pre word ret tail gas
  rw [continue1 (fuel + 9) jumps pre word ret tail code pc stack (by omega) depth]
  rw [continue2 (fuel + 8) jumps pre word ret tail code pc stack (by omega) depth]
  rw [continue3 (fuel + 7) jumps pre word ret tail code pc stack (by omega) depth]
  rw [continue4 (fuel + 6) jumps pre word ret tail code pc stack (by omega) depth]
  rw [continue5 (fuel + 5) jumps pre word ret tail code pc stack (by omega) depth]
  rw [continue6 (fuel + 4) jumps pre word ret tail code pc stack (by omega) depth]
  rw [continue7 (fuel + 3) jumps pre word ret tail code pc stack (by omega) depth]
  rw [continue8 (fuel + 2) jumps pre word ret tail code pc stack (by omega) depth]
  rw [continue9 (fuel + 1) jumps pre word ret tail code pc stack (by omega) depth]
  rw [continue10 (fuel + 0) jumps pre word ret tail code pc stack (by omega) depth]

theorem reject_exact (fuel : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) (invalid : ¬word.toNat < 2 ^ 160)
    (gas : 49 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 17) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      .ok (.revert (UInt256.ofNat (pre.gasAvailable.toNat - 49)) ByteArray.empty) := by
  have charged := (gas_chain pre word ret tail (by omega)).2.2.2.2.2.2.2.2.2
  have nonzero : word - word.land NativeSourceAddressCanonicality.mask ≠ UInt256.ofNat 0 :=
    fun zero => invalid ((NativeSourceAddressCanonicality.difference_zero_iff word).mp zero)
  have codeAfter : (s10 3 pre word ret tail).executionEnv.code = NativeSourceAbiWrite.code :=
    (NativeSourceAddressHelper.guard_code 3 pre word ret tail).trans code
  rw [execute (fuel + 6) _ pre word ret tail code pc stack (by omega) depth]
  rw [NativeSourceCheckedPushRejection.execute_exact fuel _ _ (ret :: word :: tail) codeAfter
    (NativeSourceAddressHelper.guard_pc 3 pre word ret tail pc) (output_stack 3 pre word ret tail)
    nonzero (by omega) (by simp only [List.length_cons]; omega), charged]
  congr 3

end Compiler.Proofs.IRGeneration.NativeSourceCheckedGuard
