import Compiler.Proofs.IRGeneration.NativeSourceFieldStoreChecks

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedFieldPrefix
open EvmYul EVM EVM.Proof NativeSourceMidnightFieldStore

theorem continue1 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail)
    (gas : 1 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (s1 pre) := by
  have atPC : pre.pc = UInt256.ofNat 191 := by
    exact pc
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode191]; rfl
  have check := Z_JUMPDEST jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word, GasConstants.Gjumpdest] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition1 fuel 3 pre word a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step (H_JUMPDEST _)

theorem continue2 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail)
    (gas : 3 ≤ (s1 pre).gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 2) jumps (s1 pre) = EVM.X (fuel + 1) jumps (s2 pre word a base tail) := by
  have atPC : (s1 pre).pc = UInt256.ofNat 192 := by
    simp only [s1, stepPre, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 pre) = ((.Push .PUSH1), some (UInt256.ofNat 32, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre).pc).getD _ = _
    rw [code, atPC, decode192]; rfl
  have check := NativeSourceGuardChecks.push1 jumps (s1 pre)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s1, stepPre, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition2 fuel 3 pre word a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue3 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail)
    (gas : 3 ≤ (s2 pre word a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 2) jumps (s2 pre word a base tail) = EVM.X (fuel + 1) jumps (s3 pre word a base tail) := by
  have atPC : (s2 pre word a base tail).pc = UInt256.ofNat 194 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 pre word a base tail) = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre word a base tail).pc).getD _ = _
    rw [code, atPC, decode194]; rfl
  have check := NativeSourceFieldStoreChecks.dup4 jumps (s2 pre word a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition3 fuel 3 pre word a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue4 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail)
    (gas : 3 ≤ (s3 pre word a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 2) jumps (s3 pre word a base tail) = EVM.X (fuel + 1) jumps (s4 pre word a base tail) := by
  have atPC : (s3 pre word a base tail).pc = UInt256.ofNat 195 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 pre word a base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 pre word a base tail).pc).getD _ = _
    rw [code, atPC, decode195]; rfl
  have check := NativeSourceFieldStoreChecks.add jumps (s3 pre word a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition4 fuel 3 pre word a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue5 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail)
    (gas : 3 ≤ (s4 pre word a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 2) jumps (s4 pre word a base tail) = EVM.X (fuel + 1) jumps (s5 pre word a base tail) := by
  have atPC : (s4 pre word a base tail).pc = UInt256.ofNat 196 := by
    simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s4 pre word a base tail) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 pre word a base tail).pc).getD _ = _
    rw [code, atPC, decode196]; rfl
  have check := NativeSourceGuardChecks.swap1 jumps (s4 pre word a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition5 fuel 3 pre word a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue6 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail)
    (gas : 3 ≤ (s5 pre word a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 2) jumps (s5 pre word a base tail) = EVM.X (fuel + 1) jumps (s6 pre word a base tail) := by
  have atPC : (s5 pre word a base tail).pc = UInt256.ofNat 197 := by
    simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s5 pre word a base tail) = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 pre word a base tail).pc).getD _ = _
    rw [code, atPC, decode197]; rfl
  have check := NativeSourceFieldStoreChecks.dup2 jumps (s5 pre word a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition6 fuel 3 pre word a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem gas_chain (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256)
    (gas : 16 ≤ pre.gasAvailable.toNat) :
    (s1 pre).gasAvailable.toNat = pre.gasAvailable.toNat - 1 ∧
      (s2 pre word a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 4 ∧
      (s3 pre word a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 7 ∧
      (s4 pre word a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 10 ∧
      (s5 pre word a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 13 ∧
      (s6 pre word a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 16 := by
  have g1 : (s1 pre).gasAvailable.toNat = pre.gasAvailable.toNat - 1 :=
    NativeSourceCheckedRejection.gas_sub _ 1 (by decide) (by omega)
  have g2 : (s2 pre word a base tail).gasAvailable.toNat = (s1 pre).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre word a base tail).gasAvailable.toNat = (s2 pre word a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre word a base tail).gasAvailable.toNat = (s3 pre word a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g5 : (s5 pre word a base tail).gasAvailable.toNat = (s4 pre word a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g6 : (s6 pre word a base tail).gasAvailable.toNat = (s5 pre word a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail)
    (gas : 16 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 7) jumps pre = EVM.X (fuel + 1) jumps (s6 pre word a base tail) := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := gas_chain pre word a base tail gas
  rw [continue1 (fuel + 5) jumps pre word a base tail code pc stack (by omega) depth]
  rw [continue2 (fuel + 4) jumps pre word a base tail code pc stack (by omega) depth]
  rw [continue3 (fuel + 3) jumps pre word a base tail code pc stack (by omega) depth]
  rw [continue4 (fuel + 2) jumps pre word a base tail code pc stack (by omega) depth]
  rw [continue5 (fuel + 1) jumps pre word a base tail code pc stack (by omega) depth]
  rw [continue6 (fuel + 0) jumps pre word a base tail code pc stack (by omega) depth]

theorem execute_store (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail)
    (gas : 19 + memoryExpansionCost (s6 pre word a base tail) .MSTORE ≤ pre.gasAvailable.toNat)
    (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 8) jumps pre = EVM.X (fuel + 1) jumps
      (mstorePost 3 (NativeSourceFieldStoreChecks.expanded (s6 pre word a base tail))
        ((base + UInt256.ofNat 32) :: a :: base :: tail) (base + UInt256.ofNat 32) word) := by
  have charged := (gas_chain pre word a base tail (by omega)).2.2.2.2.2
  have atPC : (s6 pre word a base tail).pc = UInt256.ofNat 198 := by
    simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  rw [execute (fuel + 1) jumps pre word a base tail code pc stack (by omega) depth]
  exact NativeSourceFieldStoreChecks.store_continue fuel jumps _ _ _ _ code atPC rfl
    (by omega) (by simp only [List.length_cons]; omega)

end Compiler.Proofs.IRGeneration.NativeSourceCheckedFieldPrefix


