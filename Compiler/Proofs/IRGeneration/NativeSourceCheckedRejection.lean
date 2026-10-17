import Compiler.Proofs.IRGeneration.NativeSourceRejectionChecks

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedRejection
open EvmYul EVM EVM.Proof

theorem sub_zero_word (word : UInt256) : word - UInt256.ofNat 0 = word := by
  cases word with
  | mk value => change UInt256.mk (value - 0) = UInt256.mk value; rw [sub_zero]

theorem zero_gas_state (pre : EVM.State) :
    { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 } = pre := by
  rw [sub_zero_word]

def first (pre : EVM.State) := (stepPre 1 pre).incrPC
def second (pre : EVM.State) := (stepPre 2 (first pre)).replaceStackAndIncrPC (UInt256.ofNat 0 :: pre.stack)
def third (pre : EVM.State) := (stepPre 3 (second pre)).replaceStackAndIncrPC (UInt256.ofNat 0 :: UInt256.ofNat 0 :: pre.stack)

theorem jumpdest_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 91)
    (gas : 1 ≤ pre.gasAvailable.toNat) (stack : pre.stack.length ≤ 1024) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (first pre) := by
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceEmptyRevert.decode91]; rfl
  have check := Z_JUMPDEST jumps pre (by simpa only [sub_zero_word, GasConstants.Gjumpdest] using gas) stack
  rw [zero_gas_state] at check
  exact X_succ_of_continue decoded check (step_JUMPDEST fuel 1 pre) (H_JUMPDEST _)

theorem push_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 91)
    (gas : 2 ≤ (first pre).gasAvailable.toNat) (stack : pre.stack.length < 1024) :
    EVM.X (fuel + 2) jumps (first pre) = EVM.X (fuel + 1) jumps (second pre) := by
  have atPC : (first pre).pc = UInt256.ofNat 92 := by change pre.pc + UInt256.ofNat 1 = _; rw [pc]; decide
  have decoded : decodeAt (first pre) = (.Push .PUSH0, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (first pre).pc).getD _ = _
    rw [code, atPC, NativeSourceEmptyRevert.decode92]; rfl
  have check := NativeSourceRejectionChecks.push0 jumps (first pre) (by simpa only [sub_zero_word] using gas) stack
  rw [zero_gas_state] at check
  have step : StepOk (fuel + 1) 2 (.Push .PUSH0, none) (first pre) (second pre) := by rfl
  exact X_succ_of_continue decoded check step rfl

theorem dup_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 91)
    (gas : 3 ≤ (second pre).gasAvailable.toNat) (stack : pre.stack.length ≤ 1022) :
    EVM.X (fuel + 2) jumps (second pre) = EVM.X (fuel + 1) jumps (third pre) := by
  have atPC : (second pre).pc = UInt256.ofNat 93 := by
    change (pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1 = _; rw [pc]; decide
  have decoded : decodeAt (second pre) = (.DUP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (second pre).pc).getD _ = _
    rw [code, atPC, NativeSourceEmptyRevert.decode93]; rfl
  have depth : 0 < (second pre).stack.length ∧ (second pre).stack.length < 1024 := by
    change 0 < (UInt256.ofNat 0 :: pre.stack).length ∧ (UInt256.ofNat 0 :: pre.stack).length < 1024
    simp only [List.length_cons]; omega
  have check := NativeSourceRejectionChecks.dup1 jumps (second pre) (by simpa only [sub_zero_word] using gas) depth
  rw [zero_gas_state] at check
  have step : StepOk (fuel + 1) 3 (.DUP1, none) (second pre) (third pre) := by rfl
  exact X_succ_of_continue decoded check step rfl

theorem final_revert (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 91)
    (stack : pre.stack.length ≤ 1022) :
    EVM.X (fuel + 2) jumps (third pre) =
      .ok (.revert (third pre).gasAvailable ByteArray.empty) := by
  have atPC : (third pre).pc = UInt256.ofNat 94 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _; rw [pc]; decide
  have shape : (third pre).stack = UInt256.ofNat 0 :: UInt256.ofNat 0 :: pre.stack := by rfl
  have check := NativeSourceRejectionChecks.zero_revert jumps (third pre) pre.stack shape stack
  rw [zero_gas_state] at check
  have actual := NativeSourceEmptyRevert.checked_revert fuel 0 jumps (third pre) (third pre) pre.stack code atPC shape check
  have sameGas : (NativeSourceEmptyRevert.reverted 0 (third pre) pre.stack).gasAvailable = (third pre).gasAvailable := by
    change (third pre).gasAvailable - UInt256.ofNat 0 = _; exact sub_zero_word _
  rw [sameGas] at actual
  exact actual

theorem gas_sub (word : UInt256) (cost : Nat) (bounded : cost < 2 ^ 256) (enough : cost ≤ word.toNat) :
    (word - UInt256.ofNat cost).toNat = word.toNat - cost := by
  have natural : (UInt256.ofNat cost).toNat = cost := Nat.mod_eq_of_lt bounded
  have ordered : (UInt256.ofNat cost).val ≤ word.val := by change (UInt256.ofNat cost).toNat ≤ word.toNat; rw [natural]; exact enough
  rw [show (word - UInt256.ofNat cost).toNat = word.toNat - (UInt256.ofNat cost).toNat from Fin.sub_val_of_le ordered, natural]

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 91)
    (gas : 6 ≤ pre.gasAvailable.toNat) (stack : pre.stack.length ≤ 1022) :
    EVM.X (fuel + 5) jumps pre = .ok (.revert (third pre).gasAvailable ByteArray.empty) := by
  have g1 : (first pre).gasAvailable.toNat = pre.gasAvailable.toNat - 1 := gas_sub _ 1 (by decide) (by omega)
  have g2 : (second pre).gasAvailable.toNat = (first pre).gasAvailable.toNat - 2 := gas_sub _ 2 (by decide) (by omega)
  rw [jumpdest_continue (fuel + 3) jumps pre code pc (by omega) (by omega),
    push_continue (fuel + 2) jumps pre code pc (by omega) (by omega),
    dup_continue (fuel + 1) jumps pre code pc (by omega) stack]
  exact final_revert fuel jumps pre code pc stack

theorem remaining_gas (pre : EVM.State) (gas : 6 ≤ pre.gasAvailable.toNat) :
    (third pre).gasAvailable.toNat = pre.gasAvailable.toNat - 6 := by
  have g1 : (first pre).gasAvailable.toNat = pre.gasAvailable.toNat - 1 := gas_sub _ 1 (by decide) (by omega)
  have g2 : (second pre).gasAvailable.toNat = (first pre).gasAvailable.toNat - 2 := gas_sub _ 2 (by decide) (by omega)
  have g3 : (third pre).gasAvailable.toNat = (second pre).gasAvailable.toNat - 3 := gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute_exact (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 91)
    (gas : 6 ≤ pre.gasAvailable.toNat) (stack : pre.stack.length ≤ 1022) :
    EVM.X (fuel + 5) jumps pre =
      .ok (.revert (UInt256.ofNat (pre.gasAvailable.toNat - 6)) ByteArray.empty) := by
  have word : (third pre).gasAvailable = UInt256.ofNat (pre.gasAvailable.toNat - 6) := by
    rw [← remaining_gas pre gas]
    exact (NativeSourceRejectionChecks.word_roundtrip _).symm
  rw [execute fuel jumps pre code pc gas stack, word]

end Compiler.Proofs.IRGeneration.NativeSourceCheckedRejection
