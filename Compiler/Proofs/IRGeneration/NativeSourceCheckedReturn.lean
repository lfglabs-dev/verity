import Compiler.Proofs.IRGeneration.NativeSourceCheckedInputRejection

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedReturn
open EvmYul EVM EVM.Proof EVM.InstructionGasGroups

def fallthrough (pre : EVM.State) (tail : Stack UInt256) : EVM.State :=
  { stepPre 10 pre with pc := pre.pc + UInt256.ofNat 1, stack := tail }

theorem zero_transition (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (stack : pre.stack = UInt256.ofNat 91 :: UInt256.ofNat 0 :: tail) :
    EVM.step (fuel + 1) 10 (some (.JUMPI, none)) pre = .ok (fallthrough pre tail) := by
  change EvmYul.step (τ := .EVM) .JUMPI none (stepPre 10 pre) = _
  unfold EvmYul.step
  simp only [stepPre, stack]
  rfl

theorem continue_zero (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 962)
    (stack : pre.stack = UInt256.ofNat 91 :: UInt256.ofNat 0 :: tail)
    (gas : 10 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (fallthrough pre tail) := by
  have decoded : decodeAt pre = (.JUMPI, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceAddressBranch.decode962]; rfl
  have check := NativeSourceJumpChecks.rejection_jumpi pre (UInt256.ofNat 0) tail stack
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) depth
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  exact X_succ_of_continue decoded check (zero_transition fuel pre tail stack) rfl

theorem jump_check (jumps : Array UInt256) (pre : EVM.State)
    (gas : 8 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 1 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024)
    (destination : EVM.X.notIn pre.stack[0]? jumps = false) :
    Z jumps .JUMP pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 8) := by
  have cost (state : EVM.State) : C' state .JUMP = 8 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [destination, show ¬pre.stack.length < 1 by omega, show ¬pre.stack.length - 1 > 1024 by omega]

theorem continue_return (fuel : Nat) (pre : EVM.State) (ret word : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 963)
    (stack : pre.stack = ret :: word :: tail) (gas : 8 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022)
    (destination : ret ∈ EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) :
    EVM.X (fuel + 2) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceAddressBranch.returned 8 pre ret word tail) := by
  have decoded : decodeAt pre = (.JUMP, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceAddressBranch.decode963]; rfl
  have lookup : EVM.X.notIn pre.stack[0]? (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) = false := by
    rw [stack]
    change (!(EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)).contains ret) = false
    rw [NativeSourceJumpChecks.contains_of_mem _ ret destination]; rfl
  have check := jump_check _ pre (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega) lookup
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceAddressBranch.return_step fuel 8 pre ret word tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem fallthrough_frame (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 962) :
    (fallthrough pre tail).executionEnv.code = NativeSourceAbiWrite.code ∧
      (fallthrough pre tail).pc = UInt256.ofNat 963 ∧ (fallthrough pre tail).stack = tail := by
  refine ⟨code, ?_, rfl⟩
  change pre.pc + UInt256.ofNat 1 = _
  rw [pc]; decide

theorem execute_branch_return (fuel : Nat) (pre : EVM.State) (ret word : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 959)
    (stack : pre.stack = UInt256.ofNat 0 :: ret :: word :: tail)
    (gas : 21 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020)
    (destination : ret ∈ EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) :
    EVM.X (fuel + 4) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceAddressBranch.returned 8
          (fallthrough (NativeSourceAddressBranch.pushed 3 pre) (ret :: word :: tail)) ret word tail) := by
  have pushed := NativeSourceCheckedPushRejection.pushed_frame pre code pc
  have g1 : (NativeSourceAddressBranch.pushed 3 pre).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have frame := fallthrough_frame _ (ret :: word :: tail) pushed.1 pushed.2.1
  have g2 : (fallthrough (NativeSourceAddressBranch.pushed 3 pre) (ret :: word :: tail)).gasAvailable.toNat =
      (NativeSourceAddressBranch.pushed 3 pre).gasAvailable.toNat - 10 :=
    NativeSourceCheckedRejection.gas_sub _ 10 (by decide) (by omega)
  rw [NativeSourceCheckedPushRejection.continue_push (fuel + 2) _ pre code pc (by omega)
    (by simp only [stack, List.length_cons]; omega)]
  rw [continue_zero (fuel + 1) _ (ret :: word :: tail) pushed.1 pushed.2.1
    (by rw [pushed.2.2, stack]) (by omega) (by simp only [List.length_cons]; omega)]
  exact continue_return fuel _ ret word tail frame.1 frame.2.1 frame.2.2 (by omega) (by omega) destination

end Compiler.Proofs.IRGeneration.NativeSourceCheckedReturn
