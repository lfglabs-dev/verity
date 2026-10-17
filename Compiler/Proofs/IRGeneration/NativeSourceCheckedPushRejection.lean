import Compiler.Proofs.IRGeneration.NativeSourceCheckedJumpRejection

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedPushRejection
open EvmYul EVM EVM.Proof EVM.InstructionGasGroups

theorem push2_check (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat) (depth : pre.stack.length < 1024) :
    Z jumps (.Push .PUSH2) pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state (.Push .PUSH2) = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

theorem continue_push (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 959)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : pre.stack.length < 1024) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps (NativeSourceAddressBranch.pushed 3 pre) := by
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 91, 2)) := by
    unfold decodeAt; rw [code, pc, NativeSourceAddressBranch.decode959]; rfl
  have check := push2_check jumps pre (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) depth
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceAddressBranch.push fuel 3 pre code pc
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem pushed_frame (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 959) :
    (NativeSourceAddressBranch.pushed 3 pre).executionEnv.code = NativeSourceAbiWrite.code ∧
      (NativeSourceAddressBranch.pushed 3 pre).pc = UInt256.ofNat 962 ∧
      (NativeSourceAddressBranch.pushed 3 pre).stack = UInt256.ofNat 91 :: pre.stack := by
  refine ⟨code, ?_, rfl⟩
  change pre.pc + UInt256.ofNat 3 = _
  rw [pc]; decide

theorem execute_exact (fuel : Nat) (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 959)
    (stack : pre.stack = condition :: tail) (nonzero : condition ≠ UInt256.ofNat 0)
    (gas : 19 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 7) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      .ok (.revert (UInt256.ofNat (pre.gasAvailable.toNat - 19)) ByteArray.empty) := by
  have frame := pushed_frame pre code pc
  have charged : (NativeSourceAddressBranch.pushed 3 pre).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  rw [continue_push (fuel + 5) _ pre code pc (by omega) (by simp only [stack, List.length_cons]; omega)]
  rw [NativeSourceCheckedJumpRejection.execute_exact fuel _ condition tail frame.1 frame.2.1
    (by rw [frame.2.2, stack]) nonzero (by omega) depth, charged]
  congr 3

end Compiler.Proofs.IRGeneration.NativeSourceCheckedPushRejection
