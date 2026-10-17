import EvmYul.EVM.Proof.Block

namespace Compiler.Proofs.IRGeneration.NativeInitcodeFrames
open EvmYul EVM.Proof

/-- A checked-step invariant may depend on gas: its premise sees the actual
pre-Z state, Z's memory-debited state, and the actual instruction result. -/
theorem X_result_of_checked_invariant (invariant : EVM.State → Prop)
    (result : EVM.State → ByteArray → Prop) (jumps : Array UInt256)
    (stepResult : ∀ fuel gasCost instruction (before mid after : EVM.State),
      invariant before → instruction = decodeAt before →
      Z jumps instruction.1 before = .ok (mid, gasCost) →
      EVM.step fuel gasCost (some instruction) mid = .ok after →
      (H after.toMachineState instruction.1 = none → invariant after) ∧
      (∀ bytes, H after.toMachineState instruction.1 = some bytes →
        instruction.1 ≠ .REVERT → result after bytes))
    (fuel : Nat) (before after : EVM.State) (output : ByteArray)
    (holds : invariant before)
    (success : EVM.X fuel jumps before = .ok (.success after output)) :
    result after output := by
  induction fuel generalizing before with
  | zero => rw [X_zero] at success; cases success
  | succ fuel ih =>
    cases checked : Z jumps (decodeAt before).1 before with
    | error reason =>
      rw [X_succ_of_Z_error rfl checked] at success
      cases success
    | ok entry =>
      rcases entry with ⟨mid, gasCost⟩
      cases stepped : EVM.step fuel gasCost (some (decodeAt before)) mid with
      | error reason =>
        rw [X_succ_of_step_error rfl checked stepped] at success
        cases success
      | ok next =>
        have facts := stepResult fuel gasCost (decodeAt before) before mid next
          holds rfl checked stepped
        cases halts : H next.toMachineState (decodeAt before).1 with
        | none =>
          rw [X_succ_of_continue rfl checked stepped halts] at success
          exact ih next (facts.1 halts) success
        | some data =>
          by_cases reverted : (decodeAt before).1 = .REVERT
          · rw [X_succ_of_revert rfl checked stepped halts reverted] at success
            cases success
          · rw [X_succ_of_halt rfl checked stepped halts reverted] at success
            cases success
            exact facts.2 output halts reverted

end Compiler.Proofs.IRGeneration.NativeInitcodeFrames
