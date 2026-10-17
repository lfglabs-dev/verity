import EvmYul.EVM.Proof.Block

/-! Reusable native-X world frames using the upstream proven decomposition.
The invariant must tolerate gas charging and be preserved by actual steps. -/
namespace Compiler.Proofs.IRGeneration.NativeInitcodeFrames
open EvmYul EVM.Proof

/-- Every successful native X run preserves State when its actual steps do.
This exposes gas charging separately: no gas-blind fabricated prestate is used. -/
theorem X_state_of_invariant (invariant : EVM.State → Prop)
    (chargeInvariant : ∀ (before : EVM.State) (gas : UInt256), invariant before →
      invariant { before with gasAvailable := gas })
    (stepFrame : ∀ fuel gasCost instruction (before after : EVM.State),
      invariant before → instruction = decodeAt before →
      EVM.step fuel gasCost (some instruction) before = .ok after →
      (H after.toMachineState instruction.1 = none → invariant after) ∧
        after.toState = before.toState)
    (fuel : Nat) (jumps : Array UInt256) (before after : EVM.State) (output : ByteArray)
    (holds : invariant before)
    (success : EVM.X fuel jumps before = .ok (.success after output)) :
    after.toState = before.toState := by
  induction fuel generalizing before with
  | zero => rw [X_zero] at success; cases success
  | succ fuel ih =>
    cases checked : Z jumps (decodeAt before).1 before with
    | error reason =>
      rw [X_succ_of_Z_error rfl checked] at success
      cases success
    | ok entry =>
      rcases entry with ⟨mid, gasCost⟩
      have midEq := Z_ok_state checked
      have midState : mid.toState = before.toState := by rw [midEq]; rfl
      have midHolds : invariant mid := by rw [midEq]; exact chargeInvariant before _ holds
      have midDecode : decodeAt before = decodeAt mid := by rw [midEq]; rfl
      cases stepped : EVM.step fuel gasCost (some (decodeAt before)) mid with
      | error reason =>
        rw [X_succ_of_step_error rfl checked stepped] at success
        cases success
      | ok next =>
        have frame := stepFrame fuel gasCost (decodeAt before) mid next midHolds midDecode stepped
        cases halts : H next.toMachineState (decodeAt before).1 with
        | none =>
          rw [X_succ_of_continue rfl checked stepped halts] at success
          exact (ih next (frame.1 halts) success).trans (frame.2.trans midState)
        | some data =>
          by_cases reverted : (decodeAt before).1 = .REVERT
          · rw [X_succ_of_revert rfl checked stepped halts reverted] at success
            cases success
          · rw [X_succ_of_halt rfl checked stepped halts reverted] at success
            cases success
            exact frame.2.trans midState

end Compiler.Proofs.IRGeneration.NativeInitcodeFrames
