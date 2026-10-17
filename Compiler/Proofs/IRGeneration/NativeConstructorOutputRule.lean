import EvmYul.EVM.Proof.Block

/-! Native X output rule for a constructor invariant. The concrete step and
halting premises must still be proved for the real header; no output oracle is
installed in the interpreter. -/
namespace Compiler.Proofs.IRGeneration.NativeInitcodeFrames
open EvmYul EVM.Proof

/-- Lift actual one-step invariant/halting facts to a successful X result. -/
theorem X_output_of_invariant (invariant : EVM.State → Prop) (expected : ByteArray)
    (chargeInvariant : ∀ (before : EVM.State) (gas : UInt256), invariant before →
      invariant { before with gasAvailable := gas })
    (stepOutput : ∀ fuel gasCost instruction (before after : EVM.State),
      invariant before → instruction = decodeAt before →
      EVM.step fuel gasCost (some instruction) before = .ok after →
      (H after.toMachineState instruction.1 = none → invariant after) ∧
      (∀ bytes, H after.toMachineState instruction.1 = some bytes →
        instruction.1 ≠ .REVERT → bytes = expected))
    (fuel : Nat) (jumps : Array UInt256) (before after : EVM.State) (output : ByteArray)
    (holds : invariant before)
    (success : EVM.X fuel jumps before = .ok (.success after output)) :
    output = expected := by
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
      have midHolds : invariant mid := by rw [midEq]; exact chargeInvariant before _ holds
      have midDecode : decodeAt before = decodeAt mid := by rw [midEq]; rfl
      cases stepped : EVM.step fuel gasCost (some (decodeAt before)) mid with
      | error reason =>
        rw [X_succ_of_step_error rfl checked stepped] at success
        cases success
      | ok next =>
        have facts := stepOutput fuel gasCost (decodeAt before) mid next midHolds midDecode stepped
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
