import EvmYul.EVM.Proof.Block

/-! Fuel adequacy for the actual native interpreter. This is a proof rule,
not an admission check: clients must prove actual-step independence and a
strictly decreasing rank before invoking it. Execution gas remains native. -/
namespace Compiler.Proofs.IRGeneration.NativeInitcodeFrames
open EvmYul EVM.Proof

private theorem ite_ne_fuel {α : Type} (condition : Prop) [Decidable condition]
    (left right : Except EVM.ExecutionException α)
    (leftOk : left ≠ .error .OutOfFuel) (rightOk : right ≠ .error .OutOfFuel) :
    (if condition then left else right) ≠ .error .OutOfFuel := by
  split <;> assumption

private theorem X_halt_fuel_eq
    {fuelA fuelB gasCost : Nat} {jumps : Array UInt256}
    {before mid next : EVM.State} {output : ByteArray}
    (checked : Z jumps (decodeAt before).1 before = .ok (mid, gasCost))
    (stepA : EVM.step fuelA gasCost (some (decodeAt before)) mid = .ok next)
    (stepB : EVM.step fuelB gasCost (some (decodeAt before)) mid = .ok next)
    (halts : H next.toMachineState (decodeAt before).1 = some output) :
    EVM.X (fuelA + 1) jumps before = EVM.X (fuelB + 1) jumps before := by
  by_cases reverted : (decodeAt before).1 = .REVERT
  · rw [X_succ_of_revert rfl checked stepA halts reverted,
      X_succ_of_revert rfl checked stepB halts reverted]
  · rw [X_succ_of_halt rfl checked stepA halts reverted,
      X_succ_of_halt rfl checked stepB halts reverted]

/-- A finite rank bounds interpreter fuel when actual accepted steps do not
recurse into calls/creation and every continuing step decreases that rank.
The equality covers success, revert and every exceptional result. In
particular, no OutOfFuel is reinterpreted as a Solidity-level revert here. -/
theorem X_fuel_independent
    (invariant : EVM.State → Prop) (rank : EVM.State → Nat)
    (localSteps : ∀ (before mid : EVM.State) (gasCost : Nat),
      invariant before →
      Z jumps (decodeAt before).1 before = .ok (mid, gasCost) →
      (∀ k, EVM.step (k + 1) gasCost (some (decodeAt before)) mid =
        EVM.step 1 gasCost (some (decodeAt before)) mid) ∧
      (∀ next, EVM.step 1 gasCost (some (decodeAt before)) mid = .ok next →
        H next.toMachineState (decodeAt before).1 = none →
        invariant next ∧ rank next < rank before))
    (bound fuelA fuelB : Nat) (before : EVM.State)
    (holds : invariant before) (rankBound : rank before ≤ bound)
    (enoughA : bound + 2 ≤ fuelA) (enoughB : bound + 2 ≤ fuelB) :
    EVM.X fuelA jumps before = EVM.X fuelB jumps before := by
  induction bound using Nat.strong_induction_on generalizing before fuelA fuelB with
  | h bound ih =>
    obtain ⟨left, rfl⟩ : ∃ n, fuelA = n + 2 := by
      exact ⟨fuelA - 2, by omega⟩
    obtain ⟨right, rfl⟩ : ∃ n, fuelB = n + 2 := by
      exact ⟨fuelB - 2, by omega⟩
    cases checked : Z jumps (decodeAt before).1 before with
    | error reason =>
      rw [X_succ_of_Z_error rfl checked, X_succ_of_Z_error rfl checked]
    | ok entry =>
      rcases entry with ⟨mid, gasCost⟩
      obtain ⟨stepFuel, decreases⟩ := localSteps before mid gasCost holds checked
      cases stepped : EVM.step 1 gasCost (some (decodeAt before)) mid with
      | error reason =>
        have leftStep : EVM.step (left + 1) gasCost (some (decodeAt before)) mid =
            .error reason := (stepFuel left).trans stepped
        have rightStep : EVM.step (right + 1) gasCost (some (decodeAt before)) mid =
            .error reason := (stepFuel right).trans stepped
        rw [X_succ_of_step_error rfl checked leftStep,
          X_succ_of_step_error rfl checked rightStep]
      | ok next =>
        have leftStep : EVM.step (left + 1) gasCost (some (decodeAt before)) mid =
            .ok next := (stepFuel left).trans stepped
        have rightStep : EVM.step (right + 1) gasCost (some (decodeAt before)) mid =
            .ok next := (stepFuel right).trans stepped
        cases halts : H next.toMachineState (decodeAt before).1 with
        | none =>
          rw [X_succ_of_continue rfl checked leftStep halts,
            X_succ_of_continue rfl checked rightStep halts]
          obtain ⟨nextHolds, smaller⟩ := decreases next stepped halts
          exact ih (rank next) (by omega) (left + 1) (right + 1) next nextHolds
            (Nat.le_refl _) (by omega) (by omega)
        | some data => exact X_halt_fuel_eq checked leftStep rightStep halts

/-- Native exceptional prechecks never manufacture interpreter-fuel errors. -/
theorem Z_ne_outOfFuel (jumps : Array UInt256) (op : Operation .EVM) (before : EVM.State) :
    Z jumps op before ≠ .error .OutOfFuel := by
  simp only [Z, Bind.bind, Pure.pure, Except.bind, Except.pure]
  repeat first | apply ite_ne_fuel | (intro impossible; cases impossible)

/-- A decreasing native rank also excludes interpreter OutOfFuel, provided
both actual native steps and Z distinguish it from real EVM exceptions. This
premise is stronger than fuel independence: a recursive step that consistently
returns OutOfFuel cannot satisfy it. -/
theorem X_ne_outOfFuel_of_rank
    (invariant : EVM.State → Prop) (rank : EVM.State → Nat)
    (localSteps : ∀ (before mid : EVM.State) (gasCost : Nat),
      invariant before → Z jumps (decodeAt before).1 before = .ok (mid, gasCost) →
      (∀ k, EVM.step (k + 1) gasCost (some (decodeAt before)) mid =
        EVM.step 1 gasCost (some (decodeAt before)) mid) ∧
      EVM.step 1 gasCost (some (decodeAt before)) mid ≠ .error .OutOfFuel ∧
      (∀ next, EVM.step 1 gasCost (some (decodeAt before)) mid = .ok next →
        H next.toMachineState (decodeAt before).1 = none →
        invariant next ∧ rank next < rank before))
    (bound fuel : Nat) (before : EVM.State) (holds : invariant before)
    (rankBound : rank before ≤ bound) (enough : bound + 2 ≤ fuel) :
    EVM.X fuel jumps before ≠ .error .OutOfFuel := by
  induction bound using Nat.strong_induction_on generalizing before fuel with
  | h bound ih =>
    obtain ⟨rest, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
    cases checked : Z jumps (decodeAt before).1 before with
    | error reason =>
      rw [X_succ_of_Z_error rfl checked]
      intro impossible
      have same := Except.error.inj impossible
      subst reason
      exact Z_ne_outOfFuel _ _ _ checked
    | ok entry =>
      rcases entry with ⟨mid, gasCost⟩
      obtain ⟨stepFuel, stepNotFuel, decreases⟩ := localSteps before mid gasCost holds checked
      cases stepped : EVM.step 1 gasCost (some (decodeAt before)) mid with
      | error reason =>
        have actual := (stepFuel rest).trans stepped
        rw [X_succ_of_step_error rfl checked actual]
        intro impossible
        have same := Except.error.inj impossible
        subst reason
        exact stepNotFuel stepped
      | ok next =>
        have actual := (stepFuel rest).trans stepped
        cases halts : H next.toMachineState (decodeAt before).1 with
        | none =>
          rw [X_succ_of_continue rfl checked actual halts]
          obtain ⟨nextHolds, smaller⟩ := decreases next stepped halts
          exact ih (rank next) (by omega) (rest + 1) next nextHolds (Nat.le_refl _) (by omega)
        | some data =>
          by_cases reverted : (decodeAt before).1 = .REVERT
          · rw [X_succ_of_revert rfl checked actual halts reverted]
            intro impossible; cases impossible
          · rw [X_succ_of_halt rfl checked actual halts reverted]
            intro impossible; cases impossible

end Compiler.Proofs.IRGeneration.NativeInitcodeFrames
