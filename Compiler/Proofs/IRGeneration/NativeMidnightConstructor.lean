import Compiler.Proofs.IRGeneration.MidnightHeaderProgress
import Compiler.Proofs.IRGeneration.NativeInitcodeRunFrames
import Compiler.Proofs.IRGeneration.NativeInitcodeFuel

/-! Concrete native Midnight constructor invariant, world frames and fuel
adequacy. These concern actual X, not a separately fabricated callee state.
Output-byte/gas correspondence and Lambda commits are separate obligations. -/
namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof
open NativeInitcodeFrames
open Verity.Core.Model.MidnightInitcode

/-- The constructor cannot execute appended runtime bytes before it halts. -/
def InHeader (payload : ByteArray) (state : EVM.State) : Prop :=
  state.executionEnv.code = initcode payload ∧ state.pc.toNat < 11

def remaining (state : EVM.State) : Nat := 11 - state.pc.toNat

private theorem header_decodes (payload : ByteArray) (pc : UInt256) (inside : pc.toNat < 11) :
    ∃ op arg, EVM.decode (initcode payload) pc = some (op, arg) := by
  have parses : ∃ op, (header.get? pc.toNat >>= EVM.parseInstr) = some op := by
    have positions : pc.toNat = 0 ∨ pc.toNat = 1 ∨ pc.toNat = 2 ∨
        pc.toNat = 3 ∨ pc.toNat = 4 ∨ pc.toNat = 5 ∨ pc.toNat = 6 ∨
        pc.toNat = 7 ∨ pc.toNat = 8 ∨ pc.toNat = 9 ∨ pc.toNat = 10 := by omega
    rcases positions with h | h | h | h | h | h | h | h | h | h | h
    all_goals rw [h]
    all_goals first
      | exact ⟨.Push .PUSH1, rfl⟩
      | exact ⟨.SIGNEXTEND, rfl⟩
      | exact ⟨.CODESIZE, rfl⟩
      | exact ⟨.SUB, rfl⟩
      | exact ⟨.DUP1, rfl⟩
      | exact ⟨.Push .PUSH0, rfl⟩
      | exact ⟨.CODECOPY, rfl⟩
      | exact ⟨.RETURN, rfl⟩
  obtain ⟨op, parsed⟩ := parses
  have fetch : ((initcode payload).get? pc.toNat >>= EVM.parseInstr) = some op := by
    rw [native_header_byte payload pc.toNat inside]; exact parsed
  unfold EVM.decode
  simp only [fetch]
  exact ⟨op, _, rfl⟩

/-- The native decoder's STOP default is never used inside this header. -/
theorem decode_header (payload : ByteArray) (before : EVM.State) (holds : InHeader payload before) :
    EVM.decode before.executionEnv.code before.pc = some (decodeAt before) := by
  obtain ⟨op, arg, decoded⟩ := header_decodes payload before.pc holds.2
  unfold decodeAt
  rw [holds.1, decoded]
  rfl

private theorem step_fuel (payload : ByteArray) (before : EVM.State)
    (holds : InHeader payload before) (fuel gasCost : Nat) :
    EVM.step (fuel + 1) gasCost (some (decodeAt before)) before =
      EVM.step 1 gasCost (some (decodeAt before)) before := by
  have decoded := decode_header payload before holds
  rw [holds.1] at decoded
  rcases native_header_local payload before.pc _ _ holds.2 decoded with supported | returning
  · exact supported_step_fuel fuel _ before _ gasCost supported
  · have pair : decodeAt before = (.RETURN, (decodeAt before).2) := by
      exact Prod.ext returning rfl
    rw [pair]
    simp only [EVM.step, Bind.bind, Pure.pure, Except.bind, Except.pure]

private theorem continue_not_return {before next : EVM.State}
    (continues : H next.toMachineState (decodeAt before).1 = none) :
    (decodeAt before).1 ≠ .RETURN := by
  intro returning
  rw [returning] at continues
  change some _ = none at continues
  cases continues

/-- Actual continuing steps preserve the invariant and strictly decrease rank. -/
theorem step_invariant (payload : ByteArray) (fuel gasCost : Nat)
    (before after : EVM.State) (holds : InHeader payload before)
    (success : EVM.step fuel gasCost (some (decodeAt before)) before = .ok after)
    (continues : H after.toMachineState (decodeAt before).1 = none) :
    InHeader payload after ∧ remaining after < remaining before := by
  have result := header_invariant_step payload fuel gasCost before after _ _ holds.1 holds.2
    (decode_header payload before holds) (continue_not_return continues) success
  exact ⟨⟨result.1, result.2.1⟩, result.2.2⟩

/-- All premises use the actual memory-gas-charged state produced by Z. -/
theorem local_steps (payload : ByteArray) (jumps : Array UInt256)
    (before mid : EVM.State) (gasCost : Nat) (holds : InHeader payload before)
    (checked : Z jumps (decodeAt before).1 before = .ok (mid, gasCost)) :
    (∀ k, EVM.step (k + 1) gasCost (some (decodeAt before)) mid =
      EVM.step 1 gasCost (some (decodeAt before)) mid) ∧
    EVM.step 1 gasCost (some (decodeAt before)) mid ≠ .error .OutOfFuel ∧
    (∀ next, EVM.step 1 gasCost (some (decodeAt before)) mid = .ok next →
      H next.toMachineState (decodeAt before).1 = none →
      InHeader payload next ∧ remaining next < remaining before) := by
  have midEq := Z_ok_state checked
  have midHolds : InHeader payload mid := by rw [midEq]; exact holds
  have decodeEq : decodeAt mid = decodeAt before := by rw [midEq]; rfl
  have decoded := decode_header payload mid midHolds
  rw [midHolds.1] at decoded
  refine ⟨?_, ?_, ?_⟩
  · intro k; rw [← decodeEq]; exact step_fuel payload mid midHolds k gasCost
  · rw [← decodeEq]
    exact header_step_ne_outOfFuel payload mid _ _ gasCost midHolds.2 decoded
  · intro next success continues
    rw [← decodeEq] at success continues
    have result := step_invariant payload 1 gasCost mid next midHolds success continues
    rw [midEq] at result
    exact result

/-- A uniform conservative bound for any state inside the constructor header.
This excludes interpreter exhaustion; real EVM gas/stack exceptions remain. -/
theorem fuel_adequate (payload : ByteArray) (jumps : Array UInt256)
    (before : EVM.State) (holds : InHeader payload before)
    (fuel : Nat) (enough : 13 ≤ fuel) :
    EVM.X fuel jumps before ≠ .error .OutOfFuel := by
  exact X_ne_outOfFuel_of_rank (InHeader payload) remaining (local_steps payload jumps)
    11 fuel before holds (Nat.sub_le _ _) enough

/-- All sufficiently fueled native runs have identical full outcomes. -/
theorem fuel_stable (payload : ByteArray) (jumps : Array UInt256)
    (before : EVM.State) (holds : InHeader payload before)
    (fuelA fuelB : Nat) (enoughA : 13 ≤ fuelA) (enoughB : 13 ≤ fuelB) :
    EVM.X fuelA jumps before = EVM.X fuelB jumps before := by
  apply X_fuel_independent (InHeader payload) remaining ?_ 11 fuelA fuelB before holds
    (Nat.sub_le _ _) enoughA enoughB
  intro state mid gasCost invariant checked
  have facts := local_steps payload jumps state mid gasCost invariant checked
  exact ⟨facts.1, facts.2.2⟩

/-- A successful actual constructor run preserves the entire native world,
including accounts, original storage, substate and execution environment. -/
theorem success_state (payload : ByteArray) (jumps : Array UInt256)
    (before after : EVM.State) (output : ByteArray) (fuel : Nat)
    (holds : InHeader payload before)
    (success : EVM.X fuel jumps before = .ok (.success after output)) :
    after.toState = before.toState := by
  apply X_state_of_invariant (InHeader payload) ?_ ?_ fuel jumps before after output holds success
  · intro state gas invariant; exact invariant
  · intro stepFuel gasCost instruction state next invariant decoded stepped
    subst instruction
    have decodedHeader := decode_header payload state invariant
    rw [invariant.1] at decodedHeader
    refine ⟨?_, native_header_step_state payload stepFuel gasCost state next _ _
      invariant.2 decodedHeader stepped⟩
    intro continues
    exact (step_invariant payload stepFuel gasCost state next invariant stepped continues).1

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
