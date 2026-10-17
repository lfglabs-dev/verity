import Verity.Core.Model.MidnightInitcode
import Verity.Core.Model.Create2Runtime

/-! Computed callee execution and deposit for Midnight's actual raw-payload
constructor. Input gas is actual forwarded callee gas. CREATE2 caller entry,
nonce/depth/static/cap guards, hashing and EIP-150 are outside this component. -/
namespace Verity.Core.Model.Create2Callee
open Create2Accounts Create2Runtime MidnightInitcode

def depositCost (runtime : ByteArray) : Nat := 200 * runtime.size

structure Execution where
  result : InitcodeResult
  gasLeft : Nat

/-- No supplied execution result or gas-availability certificate. Illegal code
and deposit OOG are exceptional child halts: they return no gas or bytes. -/
def execute (payload : ByteArray) (gas : Nat) : Except String Execution :=
  match runMetered 9 (initcode payload) initial gas with
  | .error message => .error message
  | .ok .outOfGas => .ok { result := .exceptional, gasLeft := 0 }
  | .ok (.returned runtime _ remaining) =>
      if runtimeAccepted runtime && decide (depositCost runtime ≤ remaining) then
        .ok { result := .returned runtime true, gasLeft := remaining - depositCost runtime }
      else .ok { result := .exceptional, gasLeft := 0 }

theorem execute_prefix_out_of_gas (payload : ByteArray)
    (bounded : 11 + payload.size < modulus) (gas : Nat)
    (exhausted : gas < prefixCost payload.size) :
    execute payload gas = .ok { result := .exceptional, gasLeft := 0 } := by
  simp only [execute, metered_prefix payload bounded gas, exhausted, if_true]

theorem execute_rejected (payload : ByteArray)
    (bounded : 11 + payload.size < modulus) (gas : Nat)
    (rejected : runtimeAccepted payload = false) :
    execute payload gas = .ok { result := .exceptional, gasLeft := 0 } := by
  unfold execute
  rw [metered_prefix payload bounded gas]
  by_cases exhausted : gas < prefixCost payload.size
  · simp only [exhausted, if_true]
  · simp [exhausted, rejected]

theorem execute_deposit_out_of_gas (payload : ByteArray)
    (bounded : 11 + payload.size < modulus) (gas : Nat)
    (exhausted : gas < prefixCost payload.size + depositCost payload) :
    execute payload gas = .ok { result := .exceptional, gasLeft := 0 } := by
  by_cases early : gas < prefixCost payload.size
  · exact execute_prefix_out_of_gas payload bounded gas early
  · have deposit : ¬ depositCost payload ≤ gas - prefixCost payload.size := by omega
    simp [execute, metered_prefix payload bounded gas, early, deposit]

theorem execute_success (payload : ByteArray)
    (bounded : 11 + payload.size < modulus) (gas : Nat)
    (accepted : runtimeAccepted payload = true)
    (enough : prefixCost payload.size + depositCost payload ≤ gas) :
    execute payload gas = .ok
      { result := .returned payload true,
        gasLeft := gas - (prefixCost payload.size + depositCost payload) } := by
  have enoughPrefix : ¬ gas < prefixCost payload.size := by omega
  have deposit : depositCost payload ≤ gas - prefixCost payload.size := by omega
  simp only [execute, metered_prefix payload bounded gas, enoughPrefix, if_false, accepted,
    deposit, decide_true, Bool.and_self, if_true]
  congr 2
  omega

/-- Exact computed result, including complete code-deposit gas. -/
theorem execute_formula (payload : ByteArray)
    (bounded : 11 + payload.size < modulus) (gas : Nat) :
    execute payload gas =
      if runtimeAccepted payload && decide (prefixCost payload.size + depositCost payload ≤ gas) then
        .ok { result := .returned payload true, gasLeft := gas - (prefixCost payload.size + depositCost payload) }
      else .ok { result := .exceptional, gasLeft := 0 } := by
  cases accepted : runtimeAccepted payload with
  | false => simp only [Bool.false_and, Bool.false_eq_true, if_false]
             exact execute_rejected payload bounded gas accepted
  | true =>
      by_cases enough : prefixCost payload.size + depositCost payload ≤ gas
      · simp only [enough, decide_true, Bool.and_self, if_true]
        exact execute_success payload bounded gas accepted enough
      · simp only [enough, decide_false, Bool.and_false, Bool.false_eq_true, if_false]
        exact execute_deposit_out_of_gas payload bounded gas (Nat.lt_of_not_ge enough)

structure EnteredResult where
  outcome : Outcome
  gasLeft : Nat

/-- Account reservation occurs before callee evaluation. A collision consumes
all forwarded gas without executing constructor instructions. Caller entry
checks must already have succeeded before invoking this entered-boundary API. -/
def runEntered (before : Accounts) (creator target : Nat) (payload : ByteArray)
    (gas : Nat) : Except String EnteredResult :=
  match reserve before creator target with
  | .collision after => .ok { outcome := .failed after ByteArray.empty, gasLeft := 0 }
  | .reserved _ =>
      match execute payload gas with
      | .error message => .error message
      | .ok execution => .ok
          { outcome := finish before creator target execution.result, gasLeft := execution.gasLeft }

theorem runEntered_collision (before : Accounts) (creator target : Nat)
    (after : Accounts) (collision : reserve before creator target = .collision after)
    (payload : ByteArray) (gas : Nat) :
    runEntered before creator target payload gas =
      .ok { outcome := .failed after ByteArray.empty, gasLeft := 0 } := by
  simp only [runEntered, collision]

theorem runEntered_created (before : Accounts) (creator target : Nat)
    (after : Accounts) (reserved : reserve before creator target = .reserved after)
    (payload : ByteArray) (bounded : 11 + payload.size < modulus) (gas : Nat)
    (accepted : runtimeAccepted payload = true)
    (enough : prefixCost payload.size + depositCost payload ≤ gas) :
    runEntered before creator target payload gas = .ok
      { outcome := .created target (installRuntime after target payload),
        gasLeft := gas - (prefixCost payload.size + depositCost payload) } := by
  simp only [runEntered, reserved, execute_success payload bounded gas accepted enough]
  rw [finish_returned before creator target after reserved payload accepted]

theorem runEntered_deposit_out_of_gas (before : Accounts) (creator target : Nat)
    (after : Accounts) (reserved : reserve before creator target = .reserved after)
    (payload : ByteArray) (bounded : 11 + payload.size < modulus) (gas : Nat)
    (exhausted : gas < prefixCost payload.size + depositCost payload) :
    runEntered before creator target payload gas = .ok
      { outcome := .failed (bumpCreator before creator) ByteArray.empty, gasLeft := 0 } := by
  simp only [runEntered, reserved, execute_deposit_out_of_gas payload bounded gas exhausted]
  rw [finish_exceptional before creator target after reserved]

theorem runEntered_rejected (before : Accounts) (creator target : Nat)
    (after : Accounts) (reserved : reserve before creator target = .reserved after)
    (payload : ByteArray) (bounded : 11 + payload.size < modulus) (gas : Nat)
    (rejected : runtimeAccepted payload = false) :
    runEntered before creator target payload gas = .ok
      { outcome := .failed (bumpCreator before creator) ByteArray.empty, gasLeft := 0 } := by
  simp only [runEntered, reserved, execute_rejected payload bounded gas rejected]
  rw [finish_exceptional before creator target after reserved]

theorem runEntered_frame (before : Accounts) (creator target query : Nat)
    (payload : ByteArray) (gas : Nat) (result : EnteredResult)
    (executed : runEntered before creator target payload gas = .ok result)
    (notCreator : query ≠ creator) (notTarget : query ≠ target) :
    result.outcome.accounts query = before query := by
  cases reservation : reserve before creator target with
  | collision after =>
      simp only [runEntered, reservation, Except.ok.injEq] at executed
      cases executed
      exact reserve_frame before creator target query notCreator notTarget
        |> fun h => by simpa only [reservation, Reservation.accounts, Outcome.accounts] using h
  | reserved after =>
      cases computation : execute payload gas with
      | error message => simp [runEntered, reservation, computation] at executed
      | ok execution =>
          simp only [runEntered, reservation, computation, Except.ok.injEq] at executed
          cases executed
          exact finish_frame before creator target query execution.result notCreator notTarget

end Verity.Core.Model.Create2Callee
