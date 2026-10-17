import Verity.Core.Model.Create2Accounts

/-! Account/returndata completion for value-zero creation by a constructor that
makes no persistent state changes, such as Midnight's return-data initcode.
The actual initcode execution and code-deposit gas decision are explicit inputs;
this component is not an initcode/gas evaluator or Solidity admission. -/
namespace Verity.Core.Model.Create2Runtime
open Create2Accounts

inductive InitcodeResult where
  | returned (runtime : ByteArray) (depositGasAvailable : Bool)
  | reverted (data : ByteArray)
  | exceptional

inductive Outcome where
  | created (address : Nat) (accounts : Accounts)
  | failed (accounts : Accounts) (returndata : ByteArray)

def Outcome.accounts : Outcome → Accounts
  | .created _ accounts | .failed accounts _ => accounts

def runtimeAccepted (runtime : ByteArray) : Bool :=
  decide (runtime.size ≤ 24576) && runtime.data[0]?.getD 0 != (0xef : UInt8)

def installRuntime (accounts : Accounts) (target : Nat) (runtime : ByteArray) : Accounts :=
  fun query => if query = target then { accounts query with code := runtime } else accounts query

/-- A failed constructor or code deposit restores the target snapshot, keeping
only the creator nonce increment. Revert bytes survive only an actual REVERT. -/
def finish (before : Accounts) (creator target : Nat) (result : InitcodeResult) : Outcome :=
  match reserve before creator target with
  | .collision after => .failed after ByteArray.empty
  | .reserved after =>
      match result with
      | .returned runtime depositGasAvailable =>
          if runtimeAccepted runtime && depositGasAvailable then
            .created target (installRuntime after target runtime)
          else .failed (bumpCreator before creator) ByteArray.empty
      | .reverted data => .failed (bumpCreator before creator) data
      | .exceptional => .failed (bumpCreator before creator) ByteArray.empty

theorem runtimeAccepted_oversized (runtime : ByteArray) (oversized : 24576 < runtime.size) :
    runtimeAccepted runtime = false := by
  simp [runtimeAccepted, Nat.not_le.mpr oversized]

theorem runtimeAccepted_ef (runtime : ByteArray)
    (first : runtime.data[0]?.getD 0 = (0xef : UInt8)) :
    runtimeAccepted runtime = false := by
  simp [runtimeAccepted, first]

theorem installRuntime_code (accounts : Accounts) (target : Nat) (runtime : ByteArray) :
    (installRuntime accounts target runtime target).code = runtime := by
  simp [installRuntime]

theorem installRuntime_nonce (accounts : Accounts) (target query : Nat) (runtime : ByteArray) :
    (installRuntime accounts target runtime query).nonce = (accounts query).nonce := by
  unfold installRuntime; split <;> rfl

theorem finish_collision (before : Accounts) (creator target : Nat) (after : Accounts)
    (collision : reserve before creator target = .collision after) (result : InitcodeResult) :
    finish before creator target result = .failed after ByteArray.empty := by
  simp [finish, collision]

theorem finish_returned (before : Accounts) (creator target : Nat) (after : Accounts)
    (reserved : reserve before creator target = .reserved after) (runtime : ByteArray)
    (accepted : runtimeAccepted runtime = true) :
    finish before creator target (.returned runtime true) =
      .created target (installRuntime after target runtime) := by
  simp [finish, reserved, accepted]

theorem finish_reverted (before : Accounts) (creator target : Nat) (after : Accounts)
    (reserved : reserve before creator target = .reserved after) (data : ByteArray) :
    finish before creator target (.reverted data) = .failed (bumpCreator before creator) data := by
  simp [finish, reserved]

theorem finish_exceptional (before : Accounts) (creator target : Nat) (after : Accounts)
    (reserved : reserve before creator target = .reserved after) :
    finish before creator target .exceptional =
      .failed (bumpCreator before creator) ByteArray.empty := by
  simp [finish, reserved]

theorem finish_deposit_out_of_gas (before : Accounts) (creator target : Nat) (after : Accounts)
    (reserved : reserve before creator target = .reserved after) (runtime : ByteArray) :
    finish before creator target (.returned runtime false) =
      .failed (bumpCreator before creator) ByteArray.empty := by
  simp [finish, reserved]

theorem finish_rejected_runtime (before : Accounts) (creator target : Nat) (after : Accounts)
    (reserved : reserve before creator target = .reserved after) (runtime : ByteArray)
    (rejected : runtimeAccepted runtime = false) (deposit : Bool) :
    finish before creator target (.returned runtime deposit) =
      .failed (bumpCreator before creator) ByteArray.empty := by
  simp [finish, reserved, rejected]

/-- Every branch preserves all accounts outside creator and target. -/
theorem finish_frame (before : Accounts) (creator target query : Nat) (result : InitcodeResult)
    (notCreator : query ≠ creator) (notTarget : query ≠ target) :
    (finish before creator target result).accounts query = before query := by
  have creatorFrame : bumpCreator before creator query = before query := by
    simp [bumpCreator, notCreator]
  have reservedFrame := reserve_frame before creator target query notCreator notTarget
  cases reservation : reserve before creator target with
  | collision after =>
      simp only [reservation, Reservation.accounts] at reservedFrame
      simpa only [finish, reservation, Outcome.accounts] using reservedFrame
  | reserved after =>
      simp only [reservation, Reservation.accounts] at reservedFrame
      cases result with
      | returned runtime deposit =>
          simp only [finish, reservation]
          split
          · simpa [Outcome.accounts, installRuntime, notTarget] using reservedFrame
          · exact creatorFrame
      | reverted data => simpa only [finish, reservation, Outcome.accounts] using creatorFrame
      | exceptional => simpa only [finish, reservation, Outcome.accounts] using creatorFrame

end Verity.Core.Model.Create2Runtime
