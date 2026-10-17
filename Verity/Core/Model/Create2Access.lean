import Verity.Core.Model.Create2Entry
import Verity.Core.Model.Create2NonceEntry

/-! Transaction-scoped EIP-2929 access effect at the CREATE2 boundary.
Caller rollback must restore the previous access set; constructor rollback
retains this update because it happens before the constructor snapshot. -/
namespace Verity.Core.Model.Create2Access
open Create2Entry

abbrev WarmAccounts := Nat → Bool

def warm (before : WarmAccounts) (target : Nat) : WarmAccounts :=
  fun query => if query = target then true else before query

/-- Preparation and nonce gates are measured/derived by their actual components.
No target access occurs on caller halt, depth failure or nonce overflow. -/
def update (before : WarmAccounts) (preparation : Preparation) (nonce target : Nat) :
    Except String WarmAccounts :=
  match preparation with
  | .exceptional | .depthFailure _ _ => .ok before
  | .forwarded _ =>
      if Create2NonceEntry.maxCreatorNonce < nonce then
        .error "CREATE2 creator nonce exceeds uint64 account projection"
      else if nonce = Create2NonceEntry.maxCreatorNonce then .ok before
      else .ok (warm before target)

theorem warm_target (before : WarmAccounts) (target : Nat) : warm before target target = true := by
  simp only [warm, if_true]

theorem warm_other (before : WarmAccounts) (target query : Nat) (other : query ≠ target) :
    warm before target query = before query := by
  simp only [warm, other, if_false]

theorem warm_idempotent (before : WarmAccounts) (target : Nat) :
    warm (warm before target) target = warm before target := by
  funext query
  unfold warm
  split <;> rfl

theorem update_exceptional (before : WarmAccounts) (nonce target : Nat) :
    update before .exceptional nonce target = .ok before := rfl

theorem update_depth_failure (before : WarmAccounts) (memory : Compiler.CompilationModel.DenoteMemory.Memory)
    (gas nonce target : Nat) : update before (.depthFailure memory gas) nonce target = .ok before := rfl

theorem update_nonce_overflow (before : WarmAccounts) (frame : Forwarded) (target : Nat) :
    update before (.forwarded frame) Create2NonceEntry.maxCreatorNonce target = .ok before := by
  simp only [update, Nat.lt_irrefl, if_false, if_true]

theorem update_legal_nonce (before : WarmAccounts) (frame : Forwarded) (nonce target : Nat)
    (legal : nonce < Create2NonceEntry.maxCreatorNonce) :
    update before (.forwarded frame) nonce target = .ok (warm before target) := by
  have noOverflow : nonce ≠ Create2NonceEntry.maxCreatorNonce := Nat.ne_of_lt legal
  have noInvalid : ¬ Create2NonceEntry.maxCreatorNonce < nonce := by omega
  simp only [update, noInvalid, noOverflow, if_false]

theorem update_invalid_nonce (before : WarmAccounts) (frame : Forwarded) (nonce target : Nat)
    (invalid : Create2NonceEntry.maxCreatorNonce < nonce) :
    update before (.forwarded frame) nonce target =
      .error "CREATE2 creator nonce exceeds uint64 account projection" := by
  simp only [update, invalid, if_true]

end Verity.Core.Model.Create2Access
