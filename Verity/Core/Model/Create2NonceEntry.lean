import Verity.Core.Model.Create2Callee

/-! EIP-2681 creator-nonce gate, before account reservation/collision or callee
execution. Input gas is already-forwarded child gas; this is not full caller
entry (static/depth/value/cap/base/hash/memory checks remain separate). -/
namespace Verity.Core.Model.Create2NonceEntry
open Create2Accounts Create2Runtime Create2Callee

def maxCreatorNonce : Nat := 2^64 - 1

/-- Overflow at the legal uint64 maximum returns ZERO, leaves accounts alone,
and refunds all forwarded gas. An impossible larger projection fails closed. -/
def run (before : Accounts) (creator target : Nat) (payload : ByteArray)
    (gas : Nat) : Except String EnteredResult :=
  if maxCreatorNonce < (before creator).nonce then
    .error "CREATE2 creator nonce exceeds uint64 account projection"
  else if (before creator).nonce = maxCreatorNonce then
    .ok { outcome := .failed before ByteArray.empty, gasLeft := gas }
  else runEntered before creator target payload gas

theorem run_invalid_nonce (before : Accounts) (creator target : Nat)
    (payload : ByteArray) (gas : Nat) (invalid : maxCreatorNonce < (before creator).nonce) :
    run before creator target payload gas =
      .error "CREATE2 creator nonce exceeds uint64 account projection" := by
  simp only [run, invalid, if_true]

theorem run_nonce_overflow (before : Accounts) (creator target : Nat)
    (payload : ByteArray) (gas : Nat) (overflow : (before creator).nonce = maxCreatorNonce) :
    run before creator target payload gas =
      .ok { outcome := .failed before ByteArray.empty, gasLeft := gas } := by
  simp only [run, overflow, Nat.lt_irrefl, if_false, if_true]

theorem run_legal_nonce (before : Accounts) (creator target : Nat)
    (payload : ByteArray) (gas : Nat) (legal : (before creator).nonce < maxCreatorNonce) :
    run before creator target payload gas = runEntered before creator target payload gas := by
  have notOverflow : (before creator).nonce ≠ maxCreatorNonce := Nat.ne_of_lt legal
  have notInvalid : ¬ maxCreatorNonce < (before creator).nonce := by omega
  simp only [run, notInvalid, notOverflow, if_false]

theorem run_frame (before : Accounts) (creator target query : Nat)
    (payload : ByteArray) (gas : Nat) (result : EnteredResult)
    (executed : run before creator target payload gas = .ok result)
    (notCreator : query ≠ creator) (notTarget : query ≠ target) :
    result.outcome.accounts query = before query := by
  unfold run at executed
  split at executed
  · contradiction
  · split at executed
    · cases executed; rfl
    · exact runEntered_frame before creator target query payload gas result executed notCreator notTarget

end Verity.Core.Model.Create2NonceEntry
