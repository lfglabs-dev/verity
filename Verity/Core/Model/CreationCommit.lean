import Verity.Core.Model.CreationWorld
import Verity.Core.Model.Create2Runtime

/-! Canonical-world commit of the account component, not opcode execution.
The word-returndata adapter accepts only an empty creation buffer; a nonempty
byte buffer fails explicitly rather than being padded or discarded. -/
namespace Verity.Core.Model.CreationCommit
open Create2Runtime

/-- Erase exactly the account, code-size and returndata observations that this
commit may change. All storage, memory, events, context and calls remain. -/
def frame (world : Verity.ContractState) : Verity.ContractState :=
  { world with creationAccounts := fun _ => {}, codeSize := fun _ => 0, returndata := [] }

def commit (world : Verity.ContractState) : Outcome → Except String Verity.ContractState
  | .created target accounts => .ok
      { world with creationAccounts := accounts,
                   codeSize := fun query => if query = target then
                     Uint256.ofNat (accounts target).code.size else world.codeSize query,
                   returndata := [] }
  | .failed accounts data =>
      if data.size = 0 then .ok { world with creationAccounts := accounts, returndata := [] }
      else .error "CREATE2 constructor revert requires the exact byte-returndata interpreter"

theorem commit_created_codeSize (world : Verity.ContractState) (target : Nat)
    (accounts : Create2Accounts.Accounts) (next : Verity.ContractState)
    (committed : commit world (.created target accounts) = .ok next) :
    next.codeSize target = Uint256.ofNat (accounts target).code.size := by
  simp only [commit, Except.ok.injEq] at committed
  cases committed
  simp

theorem commit_created_codeSize_frame (world : Verity.ContractState) (target query : Nat)
    (accounts : Create2Accounts.Accounts) (next : Verity.ContractState)
    (committed : commit world (.created target accounts) = .ok next)
    (outside : query ≠ target) : next.codeSize query = world.codeSize query := by
  simp only [commit, Except.ok.injEq] at committed
  cases committed
  simp [outside]

theorem commit_failed_empty (world : Verity.ContractState) (accounts : Create2Accounts.Accounts) :
    commit world (.failed accounts ByteArray.empty) =
      .ok { world with creationAccounts := accounts, returndata := [] } := by
  simp only [commit, ByteArray.size_empty, if_true]

theorem commit_failed_nonempty (world : Verity.ContractState) (accounts : Create2Accounts.Accounts)
    (data : ByteArray) (nonempty : data.size ≠ 0) :
    commit world (.failed accounts data) =
      .error "CREATE2 constructor revert requires the exact byte-returndata interpreter" := by
  simp [commit, nonempty]

theorem commit_accounts (world : Verity.ContractState) (result : Outcome) (next : Verity.ContractState)
    (committed : commit world result = .ok next) : next.creationAccounts = result.accounts := by
  cases result with
  | created target accounts =>
      simp only [commit, Except.ok.injEq] at committed
      cases committed
      rfl
  | failed accounts data =>
      simp only [commit] at committed
      split at committed
      · cases committed; rfl
      · contradiction

/-- Every successful commit retains every other world observation, regardless
of creation success or failure. No old word-map poststate is substituted. -/
theorem commit_frame (world : Verity.ContractState) (result : Outcome) (next : Verity.ContractState)
    (committed : commit world result = .ok next) : frame next = frame world := by
  cases result with
  | created target accounts =>
      simp only [commit, Except.ok.injEq] at committed
      cases committed
      rfl
  | failed accounts data =>
      simp only [commit] at committed
      split at committed
      · cases committed; rfl
      · contradiction

end Verity.Core.Model.CreationCommit
