import Verity.Core
import Verity.Core.Invariant

/-!
# Source-level semantics of the `nonreentrant(lock)` guard

The compiler attaches a transient-storage prologue/epilogue to annotated
entrypoints (`attachNonReentrantGuard`): `tload` the lock slot, revert if set,
`tstore 1`, run the body, and `tstore 0` on every successful exit (reverting
exits roll the acquire back).  This module gives that transformation an
executable source semantics, `guarded`, and proves the guard laws the
roadmap's reentrancy lane needs:

- lock free → the body runs with the lock observably set, and a successful
  exit releases it;
- lock held → revert with the pre-call state unchanged;
- a callback into *any* entrypoint guarded by the same lock, made while the
  lock is held, is the identity as a state transformer — so whole reentry
  schedules of same-lock entrypoints collapse to the identity, which is the
  formal statement that the guard closes the reentry window.

Connecting `guarded` to the Yul emitted by `attachNonReentrantGuard`, and
lifting the supported-fragment `noNonReentrant` restriction, are the
follow-up steps of this lane.  EIP-1153 end-of-transaction erasure is not
modeled here: within a transaction the release on successful exit already
restores the pre-call lock value.
-/
namespace Verity.Core.NonReentrantGuard

open Verity
open Verity.Core.Invariant (Preserves runSeq)

/-- Write `value` into transient lock slot `slot`. -/
def setLock (slot : Nat) (value : Uint256) (s : ContractState) : ContractState :=
  { s with transientStorage := fun k => if k == slot then value else s.transientStorage k }

@[simp] theorem setLock_reads (slot : Nat) (value : Uint256) (s : ContractState) :
    (setLock slot value s).transientStorage slot = value := by
  simp [setLock]

@[simp] theorem setLock_reads_other (slot k : Nat) (value : Uint256)
    (s : ContractState) (h : k ≠ slot) :
    (setLock slot value s).transientStorage k = s.transientStorage k := by
  simp [setLock, h]

/-- Executable semantics of a `nonreentrant(slot)` entrypoint. -/
def guarded (slot : Nat) (body : Contract α) : Contract α :=
  fun s =>
    if s.transientStorage slot = 0 then
      match body.run (setLock slot 1 s) with
      | .success a s' => .success a (setLock slot 0 s')
      | .revert msg _ => .revert msg s
    else
      ContractResult.revert "reentrant call blocked" s

/-- Lock held → the guarded entrypoint reverts without touching the state. -/
theorem guarded_locked_reverts (slot : Nat) (body : Contract α)
    (s : ContractState) (hlock : s.transientStorage slot ≠ 0) :
    guarded slot body s = ContractResult.revert "reentrant call blocked" s := by
  simp [guarded, hlock]

/-- Lock free → the body runs from the locked state; successful exits release
the lock, reverting exits roll back to the pre-call state. -/
theorem guarded_free_runs_body (slot : Nat) (body : Contract α)
    (s : ContractState) (hfree : s.transientStorage slot = 0) :
    guarded slot body s =
      match body.run (setLock slot 1 s) with
      | .success a s' => .success a (setLock slot 0 s')
      | .revert msg _ => .revert msg s := by
  simp [guarded, hfree]

/-- The body always observes the lock set. -/
theorem body_observes_lock (slot : Nat) (s : ContractState) :
    (setLock slot 1 s).transientStorage slot = 1 := by simp

/-- A successful guarded run exits with the lock released, so a later
top-level call to a same-lock entrypoint in the same transaction is
allowed. -/
theorem guarded_success_releases (slot : Nat) (body : Contract α)
    (s s' : ContractState) (a : α)
    (hrun : guarded slot body s = ContractResult.success a s') :
    s'.transientStorage slot = 0 := by
  by_cases hfree : s.transientStorage slot = 0
  · rw [guarded_free_runs_body slot body s hfree] at hrun
    cases hbody : body.run (setLock slot 1 s) with
    | success b sb => rw [hbody] at hrun; injection hrun with _ hs; rw [← hs]; simp
    | revert msg sr => rw [hbody] at hrun; cases hrun
  · rw [guarded_locked_reverts slot body s hfree] at hrun
    cases hrun

/-- The reentry-window theorem: while the lock is held, a callback into any
same-lock guarded entrypoint is the identity as a state transformer. -/
theorem guarded_reentry_blocked (slot : Nat) (body : Contract α)
    (s : ContractState) (hlock : s.transientStorage slot ≠ 0) :
    (guarded slot body).runState s = s := by
  unfold Contract.runState
  rw [guarded_locked_reverts slot body s hlock]

/-- Whole reentry schedules of same-lock guarded entrypoints collapse to the
identity on locked states: no interleaving of guarded entrypoints can act
inside the window.  This is the schedule-level closure of the guard. -/
theorem runSeq_guarded_locked_id (slot : Nat) (entries : List (Contract Unit))
    (s : ContractState) (hlock : s.transientStorage slot ≠ 0) :
    runSeq (entries.map (fun entry => (guarded slot entry).runState)) s = s := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      show runSeq _ ((guarded slot entry).runState s) = s
      rw [guarded_reentry_blocked slot entry s hlock]
      exact ih

/-- Guarded entrypoints trivially preserve any invariant on locked states;
packaged in the `Preserves` shape used by `ReentrancySpec` registries. -/
theorem guarded_preserves_on_locked (slot : Nat) (body : Contract Unit)
    (Inv : ContractState → Prop) :
    ∀ s, s.transientStorage slot ≠ 0 → Inv s →
      Inv ((guarded slot body).runState s) := by
  intro s hlock hInv
  rw [guarded_reentry_blocked slot body s hlock]
  exact hInv

end Verity.Core.NonReentrantGuard
