/-
  Reentrancy rely-guarantee worked example: the Midnight `take` callback bug.

  This grounds the abstract rely-guarantee proof-of-concept against Verity's real
  `ContractState`/`Contract` monad and the `Verity.Core.Reentrancy` framework.
  It machine-checks the same two claims that motivated the framework:

    * the buggy (no-lock) `take` admits a PERMANENT bad-debt liquidation during
      the transient trade window, despite the final health check;

    * the lock-based `take` admits NO new liquidation for ANY reentrant adversary
      that respects the per-position lock — the rely condition that `liquidate`
      itself satisfies — and preserves the global invariant `I s := healthy ∨ locked`.

  Storage layout for the abstract position (one word each):
    slot 0 : health      (nonzero = healthy)
    slot 1 : lock        (nonzero = locked)
    slot 2 : liquidated  (nonzero = irreversibly liquidated / bad debt realized)
-/

import Verity.Core
import Verity.Core.Semantics
import Verity.Core.Reentrancy
import Verity.Core.Model.CallbackBridge

namespace Contracts.ReentrancyRelyGuarantee

open Verity
open Verity.Core.Invariant
open Verity.Core.Reentrancy

/-! ## Storage predicates and the lock-as-disjunct invariant -/

def healthSlot : Nat := 0
def lockSlot : Nat := 1
def liquidatedSlot : Nat := 2

def healthy (s : ContractState) : Prop := s.storage healthSlot ≠ 0
def locked (s : ContractState) : Prop := s.storage lockSlot ≠ 0
def liquidated (s : ContractState) : Prop := s.storage liquidatedSlot ≠ 0

/-- Global contract invariant: every position is healthy *or* currently locked.
    The `locked` disjunct is exactly what lets `take` hold the invariant while the
    seller is transiently unhealthy during the trade window. -/
def I (s : ContractState) : Prop := healthy s ∨ locked s

/-! ## The reentrant entrypoint: `liquidate` -/

/-- The irreversible liquidation, performed only on a genuinely unhealthy
    position that is NOT locked. Touches only the `liquidated` slot. -/
def liquidate (s : ContractState) : ContractState :=
  if s.storage lockSlot == 0 && s.storage healthSlot == 0 then
    s.writeSlot liquidatedSlot 1
  else s

@[simp] theorem liquidate_health (s : ContractState) :
    (liquidate s).storage healthSlot = s.storage healthSlot := by
  unfold liquidate; split <;> simp [healthSlot, liquidatedSlot, ContractState.writeSlot, ContractState.storage]

@[simp] theorem liquidate_lock (s : ContractState) :
    (liquidate s).storage lockSlot = s.storage lockSlot := by
  unfold liquidate; split <;> simp [lockSlot, liquidatedSlot, ContractState.writeSlot, ContractState.storage]

/-- Guarantee discharged by `liquidate`: it preserves `I`. It only ever changes
    the `liquidated` slot, leaving both `I` disjuncts (health, lock) untouched. -/
theorem liquidate_preserves_I : Preserves I liquidate := by
  intro s h
  simpa only [I, healthy, locked, liquidate_health, liquidate_lock] using h

/-- Guarantee discharged by `liquidate`: it never touches a *locked* position. -/
theorem liquidate_respects_lock {s : ContractState} (h : locked s) :
    liquidate s = s := by
  unfold liquidate
  split
  · next hcond =>
      rw [Bool.and_eq_true] at hcond
      exact absurd (eq_of_beq hcond.1) h
  · rfl

/-! ## Position setters (frame: each touches exactly one slot) -/

def setHealthy (b : Bool) (s : ContractState) : ContractState :=
  s.writeSlot healthSlot (if b then 1 else 0)

def setLock (b : Bool) (s : ContractState) : ContractState :=
  s.writeSlot lockSlot (if b then 1 else 0)

@[simp] theorem setHealthy_liq (b : Bool) (s : ContractState) :
    (setHealthy b s).storage liquidatedSlot = s.storage liquidatedSlot := by
  simp [setHealthy, healthSlot, liquidatedSlot, ContractState.writeSlot, ContractState.readSlot, ContractState.storage]

@[simp] theorem setLock_liq (b : Bool) (s : ContractState) :
    (setLock b s).storage liquidatedSlot = s.storage liquidatedSlot := by
  simp [setLock, lockSlot, liquidatedSlot, ContractState.writeSlot, ContractState.readSlot, ContractState.storage]

@[simp] theorem setHealthy_lock (b : Bool) (s : ContractState) :
    (setHealthy b s).storage lockSlot = s.storage lockSlot := by
  simp [setHealthy, healthSlot, lockSlot, ContractState.writeSlot, ContractState.readSlot, ContractState.storage]

/-! ## Buggy `take`: trade ⇒ transiently unhealthy, NO lock, final health check -/

def takeBuggy (adv : ContractState → ContractState) (s : ContractState) : ContractState :=
  let s1 := setHealthy false s          -- trade ⇒ seller transiently unhealthy
  let s2 := adv s1                       -- callback / reentrancy window (no lock held)
  setHealthy true s2                     -- close: require(isHealthy(seller))

/-- The bug: from a healthy, unlocked seller (`I` holds), a single reentrant
    `liquidate` in the window yields a PERMANENT liquidation, even though the
    seller is healthy again at the final check. -/
theorem buggy_admits_permanent_bad_debt :
    ∃ s : ContractState, I s ∧ liquidated (takeBuggy liquidate s) := by
  refine ⟨setHealthy true (setLock false defaultState), ?_, ?_⟩
  · left
    show (setHealthy true (setLock false defaultState)).storage healthSlot ≠ 0
    decide
  · simp only [liquidated, takeBuggy, liquidate, setHealthy, setLock,
      healthSlot, lockSlot, liquidatedSlot, ContractState.writeSlot]
    decide

/-! ## Fixed `take`: acquire lock, trade, window, health check, release -/

def takeLocked (adv : ContractState → ContractState) (s : ContractState) : ContractState :=
  let s0 := setLock true s               -- acquire the per-position lock
  let s1 := setHealthy false s0          -- trade (transiently unhealthy, but locked)
  let s2 := adv s1                        -- window: I holds here via the lock disjunct
  let s3 := setHealthy true s2            -- close: require(isHealthy(seller))
  setLock false s3                        -- release the lock

/-- Rely-guarantee safety: for ANY reentrant adversary that respects the lock,
    the locked `take` introduces no new liquidation — the `liquidated` slot is
    left exactly as it started. -/
theorem locked_take_no_new_liquidation
    (adv : ContractState → ContractState)
    (hAdv : ∀ v, locked v → (adv v).storage liquidatedSlot = v.storage liquidatedSlot)
    (s : ContractState) :
    (takeLocked adv s).storage liquidatedSlot = s.storage liquidatedSlot := by
  have hlock : locked (setHealthy false (setLock true s)) := by
    show (setHealthy false (setLock true s)).storage lockSlot ≠ 0
    have hval : (setHealthy false (setLock true s)).storage lockSlot = 1 := by
      simp [setHealthy, setLock, healthSlot, lockSlot, ContractState.writeSlot, ContractState.readSlot]
    rw [hval]; decide
  simp only [takeLocked, setHealthy_liq, setLock_liq, hAdv _ hlock]

/-- Rely-guarantee invariant preservation: the locked `take` preserves `I` for
    ANY adversary, because the final health check re-establishes the `healthy`
    disjunct unconditionally. -/
theorem locked_take_preserves_I (adv : ContractState → ContractState) (s : ContractState) :
    I (takeLocked adv s) := by
  left
  show (takeLocked adv s).storage healthSlot ≠ 0
  have hval : (takeLocked adv s).storage healthSlot = 1 := by
    simp [takeLocked, setLock, setHealthy, healthSlot, lockSlot, ContractState.writeSlot, ContractState.readSlot]
  rw [hval]; decide

/-- Concrete corollary: the lock blocks the real `liquidate` adversary, because
    `liquidate` discharges the rely condition (`liquidate_respects_lock`). -/
theorem locked_blocks_concrete_liquidation (s : ContractState) :
    (takeLocked liquidate s).storage liquidatedSlot = s.storage liquidatedSlot := by
  apply locked_take_no_new_liquidation
  intro v hv
  rw [liquidate_respects_lock hv]

/-! ## Wiring into the framework: a `ReentrancySpec` whose registry is `[liquidate]` -/

/-- The contract's reentrancy spec: the lock-as-disjunct invariant `I`, the
    entrypoint registry `[liquidate]`, and the single per-entrypoint obligation
    (here `liquidate_preserves_I`). The macro-emitted registry would supply the
    `entrypoints` list; the proof obligation is one lemma per entrypoint. -/
def spec : ReentrancySpec where
  Inv := I
  entrypoints := [liquidate]
  entrypoints_preserve := by
    intro f hf
    simp only [List.mem_singleton] at hf
    subst hf
    exact liquidate_preserves_I

/-- Framework payoff: ANY finite reentry schedule drawn from this contract's
    registered entrypoints preserves `I`. The whole adversarial interleaving
    space is discharged by the single obligation in `spec`. -/
theorem any_reentry_schedule_preserves_I
    (sched : List (ContractState → ContractState))
    (hsched : ∀ f, f ∈ sched → f ∈ spec.entrypoints) :
    Preserves I (runSeq sched) :=
  spec.schedule_preserves sched hsched

/-- Forward-compat payoff: the SAME spec, lifted into a multi-contract `System`,
    preserves the joint invariant against any cross-contract reentry schedule —
    no new per-contract proof. -/
theorem any_cross_contract_schedule_preserves_I (inScope : List Address)
    (steps : List (Address × (ContractState → ContractState)))
    (hsteps : ∀ p, p ∈ steps → p.2 ∈ spec.entrypoints) :
    Preserves (Isys I inScope) (runSeq (steps.map (fun p => lift p.1 p.2))) :=
  cross_contract_schedule_preserves spec inScope steps hsteps

/-! ## Call-boundary payoff: invariant safety through whole call programs

The same single `liquidate` obligation now covers the external-call boundary:
any adversary whose committed transitions are reentry schedules drawn from
this contract's registry preserves `I` at every externally opened window of
any `CallProgram`, and through the transaction commit/revert boundary. -/

open Compiler.CompilationModel.DenoteExternalCalls in
theorem callback_bounded_program_preserves_I
    {adversary : AdversaryModel}
    (hbound : CallbackBounded spec.entrypoints adversary)
    (prog : CallProgram α) (state : CallState) (hInv : I state.world) :
    I (denote prog adversary state).2.world :=
  hbound.denote_preserves spec prog state hInv

open Compiler.CompilationModel.DenoteExternalCalls in
theorem callback_bounded_transaction_preserves_I
    {adversary : AdversaryModel} {α : Type}
    (hbound : CallbackBounded spec.entrypoints adversary)
    (prog : CallProgram (TransactionResult α)) (state : CallState)
    (hInv : I state.world) :
    I (denoteTransaction prog adversary state).state.world :=
  hbound.transaction_preserves spec prog state hInv

end Contracts.ReentrancyRelyGuarantee
