import Verity.Core.Model.Denote

/-!
# Composable denotation for external calls

`Denote` deliberately maps raw EVM calls and linked external calls outside its
fragment.  This module supplies the missing call boundary without postulating
callee behaviour: an `AdversaryModel` is an ordinary parameter of every
denotation.

The model records the three call contexts separately.  A successful `call`
commits the adversary's state transition, a `staticcall` observes the response
but cannot change the caller state, and a successful `delegatecall` commits a
transition explicitly indexed by the delegate context.  Failure and revert
roll back to the pre-call state.  Gas charged by the adversary is capped by
both the requested allowance and the caller's remaining gas.
-/
namespace Compiler.CompilationModel.DenoteExternalCalls

open Compiler.CompilationModel
open Compiler.CompilationModel.Denote

/-- The EVM external-call opcode family. -/
inductive CallKind where
  | call
  | staticcall
  | delegatecall
  deriving DecidableEq, Repr

/-- A call site, including the data that distinguishes repeated and nested
calls. `siteId` is chosen by the denoting client and is the stable key supplied
to the adversary. -/
structure CallSite where
  siteId : Nat
  kind : CallKind
  target : Nat
  value : Nat := 0
  calldata : List Nat := []
  /-- Source-level linked name. Opcode-level sites leave this empty. -/
  name : String := ""
  /-- Number of returndata words expected by the deterministic source stub. -/
  returnArity : Nat := 0
  /-- Words used by source stubs but omitted from the observable calldata. -/
  stubPrefix : List Nat := []
  gas : Nat
  deriving Repr

/-- Finite returndata together with the external call's control result.
`failure` represents a zero success bit without a revert payload; `revert`
keeps the payload that EVM exposes through returndata. -/
inductive ExternalCallResult where
  | success (returndata : List Nat)
  | failure (returndata : List Nat)
  | revert (returndata : List Nat)
  deriving DecidableEq, Repr

instance : Inhabited ExternalCallResult := ⟨.success []⟩

namespace ExternalCallResult

def returndata : ExternalCallResult → List Nat
  | .success data | .failure data | .revert data => data

def succeeded : ExternalCallResult → Bool
  | .success _ => true
  | .failure _ | .revert _ => false

end ExternalCallResult

/-- The control component of an external-call result, with the returndata
projected away — what branching logic in callers actually inspects. -/
inductive CallControl where
  | success
  | failure
  | revert
  deriving DecidableEq, Repr

namespace ExternalCallResult

/-- Project the control component. -/
def control : ExternalCallResult → CallControl
  | .success _ => .success
  | .failure _ => .failure
  | .revert _ => .revert

/-- A result is exactly its control paired with its returndata. -/
theorem control_returndata_eta : ∀ (r : ExternalCallResult),
    r = match r.control with
      | .success => .success r.returndata
      | .failure => .failure r.returndata
      | .revert => .revert r.returndata
  | .success _ => rfl
  | .failure _ => rfl
  | .revert _ => rfl

/-- Two results agree iff their controls and returndata agree. -/
theorem ext_iff (r₁ r₂ : ExternalCallResult) :
    r₁ = r₂ ↔ r₁.control = r₂.control ∧ r₁.returndata = r₂.returndata := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨hc, hd⟩
    cases r₁ <;> cases r₂ <;>
      simp_all [control, returndata]

@[simp] theorem control_success (data : List Nat) :
    (ExternalCallResult.success data).control = .success := rfl
@[simp] theorem control_failure (data : List Nat) :
    (ExternalCallResult.failure data).control = .failure := rfl
@[simp] theorem control_revert (data : List Nat) :
    (ExternalCallResult.revert data).control = .revert := rfl

/-- `succeeded` is a control fact. -/
theorem succeeded_iff_control (r : ExternalCallResult) :
    r.succeeded = true ↔ r.control = .success := by
  cases r <;> simp [succeeded, control]

end ExternalCallResult

/-- The caller state threaded between call sites. -/
structure CallState where
  world : Verity.ContractState
  gasRemaining : Nat
  returndata : List Nat := []

/-- All adversarial choices are explicit parameters.  State evolution is a
`ContractState → ContractState` function selected per `CallSite`, as opposed
to an axiom.  The response and gas charge may depend on the pre-call state.
The call kind is part of the site, so the same target can have distinct
`call`, `staticcall`, and `delegatecall` behaviour. -/
structure AdversaryModel where
  stateTransition : CallSite → Verity.ContractState → Verity.ContractState
  result : CallSite → Verity.ContractState → ExternalCallResult
  gasUsed : CallSite → Verity.ContractState → Nat

namespace AdversaryModel

/-- The deterministic word used by the legacy executable linked-call plane. -/
def stubWord (name : String) (args : List Nat) : Nat :=
  Denote.wordNormalize <|
    if name = "echo" then
      match args with
      | [value] => value
      | _ => args.foldl (fun acc arg => Denote.wordNormalize (acc + arg)) name.length
    else
      args.foldl (fun acc arg => Denote.wordNormalize (acc + arg)) name.length

@[simp] theorem wordNormalize_stubWord (name : String) (args : List Nat) :
    Denote.wordNormalize (stubWord name args) = stubWord name args := by
  simp [stubWord, Denote.wordNormalize]

@[simp] theorem stubWord_modulus (name : String) (args : List Nat) :
    stubWord name args % Verity.Core.Uint256.modulus = stubWord name args := by
  simpa [Denote.wordNormalize] using wordNormalize_stubWord name args

/-- The no-reentry adversary matching the current executable linked-call stub.
It preserves caller state, fails only for the reserved name `"fail"`, returns
the deterministic stub word at the site's declared arity, and consumes no gas. -/
def stub : AdversaryModel where
  stateTransition := fun _ state => state
  result := fun site _ =>
    if site.name = "fail" then .failure []
    else .success
      (List.replicate site.returnArity (stubWord site.name (site.stubPrefix ++ site.calldata)))
  gasUsed := fun _ _ => 0

@[simp] theorem stub_stateTransition (site : CallSite) (state : Verity.ContractState) :
    stub.stateTransition site state = state := rfl

@[simp] theorem stub_gasUsed (site : CallSite) (state : Verity.ContractState) :
    stub.gasUsed site state = 0 := rfl

end AdversaryModel

/-- Observable produced at one call boundary. -/
structure CallObservation where
  result : ExternalCallResult
  gasUsed : Nat
  state : CallState

def chargedGas (available requested claimed : Nat) : Nat :=
  Nat.min available (Nat.min requested claimed)

/-- Denote one external call.  Only successful mutable calls commit an
adversarial transition.  Static calls always preserve the world, while
failure and revert implement caller-side rollback. -/
def denoteCall (adversary : AdversaryModel) (site : CallSite)
    (state : CallState) : CallObservation :=
  let response := adversary.result site state.world
  let charged := chargedGas state.gasRemaining site.gas
    (adversary.gasUsed site state.world)
  let nextWorld :=
    match site.kind, response with
    | .staticcall, _ => state.world
    | .call, .success _ | .delegatecall, .success _ =>
        adversary.stateTransition site state.world
    | .call, .failure _ | .call, .revert _
    | .delegatecall, .failure _ | .delegatecall, .revert _ => state.world
  { result := response
    gasUsed := charged
    state :=
      { world := nextWorld
        gasRemaining := state.gasRemaining - charged
        returndata := response.returndata } }

/-- A composable call program. `bind` supports sequential calls and permits
the continuation to construct a nested call site from the preceding result. -/
inductive CallProgram (α : Type) where
  | pure (value : α)
  | bind (site : CallSite) (next : CallObservation → CallProgram α)

def denote : CallProgram α → AdversaryModel → CallState → α × CallState
  | .pure value, _, state => (value, state)
  | .bind site next, adversary, state =>
      let observation := denoteCall adversary site state
      denote (next observation) adversary observation.state

def sequential (first second : CallSite) : CallProgram (ExternalCallResult × ExternalCallResult) :=
  .bind first fun firstResult =>
    .bind second fun secondResult =>
      .pure (firstResult.result, secondResult.result)

def nested (outer : CallSite) (inner : ExternalCallResult → CallSite) :
    CallProgram (ExternalCallResult × ExternalCallResult) :=
  .bind outer fun outerResult =>
    .bind (inner outerResult.result) fun innerResult =>
      .pure (outerResult.result, innerResult.result)

/-! ## Gas and call-kind laws -/

theorem chargedGas_le_available (available requested claimed : Nat) :
    chargedGas available requested claimed ≤ available := by
  exact Nat.min_le_left _ _

theorem denoteCall_gasRemaining (adversary : AdversaryModel) (site : CallSite)
    (state : CallState) :
    (denoteCall adversary site state).state.gasRemaining =
      state.gasRemaining - chargedGas state.gasRemaining site.gas
        (adversary.gasUsed site state.world) := rfl

theorem denoteCall_staticcall_world (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) (h : site.kind = .staticcall) :
    (denoteCall adversary site state).state.world = state.world := by
  simp [denoteCall, h]

theorem denoteCall_call_success_world (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) (data : List Nat)
    (hkind : site.kind = .call)
    (hresult : adversary.result site state.world = .success data) :
    (denoteCall adversary site state).state.world =
      adversary.stateTransition site state.world := by
  simp [denoteCall, hkind, hresult]

theorem denoteCall_delegatecall_success_world (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) (data : List Nat)
    (hkind : site.kind = .delegatecall)
    (hresult : adversary.result site state.world = .success data) :
    (denoteCall adversary site state).state.world =
      adversary.stateTransition site state.world := by
  simp [denoteCall, hkind, hresult]

theorem denoteCall_failure_world (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) (data : List Nat)
    (hkind : site.kind = .call ∨ site.kind = .delegatecall)
    (hresult : adversary.result site state.world = .failure data) :
    (denoteCall adversary site state).state.world = state.world := by
  rcases hkind with h | h <;> simp [denoteCall, h, hresult]

theorem denoteCall_revert_world (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) (data : List Nat)
    (hkind : site.kind = .call ∨ site.kind = .delegatecall)
    (hresult : adversary.result site state.world = .revert data) :
    (denoteCall adversary site state).state.world = state.world := by
  rcases hkind with h | h <;> simp [denoteCall, h, hresult]

/-! ## Composition laws -/

theorem denote_bind (adversary : AdversaryModel) (state : CallState)
    (site : CallSite) (next : CallObservation → CallProgram α) :
    denote (.bind site next) adversary state =
      let observation := denoteCall adversary site state
      denote (next observation) adversary observation.state := rfl

theorem denote_sequential (adversary : AdversaryModel) (state : CallState)
    (first second : CallSite) :
    denote (sequential first second) adversary state =
      let firstResult := denoteCall adversary first state
      let secondResult := denoteCall adversary second firstResult.state
      ((firstResult.result, secondResult.result), secondResult.state) := rfl

theorem denote_nested (adversary : AdversaryModel) (state : CallState)
    (outer : CallSite) (inner : ExternalCallResult → CallSite) :
    denote (nested outer inner) adversary state =
      let outerResult := denoteCall adversary outer state
      let innerResult := denoteCall adversary (inner outerResult.result) outerResult.state
      ((outerResult.result, innerResult.result), innerResult.state) := rfl

/-! ## Journaled denotation

`denoteCall` leaves no trace of the boundary crossing in the caller world.
The journaled variant additionally appends one `Verity.ExternalCall` entry to
`ContractState.calls` per call.  Two deliberate semantic choices:

* **The journal survives rollback.**  Failure and revert restore the caller
  world *except* the journal — otherwise reverted calls would be
  unobservable, and per-iteration reasoning over retrying loops (e.g. the
  MinFirst allocation loop) would be impossible.
* **The adversary cannot touch the journal.**  Even on a committed `call` /
  `delegatecall` success, the post-call journal is forced to
  `pre.calls ++ [entry]`, regardless of what `stateTransition` did to the
  `calls` field.  The journal is the caller's observation record, not
  adversary-controlled state.

`denoteCall` itself is unchanged, so every existing world/gas law holds
verbatim; the journaled lemmas below characterize the delta. -/

/-- Journal projections of the model-level call kinds and controls. -/
def CallKind.toJournal : CallKind → Verity.ExternalCallKind
  | .call => .call
  | .staticcall => .staticcall
  | .delegatecall => .delegatecall

def CallControl.toJournal : CallControl → Verity.ExternalCallControl
  | .success => .success
  | .failure => .failure
  | .revert => .revert

/-- The journal entry recorded for one call site and its observed result. -/
def journalEntry (site : CallSite) (result : ExternalCallResult) :
    Verity.ExternalCall :=
  { siteId := site.siteId
    kind := site.kind.toJournal
    target := site.target
    value := site.value
    calldata := site.calldata
    control := result.control.toJournal
    returndata := result.returndata
    name := site.name }

/-- Denote one external call and record it in the caller world's journal. -/
def denoteCallJournaled (adversary : AdversaryModel) (site : CallSite)
    (state : CallState) : CallObservation :=
  let observation := denoteCall adversary site state
  { observation with
    state :=
      { observation.state with
        world :=
          { observation.state.world with
            calls := state.world.calls ++ [journalEntry site observation.result] } } }

@[simp] theorem denoteCallJournaled_result (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) :
    (denoteCallJournaled adversary site state).result =
      (denoteCall adversary site state).result := rfl

@[simp] theorem denoteCallJournaled_gasUsed (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) :
    (denoteCallJournaled adversary site state).gasUsed =
      (denoteCall adversary site state).gasUsed := rfl

@[simp] theorem denoteCallJournaled_gasRemaining (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) :
    (denoteCallJournaled adversary site state).state.gasRemaining =
      (denoteCall adversary site state).state.gasRemaining := rfl

@[simp] theorem denoteCallJournaled_returndata (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) :
    (denoteCallJournaled adversary site state).state.returndata =
      (denoteCall adversary site state).state.returndata := rfl

/-- The journaled world is the plain-denotation world with exactly one entry
appended to the journal — the adversary's committed transition cannot leak
into `calls`. -/
theorem denoteCallJournaled_world (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) :
    (denoteCallJournaled adversary site state).state.world =
      { (denoteCall adversary site state).state.world with
        calls := state.world.calls ++
          [journalEntry site (denoteCall adversary site state).result] } := rfl

/-- Append law: one call appends exactly one journal entry. -/
@[simp] theorem denoteCallJournaled_calls (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) :
    (denoteCallJournaled adversary site state).state.world.calls =
      state.world.calls ++
        [journalEntry site (denoteCall adversary site state).result] := rfl

/-- Rollback preserves the journal: a failed or reverted mutable call
restores the caller world except the appended entry. -/
theorem denoteCallJournaled_rollback_world (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) (data : List Nat)
    (hkind : site.kind = .call ∨ site.kind = .delegatecall)
    (hresult : adversary.result site state.world = .failure data ∨
      adversary.result site state.world = .revert data) :
    (denoteCallJournaled adversary site state).state.world =
      { state.world with
        calls := state.world.calls ++
          [journalEntry site (denoteCall adversary site state).result] } := by
  rw [denoteCallJournaled_world]
  rcases hresult with h | h
  · rw [denoteCall_failure_world adversary site state data hkind h]
  · rw [denoteCall_revert_world adversary site state data hkind h]

/-- A static call preserves the caller world except the appended entry. -/
theorem denoteCallJournaled_staticcall_world (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) (h : site.kind = .staticcall) :
    (denoteCallJournaled adversary site state).state.world =
      { state.world with
        calls := state.world.calls ++
          [journalEntry site (denoteCall adversary site state).result] } := by
  rw [denoteCallJournaled_world,
    denoteCall_staticcall_world adversary site state h]

/-- Journaled denotation of a call program: every boundary crossing along the
program is recorded, in order. -/
def denoteJournaled : CallProgram α → AdversaryModel → CallState → α × CallState
  | .pure value, _, state => (value, state)
  | .bind site next, adversary, state =>
      let observation := denoteCallJournaled adversary site state
      denoteJournaled (next observation) adversary observation.state

@[simp] theorem denoteJournaled_pure (adversary : AdversaryModel)
    (state : CallState) (value : α) :
    denoteJournaled (.pure value) adversary state = (value, state) := rfl

theorem denoteJournaled_bind (adversary : AdversaryModel) (state : CallState)
    (site : CallSite) (next : CallObservation → CallProgram α) :
    denoteJournaled (.bind site next) adversary state =
      let observation := denoteCallJournaled adversary site state
      denoteJournaled (next observation) adversary observation.state := rfl

/-- Monotonicity: a program only ever extends the journal. The witness is the
ordered trace of the calls the program performed. -/
theorem denoteJournaled_calls_monotone (program : CallProgram α)
    (adversary : AdversaryModel) (state : CallState) :
    ∃ trace, (denoteJournaled program adversary state).2.world.calls =
      state.world.calls ++ trace := by
  induction program generalizing state with
  | pure value => exact ⟨[], by simp⟩
  | bind site next ih =>
      obtain ⟨trace, htrace⟩ :=
        ih (denoteCallJournaled adversary site state) (denoteCallJournaled adversary site state).state
      exact ⟨journalEntry site (denoteCall adversary site state).result :: trace, by
        simpa [denoteJournaled_bind, denoteCallJournaled_calls] using htrace⟩

/-! ## Bridge to the existing non-call denotation -/

/-- Embed the existing statement denotation as the non-call leaf of the
composable model.  The gas component is deliberately unchanged because the
legacy `Denote` fragment has no gas semantics. -/
def denoteNonCall (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (gasRemaining : Nat) (stmts : List Stmt) :
    StmtOutcome × Nat :=
  (execStmtList oracle fields state stmts, gasRemaining)

/-- Definitional agreement with `Denote` on the fragment that contains no
external call constructors.  Call-freedom remains the established
`SupportedFunction`/surface predicate at clients of this module; the equality
itself needs no semantic assumption because `denoteNonCall` delegates exactly
to the canonical denotation. -/
theorem denotation_eq (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (gasRemaining : Nat) (stmts : List Stmt) :
    (denoteNonCall oracle fields state gasRemaining stmts).1 =
      execStmtList oracle fields state stmts := rfl

end Compiler.CompilationModel.DenoteExternalCalls
