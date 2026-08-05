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

namespace ExternalCallResult

def returndata : ExternalCallResult → List Nat
  | .success data | .failure data | .revert data => data

def succeeded : ExternalCallResult → Bool
  | .success _ => true
  | .failure _ | .revert _ => false

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
