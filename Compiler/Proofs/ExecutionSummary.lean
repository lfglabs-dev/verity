import Compiler.Proofs.IRGeneration.IRRuntimeTypes

namespace Compiler.Proofs

open Compiler.Proofs.IRGeneration

/-!
Backend-neutral, typed execution summaries.

This is deliberately a projection API rather than a new semantics.  Backends
may expose their existing result records through `RawSummary`; consumers get a
single typed outcome and observable-state shape.  Failed executions carrying a
return value are rejected, so adapters cannot silently reinterpret an
inconsistent backend result.
-/

/-- The externally visible outcome of one contract execution. -/
inductive ExecutionOutcome (α : Type) where
  | returned (value : Option α)
  | reverted
  deriving DecidableEq, Repr

/-- Observable state shared by the source, IR, and backend result layers. -/
structure ExecutionObservables (StorageSlot StorageWord Event : Type) where
  storage : StorageSlot → StorageWord
  events : List Event

/-- A typed outcome paired with the observable post-state. -/
structure ExecutionSummary
    (ReturnValue StorageSlot StorageWord Event : Type) where
  outcome : ExecutionOutcome ReturnValue
  observables : ExecutionObservables StorageSlot StorageWord Event

/-- Minimal untyped result view implemented by existing execution backends. -/
structure RawSummary
    (ReturnValue StorageSlot StorageWord Event : Type) where
  success : Bool
  returnValue : Option ReturnValue
  storage : StorageSlot → StorageWord
  events : List Event

/-- Checked projection from an existing backend result.

The projection is fail-closed: a backend failure with a return value has no
typed summary.  Successful results preserve optional return values exactly.
-/
def RawSummary.toExecutionSummary? {ReturnValue StorageSlot StorageWord Event : Type}
    (raw : RawSummary ReturnValue StorageSlot StorageWord Event) :
    Option (ExecutionSummary ReturnValue StorageSlot StorageWord Event) :=
  if raw.success then
    some {
      outcome := .returned raw.returnValue
      observables := { storage := raw.storage, events := raw.events } }
  else
    match raw.returnValue with
    | none =>
        some {
          outcome := .reverted
          observables := { storage := raw.storage, events := raw.events } }
    | some _ => none

/-- A backend transition retains its typed pre-state alongside the checked
observable summary.  The state type is intentionally backend-selected. -/
structure ExecutionTransition
    (State ReturnValue StorageSlot StorageWord Event : Type) where
  initial : State
  summary : ExecutionSummary ReturnValue StorageSlot StorageWord Event

@[simp] theorem RawSummary.toExecutionSummary?_success
    {ReturnValue StorageSlot StorageWord Event : Type}
    (returnValue : Option ReturnValue)
    (storage : StorageSlot → StorageWord)
    (events : List Event) :
    (RawSummary.mk true returnValue storage events).toExecutionSummary? =
      some {
        outcome := .returned returnValue
        observables := { storage := storage, events := events } } := by
  rfl

@[simp] theorem RawSummary.toExecutionSummary?_revert
    {ReturnValue StorageSlot StorageWord Event : Type}
    (storage : StorageSlot → StorageWord)
    (events : List Event) :
    (RawSummary.mk false (none : Option ReturnValue) storage events).toExecutionSummary? =
      some {
        outcome := (ExecutionOutcome.reverted : ExecutionOutcome ReturnValue)
        observables := { storage := storage, events := events } } := by
  rfl

/-- Explicit fail-closed theorem for inconsistent failed results. -/
@[simp] theorem RawSummary.toExecutionSummary?_failed_with_return
    {ReturnValue StorageSlot StorageWord Event : Type}
    (value : ReturnValue)
    (storage : StorageSlot → StorageWord)
    (events : List Event) :
    (RawSummary.mk false (some value) storage events).toExecutionSummary? = none := by
  rfl

/-- Adequacy of the checked projection: every admitted summary preserves the
backend success bit, return value, storage, and events exactly. -/
theorem RawSummary.toExecutionSummary?_adequate
    {ReturnValue StorageSlot StorageWord Event : Type}
    {raw : RawSummary ReturnValue StorageSlot StorageWord Event}
    {summary : ExecutionSummary ReturnValue StorageSlot StorageWord Event}
    (h : raw.toExecutionSummary? = some summary) :
    summary.observables.storage = raw.storage ∧
    summary.observables.events = raw.events ∧
    (raw.success = true ∧ summary.outcome = .returned raw.returnValue ∨
      raw.success = false ∧ raw.returnValue = none ∧ summary.outcome = .reverted) := by
  unfold RawSummary.toExecutionSummary? at h
  by_cases hs : raw.success = true
  · rw [if_pos hs] at h
    injection h with hsummary
    subst summary
    simp [hs]
  · have hf : raw.success = false := Bool.eq_false_of_not_eq_true hs
    rw [if_neg hs] at h
    cases hr : raw.returnValue with
    | none =>
        rw [hr] at h
        injection h with hsummary
        subst summary
        simp [hf]
    | some value =>
        rw [hr] at h
        contradiction

/-- Existing IR results expose the common raw-summary interface definitionally. -/
def RawSummary.ofIRResult (result : IRResult) :
    RawSummary Nat IRStorageSlot IRStorageWord (List Nat) :=
  { success := result.success
    returnValue := result.returnValue
    storage := result.finalStorage
    events := result.events }

end Compiler.Proofs
