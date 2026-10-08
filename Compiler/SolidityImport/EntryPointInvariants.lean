import Compiler.SolidityImport.Transactions

namespace Compiler.CompilationModel.SolidityImport.Transactions
open Denote

/-- Every observed reverting frame rolls back to the supplied initial world.
Unclassified interpreter failures remain errors and cannot inhabit this premise. -/
theorem finishFrame_failed_world (initial : Verity.ContractState)
    (outcome : StmtOutcome) (result : FrameResult)
    (observed : finishFrame initial outcome = .ok result)
    (failed : result.success = false) : result.world = initial := by
  cases outcome with
  | «continue» state => simp [finishFrame] at observed
  | stop state =>
      by_cases stopped : state.observedStop
      · simp [finishFrame, stopped] at observed
        cases observed
        cases failed
      · cases words : state.observedReturnWords <;> simp [finishFrame, stopped, words] at observed
        cases observed
        cases failed
  | «return» value state =>
      simp only [finishFrame, Except.ok.injEq] at observed
      cases observed
      cases failed
  | revert => simp [finishFrame] at observed
  | revertWithData bytes =>
      simp only [finishFrame, Except.ok.injEq] at observed
      cases observed
      rfl

/-- The rollback point includes the transaction-local reset, whose invariant
preservation is an explicit obligation rather than an implicit assumption. -/
theorem executeBody_failed_world (oracle : DenoteOracle) (fields : List Field)
    (before : Verity.ContractState) (bindings : Env) (body : List Stmt)
    (errors : List ErrorDef) (result : FrameResult)
    (executed : executeBody oracle fields before bindings body errors = .ok result)
    (failed : result.success = false) : result.world = beginTransaction before := by
  exact finishFrame_failed_world (beginTransaction before) _ result executed failed

/-- One obligation for every public entry point. This includes successful and
rich-reverting frames and the transaction-local reset performed by executeBody.
ABI decoding, dispatch, value transfer, and environment installation are not
claimed here: arguments and the initial world are explicit. -/
def AllEntryPointsPreserve (oracle : DenoteOracle) (model : CompilationModel)
    (invariant : Verity.ContractState → Prop) : Prop :=
  ∀ fn ∈ model.functions, fn.isInternal = false →
    ∀ before bindings result,
      invariant before →
      executeBody oracle (effectiveFields model) before bindings fn.body model.errors = .ok result →
      invariant result.world

/-- It is enough to prove successful calls preserve the invariant, provided
frame initialization preserves it too. Reverting calls follow by actual rollback. -/
theorem all_entry_points_preserve_of_success (oracle : DenoteOracle)
    (model : CompilationModel) (invariant : Verity.ContractState → Prop)
    (resetPreserves : ∀ world, invariant world → invariant (beginTransaction world))
    (successPreserves : ∀ fn ∈ model.functions, fn.isInternal = false →
      ∀ before bindings result, invariant before →
        executeBody oracle (effectiveFields model) before bindings fn.body model.errors = .ok result →
        result.success = true → invariant result.world) :
    AllEntryPointsPreserve oracle model invariant := by
  intro fn member isPublic before bindings result initial executed
  cases success : result.success with
  | false =>
      rw [executeBody_failed_world oracle (effectiveFields model) before bindings
        fn.body model.errors result executed success]
      exact resetPreserves before initial
  | true => exact successPreserves fn member isPublic before bindings result initial executed success

/-- A sequence consists only of actual public model execution steps. Instrument
errors have no constructor and cannot be mistaken for Solidity reverts. -/
inductive EntryPointSequence (oracle : DenoteOracle) (model : CompilationModel) :
    Verity.ContractState → Verity.ContractState → Prop where
  | empty (world) : EntryPointSequence oracle model world world
  | step (before after : Verity.ContractState) (fn : FunctionSpec)
      (member : fn ∈ model.functions) (isPublic : fn.isInternal = false)
      (bindings : Env) (result : FrameResult)
      (executed : executeBody oracle (effectiveFields model) before bindings fn.body model.errors = .ok result)
      (tail : EntryPointSequence oracle model result.world after) :
      EntryPointSequence oracle model before after

/-- Per-entry-point obligations lift to arbitrary finite call sequences. -/
theorem invariant_of_all_entry_points (oracle : DenoteOracle) (model : CompilationModel)
    (invariant : Verity.ContractState → Prop)
    (preserved : AllEntryPointsPreserve oracle model invariant)
    (before after : Verity.ContractState)
    (initial : invariant before)
    (sequence : EntryPointSequence oracle model before after) : invariant after := by
  induction sequence with
  | empty => exact initial
  | step before after fn member isPublic bindings result executed tail ih =>
      exact ih (preserved fn member isPublic before bindings result initial executed)

/-- Environment preparation is explicit and may vary sender, block context,
or other permitted resources. Its invariant obligation is separate from the
contract's own entry-point obligations. -/
inductive ContextualEntryPointSequence (oracle : DenoteOracle) (model : CompilationModel)
    (prepare : Verity.ContractState → Verity.ContractState → Prop) :
    Verity.ContractState → Verity.ContractState → Prop where
  | empty (world) : ContextualEntryPointSequence oracle model prepare world world
  | step (before prepared after : Verity.ContractState)
      (context : prepare before prepared) (fn : FunctionSpec)
      (member : fn ∈ model.functions) (isPublic : fn.isInternal = false)
      (bindings : Env) (result : FrameResult)
      (executed : executeBody oracle (effectiveFields model) prepared bindings fn.body model.errors = .ok result)
      (tail : ContextualEntryPointSequence oracle model prepare result.world after) :
      ContextualEntryPointSequence oracle model prepare before after

theorem invariant_of_contextual_entry_points (oracle : DenoteOracle)
    (model : CompilationModel) (invariant : Verity.ContractState → Prop)
    (prepare : Verity.ContractState → Verity.ContractState → Prop)
    (contextPreserves : ∀ before prepared, prepare before prepared →
      invariant before → invariant prepared)
    (preserved : AllEntryPointsPreserve oracle model invariant)
    (before after : Verity.ContractState) (initial : invariant before)
    (sequence : ContextualEntryPointSequence oracle model prepare before after) :
    invariant after := by
  induction sequence with
  | empty => exact initial
  | step before prepared after context fn member isPublic bindings result executed tail ih =>
      exact ih (preserved fn member isPublic prepared bindings result
        (contextPreserves before prepared context initial) executed)

end Compiler.CompilationModel.SolidityImport.Transactions
