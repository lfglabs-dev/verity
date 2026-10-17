import Compiler.SolidityImport.EntryPointInvariants

namespace Compiler.CompilationModel.SolidityImport.Transactions
open Denote

/-- Public calls may select a different adversarial oracle and transaction
context at every step. Only actual successful instrumentation results form
steps; a Solidity revert is represented by the exact FrameResult as usual. -/
inductive AdversarialEntryPointSequence (model : CompilationModel)
    (prepare : Verity.ContractState → Verity.ContractState → Prop)
    (allowed : DenoteOracle → Prop) :
    Verity.ContractState → Verity.ContractState → Prop where
  | empty (world) : AdversarialEntryPointSequence model prepare allowed world world
  | step (before prepared after : Verity.ContractState)
      (context : prepare before prepared) (oracle : DenoteOracle)
      (permitted : allowed oracle) (fn : FunctionSpec)
      (member : fn ∈ model.functions) (isPublic : fn.isInternal = false)
      (bindings : Env) (result : FrameResult)
      (executed : executeBody oracle (effectiveFields model) prepared bindings
        fn.body model.errors = .ok result)
      (tail : AdversarialEntryPointSequence model prepare allowed result.world after) :
      AdversarialEntryPointSequence model prepare allowed before after

/-- Universal per-entry-point obligations cover arbitrary finite oracle
choices, rather than silently fixing one adversary for a whole campaign.
Dispatch, ABI decoding and value transfer remain separate obligations. -/
theorem invariant_of_adversarial_entry_points (model : CompilationModel)
    (invariant : Verity.ContractState → Prop)
    (prepare : Verity.ContractState → Verity.ContractState → Prop)
    (allowed : DenoteOracle → Prop)
    (contextPreserves : ∀ before prepared, prepare before prepared →
      invariant before → invariant prepared)
    (preserved : ∀ oracle, allowed oracle →
      AllEntryPointsPreserve oracle model invariant)
    (before after : Verity.ContractState) (initial : invariant before)
    (sequence : AdversarialEntryPointSequence model prepare allowed before after) :
    invariant after := by
  induction sequence with
  | empty => exact initial
  | step before prepared after context oracle permitted fn member isPublic bindings result executed tail ih =>
      exact ih (preserved oracle permitted fn member isPublic prepared bindings result
        (contextPreserves before prepared context initial) executed)

/-- Every observed prefix may be concatenated with a later sequence without
fixing its length, context choices or oracle choices. -/
theorem adversarial_sequence_append (model : CompilationModel)
    (prepare : Verity.ContractState → Verity.ContractState → Prop)
    (allowed : DenoteOracle → Prop) (before middle after : Verity.ContractState)
    (first : AdversarialEntryPointSequence model prepare allowed before middle)
    (second : AdversarialEntryPointSequence model prepare allowed middle after) :
    AdversarialEntryPointSequence model prepare allowed before after := by
  induction first with
  | empty => exact second
  | step before prepared middle context oracle permitted fn member isPublic bindings result executed tail ih =>
      exact .step before prepared after context oracle permitted fn member isPublic
        bindings result executed (ih second)

end Compiler.CompilationModel.SolidityImport.Transactions
