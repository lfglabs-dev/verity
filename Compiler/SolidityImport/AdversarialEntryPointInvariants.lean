import Compiler.SolidityImport.EntryPointInvariants
import Verity.Core.Model.DenoteByteExternalCalls

namespace Compiler.CompilationModel.SolidityImport.Transactions
open Denote

/-- Public calls may select a different adversarial oracle and transaction
context at every step. Only actual successful instrumentation results form
steps; a Solidity revert is represented by the exact FrameResult as usual. -/
inductive AdversarialEntryPointSequence (model : CompilationModel)
    (immutables : String → Verity.Core.Uint256)
    (prepare : Verity.ContractState → Verity.ContractState → Prop)
    (allowed : DenoteOracle → Prop) :
    Verity.ContractState → Verity.ContractState → Prop where
  | empty (world) : AdversarialEntryPointSequence model immutables prepare allowed world world
  | step (before prepared after : Verity.ContractState)
      (context : prepare before prepared) (oracle : DenoteOracle)
      (permitted : allowed oracle) (fn : FunctionSpec)
      (member : fn ∈ model.functions) (isPublic : fn.isInternal = false)
      (bindings : Env) (result : FrameResult)
      (executed : executeBody oracle (effectiveFields model) prepared bindings
        fn.body model.errors (immutables := immutables) = .ok result)
      (tail : AdversarialEntryPointSequence model immutables prepare allowed result.world after) :
      AdversarialEntryPointSequence model immutables prepare allowed before after

/-- Universal per-entry-point obligations cover arbitrary finite oracle
choices, rather than silently fixing one adversary for a whole campaign.
The immutables are the deployment's, the same at every step.
Dispatch, ABI decoding and value transfer remain separate obligations. -/
theorem invariant_of_adversarial_entry_points (model : CompilationModel)
    (immutables : String → Verity.Core.Uint256)
    (invariant : Verity.ContractState → Prop)
    (prepare : Verity.ContractState → Verity.ContractState → Prop)
    (allowed : DenoteOracle → Prop)
    (contextPreserves : ∀ before prepared, prepare before prepared →
      invariant before → invariant prepared)
    (preserved : ∀ oracle, allowed oracle →
      AllEntryPointsPreserve oracle model invariant immutables)
    (before after : Verity.ContractState) (initial : invariant before)
    (sequence : AdversarialEntryPointSequence model immutables prepare allowed before after) :
    invariant after := by
  induction sequence with
  | empty => exact initial
  | step before prepared after context oracle permitted fn member isPublic bindings result executed tail ih =>
      exact ih (preserved oracle permitted fn member isPublic prepared bindings result
        (contextPreserves before prepared context initial) executed)

/-- Every observed prefix may be concatenated with a later sequence without
fixing its length, context choices or oracle choices. -/
theorem adversarial_sequence_append (model : CompilationModel)
    (immutables : String → Verity.Core.Uint256)
    (prepare : Verity.ContractState → Verity.ContractState → Prop)
    (allowed : DenoteOracle → Prop) (before middle after : Verity.ContractState)
    (first : AdversarialEntryPointSequence model immutables prepare allowed before middle)
    (second : AdversarialEntryPointSequence model immutables prepare allowed middle after) :
    AdversarialEntryPointSequence model immutables prepare allowed before after := by
  induction first with
  | empty => exact second
  | step before prepared middle context oracle permitted fn member isPublic bindings result executed tail ih =>
      exact .step before prepared after context oracle permitted fn member isPublic
        bindings result executed (ih second)

/-- `AdversarialEntryPointSequence` where each step also chooses its callees' behaviour, among
the byte-call environments `callees` allows. In `AdversarialEntryPointSequence` a successful
step can make no external call (`executeBody`'s default environment has no adversary), so a
sequence invariant over a contract that calls out needs this form. Each step is a call a
transaction can make: its bindings decode the prepared world's calldata (`DecodedCall`).
`allowed` admits each step by its oracle, function and prepared world: one fixed oracle for a
whole sequence (`fun o _ _ => o = oracle`), or callers and calldata from a given set. -/
inductive CalleeEntryPointSequence (model : CompilationModel)
    (immutables : String → Verity.Core.Uint256)
    (prepare : Verity.ContractState → Verity.ContractState → Prop)
    (allowed : DenoteOracle → FunctionSpec → Verity.ContractState → Prop)
    (callees : ByteCallEnvironment → Prop) :
    Verity.ContractState → Verity.ContractState → Prop where
  | empty (world) : CalleeEntryPointSequence model immutables prepare allowed callees world world
  | step (before prepared after : Verity.ContractState)
      (context : prepare before prepared) (oracle : DenoteOracle)
      (calls : ByteCallEnvironment) (admitted : callees calls)
      (fn : FunctionSpec) (member : fn ∈ model.functions) (isPublic : fn.isInternal = false)
      (permitted : allowed oracle fn prepared)
      (bindings : Env) (decoded : DecodedCall fn prepared bindings) (result : FrameResult)
      (executed : executeBody oracle (effectiveFields model) prepared bindings
        fn.body model.errors (byteCalls := calls) (immutables := immutables) = .ok result)
      (tail : CalleeEntryPointSequence model immutables prepare allowed callees
        result.world after) :
      CalleeEntryPointSequence model immutables prepare allowed callees before after

/-- Per-entry-point obligations, universal over allowed oracles and allowed callees, give the
invariant after every finite callee-choosing sequence. -/
theorem invariant_of_callee_entry_points (model : CompilationModel)
    (immutables : String → Verity.Core.Uint256)
    (invariant : Verity.ContractState → Prop)
    (prepare : Verity.ContractState → Verity.ContractState → Prop)
    (allowed : DenoteOracle → FunctionSpec → Verity.ContractState → Prop)
    (callees : ByteCallEnvironment → Prop)
    (contextPreserves : ∀ before prepared, prepare before prepared →
      invariant before → invariant prepared)
    (preserved : ∀ oracle calls, callees calls →
      AllEntryPointsPreserveWith oracle calls model invariant immutables (allowed oracle))
    (before after : Verity.ContractState) (initial : invariant before)
    (sequence : CalleeEntryPointSequence model immutables prepare allowed callees before after) :
    invariant after := by
  induction sequence with
  | empty => exact initial
  | step before prepared after context oracle calls admitted fn member isPublic permitted
      bindings decoded result executed tail ih =>
      exact ih (preserved oracle calls admitted fn member isPublic prepared bindings result
        permitted decoded (contextPreserves before prepared context initial) executed)

/-- Callee-choosing sequences concatenate. -/
theorem callee_sequence_append (model : CompilationModel)
    (immutables : String → Verity.Core.Uint256)
    (prepare : Verity.ContractState → Verity.ContractState → Prop)
    (allowed : DenoteOracle → FunctionSpec → Verity.ContractState → Prop)
    (callees : ByteCallEnvironment → Prop)
    (before middle after : Verity.ContractState)
    (first : CalleeEntryPointSequence model immutables prepare allowed callees before middle)
    (second : CalleeEntryPointSequence model immutables prepare allowed callees middle after) :
    CalleeEntryPointSequence model immutables prepare allowed callees before after := by
  induction first with
  | empty => exact second
  | step before prepared middle context oracle calls admitted fn member isPublic permitted
      bindings decoded result executed tail ih =>
      exact .step before prepared after context oracle calls admitted fn member isPublic
        permitted bindings decoded result executed (ih second)

/-- Nested call-frame sequence within an active transaction (`executeFrameBody`, preserving
transaction-scoped transient storage across reentrant callbacks). -/
inductive CalleeFrameEntryPointSequence (model : CompilationModel)
    (immutables : String → Verity.Core.Uint256)
    (prepare : Verity.ContractState → Verity.ContractState → Prop)
    (allowed : DenoteOracle → FunctionSpec → Verity.ContractState → Prop)
    (callees : ByteCallEnvironment → Prop) :
    Verity.ContractState → Verity.ContractState → Prop where
  | empty (world) : CalleeFrameEntryPointSequence model immutables prepare allowed callees world world
  | step (before prepared after : Verity.ContractState)
      (context : prepare before prepared) (oracle : DenoteOracle)
      (calls : ByteCallEnvironment) (admitted : callees calls)
      (fn : FunctionSpec) (member : fn ∈ model.functions) (isPublic : fn.isInternal = false)
      (permitted : allowed oracle fn prepared)
      (bindings : Env) (decoded : DecodedCall fn prepared bindings) (result : FrameResult)
      (executed : executeFrameBody oracle (effectiveFields model) prepared bindings
        fn.body model.errors (byteCalls := calls) (immutables := immutables) = .ok result)
      (tail : CalleeFrameEntryPointSequence model immutables prepare allowed callees
        result.world after) :
      CalleeFrameEntryPointSequence model immutables prepare allowed callees before after

/-- Per-entry-point nested-frame obligations lift to `CalleeFrameEntryPointSequence`. -/
theorem invariant_of_callee_frame_entry_points (model : CompilationModel)
    (immutables : String → Verity.Core.Uint256)
    (invariant : Verity.ContractState → Prop)
    (prepare : Verity.ContractState → Verity.ContractState → Prop)
    (allowed : DenoteOracle → FunctionSpec → Verity.ContractState → Prop)
    (callees : ByteCallEnvironment → Prop)
    (contextPreserves : ∀ before prepared, prepare before prepared →
      invariant before → invariant prepared)
    (preserved : ∀ oracle calls, callees calls →
      AllEntryPointsPreserveFrameWith oracle calls model invariant immutables (allowed oracle))
    (before after : Verity.ContractState) (initial : invariant before)
    (sequence : CalleeFrameEntryPointSequence model immutables prepare allowed callees before after) :
    invariant after := by
  induction sequence with
  | empty => exact initial
  | step before prepared after context oracle calls admitted fn member isPublic permitted
      bindings decoded result executed tail ih =>
      exact ih (preserved oracle calls admitted fn member isPublic prepared bindings result
        permitted decoded (contextPreserves before prepared context initial) executed)

/-- The contract's own storage: every key but other accounts' slots. -/
def OwnStorageKey (key : Verity.StorageKey) : Prop := ∀ owner slot, key ≠ .contractSlot owner slot

/-- Callees that may call back into the contract, at most `depth` levels deep. At depth 0 they
answer as `base` allows. At depth `n + 1`, a successful answer's world is the request world after
a nested-frame callee-choosing sequence of the contract's own entry points (`executeFrameBody`,
preserving transaction-scoped transient storage across callbacks as on the EVM, each call
prepared from the world it starts in by `nested`, its own callees at depth `n`): the caller's
frame restored (`commitCalleeWorld`) and the contract's storage (including transient storage)
as the sequence left it. Other accounts are the callee's to change. A callee that does not call
back is the empty sequence. -/
def ReentrantCallees (model : CompilationModel) (immutables : String → Verity.Core.Uint256)
    (nested : Verity.ContractState → Verity.ContractState → Prop)
    (allowed : DenoteOracle → FunctionSpec → Verity.ContractState → Prop)
    (base : ByteCallEnvironment → Prop) : Nat → ByteCallEnvironment → Prop
  | 0 => base
  | depth + 1 => fun calls =>
      ∀ adversary, calls.adversary = some adversary →
        ∀ request world after data touched,
          adversary.respond request world = .success after data touched →
            ∃ reached, CalleeFrameEntryPointSequence model immutables nested allowed
                (ReentrantCallees model immutables nested allowed base depth) world reached ∧
              DenoteByteExternalCalls.commitCalleeWorld world after = after ∧
              (∀ key, OwnStorageKey key → after.storageWords key = reached.storageWords key) ∧
              after.storageArray = reached.storageArray

/-- An invariant of the contract's own storage survives a callee that calls back `depth + 1`
levels deep, from any world where it holds, when the entry points keep it with callees `depth`
levels deep in nested frames (`AllEntryPointsPreserveFrameWith`) and every nested call's
preparation keeps it. -/
theorem reentrant_answer_preserves (model : CompilationModel)
    (immutables : String → Verity.Core.Uint256)
    (nested : Verity.ContractState → Verity.ContractState → Prop)
    (allowed : DenoteOracle → FunctionSpec → Verity.ContractState → Prop)
    (base : ByteCallEnvironment → Prop) (invariant : Verity.ContractState → Prop) (depth : Nat)
    (storageOnly : ∀ world world', (∀ key, OwnStorageKey key →
        world'.storageWords key = world.storageWords key) →
      world'.storageArray = world.storageArray → invariant world → invariant world')
    (nestedPreserves : ∀ before prepared, nested before prepared →
      invariant before → invariant prepared)
    (preserved : ∀ oracle calls, ReentrantCallees model immutables nested allowed base depth calls →
      AllEntryPointsPreserveFrameWith oracle calls model invariant immutables (allowed oracle))
    (calls : ByteCallEnvironment)
    (reentrant : ReentrantCallees model immutables nested allowed base (depth + 1) calls)
    (adversary : ByteExternalCall.Adversary Verity.ContractState Verity.StorageKey)
    (configured : calls.adversary = some adversary) (request : ByteExternalCall.Request)
    (world after : Verity.ContractState) (data : List UInt8) (touched : List Verity.StorageKey)
    (answered : adversary.respond request world = .success after data touched)
    (initial : invariant world) : invariant after := by
  obtain ⟨reached, sequence, _, storage, arrays⟩ :=
    reentrant adversary configured request world after data touched answered
  have kept : invariant reached :=
    invariant_of_callee_frame_entry_points model immutables invariant nested allowed _
      nestedPreserves preserved world reached initial sequence
  exact storageOnly reached after storage arrays kept

end Compiler.CompilationModel.SolidityImport.Transactions
