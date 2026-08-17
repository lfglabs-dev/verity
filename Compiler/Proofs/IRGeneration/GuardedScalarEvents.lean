import Compiler.Proofs.IRGeneration.GuardedContract

/-!
# Guarded whole-contract event preservation (`compile_preserves_semantics_guarded_with_scalar_events`)

The guarded whole-contract theorem (#2314–#2317) concludes
`sourceResultMatchesIRResult`, whose fourth conjunct is the final observable
event equality `encodeEvents source.events = ir.events` — but its support
witness (`SupportedSpecGuarded`) uses the event-excluding
`SupportedBodyInterface`, so no event-carrying instance of the guarded family
existed.  Conversely, the scalar-event whole-contract theorem
(`compile_preserves_semantics_with_scalar_events`, #2000 lane) closes that
equality end-to-end but speaks about the plain, unguarded source semantics.

This module composes the two merged bricks: on the scalar-event fragment
every supported function is lock-free (`noNonReentrant`), so the guarded
source semantics collapses to the plain one and the scalar-event theorem
transports to the guarded pipeline's characterization.  The result is the
final-result event-preservation statement for `interpretGuardedContract` —
no intermediate-state detour, no new semantic assumption.

Scope boundary (unchanged): functions that carry a `nonreentrant(lock)`
annotation *and* emit events remain outside the proven fragment; admitting
them needs the event bridge inside the guarded per-function pipeline, a
fragment widening rather than a composition.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration.Contract

/-- The guarded per-function choice is the plain semantics on lock-free
functions. -/
theorem guardedFunctionChoice_eq_of_none (model : CompilationModel)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (fn : FunctionSpec) (h : fn.nonReentrantLock = none) :
    guardedFunctionChoice model tx initialWorld fn =
      SourceSemantics.interpretFunction model fn tx initialWorld := by
  unfold guardedFunctionChoice
  rw [h]

/-- On a contract whose selector-dispatched functions are all lock-free, the
guarded source contract semantics is the plain source contract semantics. -/
theorem interpretGuardedContract_eq_of_lock_free (model : CompilationModel)
    (selectors : List Nat) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hlockfree : ∀ fn ∈ selectorDispatchedFunctions model,
      fn.nonReentrantLock = none) :
    interpretGuardedContract model selectors tx initialWorld =
      sourceContractSemantics model selectors tx initialWorld := by
  unfold interpretGuardedContract interpretContractWith
    sourceContractSemantics SourceSemantics.interpretContract
  cases hfind : SourceSemantics.findFunctionBySelector model selectors
      tx.functionSelector with
  | none => rfl
  | some fn =>
      have hfn : fn ∈ selectorDispatchedFunctions model :=
        SourceSemantics.findFunctionBySelector_mem_selectorDispatchedFunctions
          hfind
      simp only [guardedFunctionChoice, hlockfree fn hfn]

/-- Every scalar-event-supported dispatch target is lock-free. -/
theorem lock_free_of_supportedSpecWithScalarEvents
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors) :
    ∀ fn ∈ selectorDispatchedFunctions model, fn.nonReentrantLock = none :=
  fun _fn hfn =>
    (hSupported.supportedFunctionOfSelectorDispatched hfn).noNonReentrant

/-- Guarded whole-contract event preservation on the scalar-event fragment:
the guarded source semantics of a scalar-event-supported contract matches the
compiled IR's final result — including the observable event equality
`encodeEvents source.events = ir.events` — end to end. -/
theorem compile_preserves_semantics_guarded_with_scalar_events
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hfuelPos : 0 < hSupported.helperFuel)
    (hhelperFree :
      ∀ fn, fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeNonEventStepInterface
          (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hstmtDisjoint :
      ∀ fn, fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint { ir with internalFunctions := [] }
          (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretGuardedContract model selectors tx initialWorld)
      (interpretIR ir tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rw [interpretGuardedContract_eq_of_lock_free model selectors tx initialWorld
    (lock_free_of_supportedSpecWithScalarEvents model selectors hSupported)]
  have hcontract := compile_preserves_semantics_with_scalar_events
    model selectors hSupported ir tx initialWorld htxNormalized
    hcalldataSizeFits hcompile hfuelPos hhelperFree hstmtDisjoint
  simpa [supportedSourceContractSemanticsWithScalarEvents_eq_sourceContractSemantics
    (hSupported := hSupported) tx initialWorld] using hcontract

/-- The final-result event equality, projected out of the guarded theorem:
the compiled contract's emitted event words are exactly the encoding of the
guarded source semantics' events. -/
theorem guarded_scalar_events_final_events_eq
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hfuelPos : 0 < hSupported.helperFuel)
    (hhelperFree :
      ∀ fn, fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeNonEventStepInterface
          (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hstmtDisjoint :
      ∀ fn, fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint { ir with internalFunctions := [] }
          (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body) :
    (interpretGuardedContract model selectors tx initialWorld).events =
      (interpretIR ir tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)).events :=
  (compile_preserves_semantics_guarded_with_scalar_events model selectors
    hSupported ir tx initialWorld htxNormalized hcalldataSizeFits hcompile
    hfuelPos hhelperFree hstmtDisjoint).2.2.2

end Compiler.Proofs.IRGeneration
