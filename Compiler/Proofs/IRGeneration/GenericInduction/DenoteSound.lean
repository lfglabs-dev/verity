import Compiler.Proofs.IRGeneration.GenericInduction.Main
import Compiler.Proofs.IRGeneration.DenoteAgreement

/-!
# Generic denote-headed soundness (`denote_sound`)

Restates the generic body/IR preservation theorems of `GenericInduction.Main`
with the compiler-free denotation (`Verity.Core.Model.Denote`) on the source
side, using the agreement theorem `DenoteAgreement.execStmtList_eq`.

This is the umbrella the per-contract `_bridge` instantiations target: one
generic statement headed by `Denote.execStmtList` instead of per-function
`SourceSemantics` re-derivations.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-- Denote-side entry state for running a function body: transaction context
applied to the initial world, parameter bindings installed, selector set. -/
def denoteEntryState (initialWorld : Verity.ContractState) (tx : IRTransaction)
    (bindings : List (String × Nat)) : Denote.DenoteState :=
  { world := SourceSemantics.withTransactionContext initialWorld tx
    bindings := bindings
    selector := tx.functionSelector }

/-- Generic denote-headed soundness: under the same hypotheses as
`supported_function_body_correct_from_exact_state_generic`, the compiler-free
denotation of the source body matches the IR execution of the compiled body. -/
theorem denote_sound
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hgeneric :
      StmtListGenericCore
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    ∃ sourceResult irExec,
      DenoteAgreement.toStmtResult
        (Denote.execStmtList DenoteAgreement.sourceOracle
          (SourceSemantics.effectiveFields model)
          (denoteEntryState initialWorld tx bindings)
          fn.body) = sourceResult ∧
      execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
  rcases supported_function_body_correct_from_exact_state_generic
      model fn bodyStmts tx initialWorld state bindings extraFuel hextraFuel
      hnormalized hnoEvents hnoErrors hnoAdtTypes hgeneric hbodyCompile hscope hbounded
      hstateRuntime hstateBindings with
    ⟨sourceResult, irExec, hsource, hexec, hmatch⟩
  refine ⟨sourceResult, irExec, ?_, hexec, hmatch⟩
  rw [DenoteAgreement.execStmtList_eq]
  exact hsource

/-- Helper-aware denote-headed soundness: same hypotheses as
`supported_function_body_correct_from_exact_state_generic_with_helpers`; the
conclusion additionally pins the helper-aware source execution to the same
result as the compiler-free denotation. -/
theorem denote_sound_with_helpers
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hhelperSurface : stmtListTouchesUnsupportedHelperSurface fn.body = false)
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    ∃ sourceResult irExec,
      DenoteAgreement.toStmtResult
        (Denote.execStmtList DenoteAgreement.sourceOracle
          (SourceSemantics.effectiveFields model)
          (denoteEntryState initialWorld tx bindings)
          fn.body) = sourceResult ∧
      SourceSemantics.execStmtListWithHelpers
        model
        (SourceSemantics.effectiveFields model)
        helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body = sourceResult ∧
      execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
  rcases supported_function_body_correct_from_exact_state_generic_with_helpers
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hnormalized hnoEvents hnoErrors hnoAdtTypes hhelperSurface hhelperFree
      hbodyCompile hscope hbounded hstateRuntime hstateBindings with
    ⟨sourceResult, irExec, hwithHelpers, hexec, hmatch⟩
  refine ⟨sourceResult, irExec, ?_, hwithHelpers, hexec, hmatch⟩
  have hcons :=
    SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
      model (SourceSemantics.effectiveFields model) helperFuel
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := bindings
        selector := tx.functionSelector }
      fn.body hhelperSurface
  rw [DenoteAgreement.execStmtList_eq]
  simp only [SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal, hnoEvents,
    SourceSemantics.execStmtListWithEvents_nil_eq_execStmtList] at hcons
  exact hcons.symm.trans hwithHelpers

end Compiler.Proofs.IRGeneration
