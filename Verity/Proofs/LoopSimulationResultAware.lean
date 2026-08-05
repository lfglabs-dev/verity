import Verity.Proofs.LoopSimulation
import Verity.Core.Model.DenoteExternalCalls

/-! # Result-aware external-call loops

This complements the total-state loop bridge with a loop that can stop, return,
or revert after observing an external call. The finite call-site list supplies
the structural bound while each continuation may depend on the call result.
-/

namespace Verity.Proofs.LoopSimulationResultAware

open Compiler.CompilationModel.DenoteExternalCalls
open Compiler.Proofs.IRGeneration.SourceSemantics

/-- The model-side result of one iteration or of the whole loop. -/
inductive IterOutcome (α : Type) where
  | continue (state : α)
  | stop (state : α)
  | return (value : Nat) (state : α)
  | revert

/-- A result-aware body sees the pre-call state, site, and full observation. -/
abbrev Body := CallState → CallSite → CallObservation → IterOutcome CallState

/-- Execute one external call per site until exhaustion or an early result. -/
def execResultAwareForEach (adversary : AdversaryModel) (body : Body) :
    CallState → List CallSite → IterOutcome CallState
  | state, [] => .continue state
  | state, site :: sites =>
      let observation := denoteCall adversary site state
      match body state site observation with
      | .continue next => execResultAwareForEach adversary body next sites
      | .stop next => .stop next
      | .return value next => .return value next
      | .revert => .revert

/-- Relate every executable result to its model-side counterpart. -/
def OutcomeRel (rel : RuntimeState → CallState → Prop) :
    StmtResult → IterOutcome CallState → Prop
  | .continue runtime, .continue model => rel runtime model
  | .stop runtime, .stop model => rel runtime model
  | .return runtimeValue runtime, .return modelValue model =>
      runtimeValue = modelValue ∧ rel runtime model
  | .revert, .revert => True
  | _, _ => False

/-- A model outcome is an early exit exactly when it is not `continue`. -/
def IterOutcome.IsEarlyExit : IterOutcome α → Prop
  | .continue _ => False
  | .stop _ | .return _ _ | .revert => True

/-- The matching executable-result predicate. -/
def stmtResultIsEarlyExit : StmtResult → Prop
  | .continue _ => False
  | .stop _ | .return _ _ | .revert => True

/-- Once a prefix exits, appending sites cannot change its result. -/
theorem execResultAwareForEach_append_of_earlyExit
    (adversary : AdversaryModel) (body : Body)
    (state : CallState) (visited suffix : List CallSite)
    (outcome : IterOutcome CallState)
    (hexec : execResultAwareForEach adversary body state visited = outcome)
    (hearly : outcome.IsEarlyExit) :
    execResultAwareForEach adversary body state (visited ++ suffix) = outcome := by
  induction visited generalizing state with
  | nil =>
      simp [execResultAwareForEach] at hexec
      subst outcome
      exact False.elim hearly
  | cons site sites ih =>
      simp only [List.cons_append, execResultAwareForEach] at hexec ⊢
      cases hbody : body state site (denoteCall adversary site state) with
      | «continue» next =>
          simp only [hbody] at hexec ⊢
          exact ih next hexec
      | stop next => simpa only [hbody] using hexec
      | «return» value next => simpa only [hbody] using hexec
      | revert => simpa only [hbody] using hexec

/-- Core bridge. Local body correspondence relates the complete loops,
including all three early-result constructors. -/
theorem forEach_rel_execForEachLoop_result_aware
    (rel : RuntimeState → CallState → Prop)
    (varName : String)
    (runBody : RuntimeState → StmtResult)
    (adversary : AdversaryModel) (body : Body)
    (hbody : ∀ runtime model index site, rel runtime model →
      OutcomeRel rel
        (runBody
          { runtime with bindings := (
              Compiler.Proofs.IRGeneration.SourceSemantics.bindValue
                runtime.bindings varName
                (Compiler.Proofs.IRGeneration.SourceSemantics.wordNormalize index)) })
        (body model site (denoteCall adversary site model)))
    (runtime : RuntimeState) (model : CallState)
    (index : Nat) (sites : List CallSite) (hinit : rel runtime model) :
    OutcomeRel rel
      (execForEachLoop varName runBody runtime index sites.length)
      (execResultAwareForEach adversary body model sites) := by
  induction sites generalizing runtime model index with
  | nil => simpa [execResultAwareForEach, OutcomeRel] using hinit
  | cons site sites ih =>
      have hlocal := hbody runtime model index site hinit
      simp only [List.length_cons, execForEachLoop,
        execResultAwareForEach]
      cases hsource : runBody
          { runtime with bindings := (
              Compiler.Proofs.IRGeneration.SourceSemantics.bindValue
                runtime.bindings varName
                (Compiler.Proofs.IRGeneration.SourceSemantics.wordNormalize index)) } <;>
        cases hmodel : body model site (denoteCall adversary site model) <;>
        simp only [hsource, hmodel, OutcomeRel] at hlocal ⊢
      · exact ih _ _ (index + 1) hlocal
      · exact hlocal
      · exact hlocal

/-- If the model loop continues, so does `execForEachLoop`, with related final
states. -/
theorem execResultAwareForEach_success_bridge
    (rel : RuntimeState → CallState → Prop)
    (varName : String)
    (runBody : RuntimeState → StmtResult)
    (adversary : AdversaryModel) (body : Body)
    (hbody : ∀ runtime model index site, rel runtime model →
      OutcomeRel rel
        (runBody
          { runtime with bindings := (
              Compiler.Proofs.IRGeneration.SourceSemantics.bindValue
                runtime.bindings varName
                (Compiler.Proofs.IRGeneration.SourceSemantics.wordNormalize index)) })
        (body model site (denoteCall adversary site model)))
    (runtime : RuntimeState) (model finalModel : CallState)
    (index : Nat) (sites : List CallSite) (hinit : rel runtime model)
    (hmodel : execResultAwareForEach adversary body model sites = .continue finalModel) :
    ∃ finalRuntime,
      execForEachLoop varName runBody runtime index sites.length =
          .continue finalRuntime ∧
      rel finalRuntime finalModel := by
  have hsound := forEach_rel_execForEachLoop_result_aware
    rel varName runBody adversary body hbody runtime model index sites hinit
  rw [hmodel] at hsound
  cases hsource : execForEachLoop varName runBody runtime index sites.length with
  | «continue» finalRuntime =>
      simp [hsource, OutcomeRel] at hsound
      exact ⟨finalRuntime, rfl, hsound⟩
  | stop finalRuntime => simp [hsource, OutcomeRel] at hsound
  | «return» value finalRuntime => simp [hsource, OutcomeRel] at hsound
  | revert => simp [hsource, OutcomeRel] at hsound

/-- If the model stops, returns, or reverts, the executable loop has the same
result constructor and return value, with related carried states. -/
theorem execResultAwareForEach_earlyExit_bridge
    (rel : RuntimeState → CallState → Prop)
    (varName : String)
    (runBody : RuntimeState → StmtResult)
    (adversary : AdversaryModel) (body : Body)
    (hbody : ∀ runtime model index site, rel runtime model →
      OutcomeRel rel
        (runBody
          { runtime with bindings := (
              Compiler.Proofs.IRGeneration.SourceSemantics.bindValue
                runtime.bindings varName
                (Compiler.Proofs.IRGeneration.SourceSemantics.wordNormalize index)) })
        (body model site (denoteCall adversary site model)))
    (runtime : RuntimeState) (model : CallState)
    (index : Nat) (sites : List CallSite) (hinit : rel runtime model)
    (hearly : (execResultAwareForEach adversary body model sites).IsEarlyExit) :
    stmtResultIsEarlyExit
        (execForEachLoop varName runBody runtime index sites.length) ∧
      OutcomeRel rel
        (execForEachLoop varName runBody runtime index sites.length)
        (execResultAwareForEach adversary body model sites) := by
  have hsound := forEach_rel_execForEachLoop_result_aware
    rel varName runBody adversary body hbody runtime model index sites hinit
  generalize hsource : execForEachLoop varName runBody runtime index sites.length =
      sourceOutcome at hsound ⊢
  generalize hmodel : execResultAwareForEach adversary body model sites =
      modelOutcome at hsound hearly ⊢
  constructor
  · cases sourceOutcome <;> cases modelOutcome <;>
      simp [OutcomeRel, stmtResultIsEarlyExit, IterOutcome.IsEarlyExit]
        at hsound hearly ⊢
  · exact hsound

end Verity.Proofs.LoopSimulationResultAware
