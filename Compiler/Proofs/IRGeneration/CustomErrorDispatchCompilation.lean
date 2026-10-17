import Compiler.Proofs.IRGeneration.CustomErrorCompilationOrigin

namespace Compiler.Proofs.IRGeneration.CustomErrorDispatchCompilation
open Compiler.CompilationModel Compiler.Yul Verity.Core.Intrinsics

/-- Injecting the actual transient guard changes only the body. -/
theorem guard_metadata (fields : List Field) (fn : FunctionSpec) (before after : IRFunction)
    (origin : attachNonReentrantGuard fields fn before = .ok after) :
    after.selector = before.selector ∧ after.payable = before.payable ∧ after.params = before.params := by
  unfold attachNonReentrantGuard at origin
  cases lock : fn.nonReentrantLock with
  | none =>
    simp only [lock, pure, Except.pure, Except.ok.injEq] at origin
    subst after
    exact ⟨rfl, rfl, rfl⟩
  | some field =>
    cases prologue : nonReentrantGuardPrologue fields field with
    | error message => simp [lock, prologue, bind, Except.bind] at origin
    | ok stmts =>
      simp only [lock, prologue, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at origin
      subst after
      exact ⟨rfl, rfl, rfl⟩

/-- Actual guarded compilation retains selector and dispatcher admission fields. -/
theorem guarded_metadata (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (adts : List AdtTypeDef) (internals : List FunctionSpec) (selector : Nat)
    (fn : FunctionSpec) (fork : HardFork) (compiled : IRFunction)
    (origin : compileGuardedFunctionSpec fields events errors adts internals selector fn fork = .ok compiled) :
    compiled.selector = selector ∧ compiled.payable = fn.isPayable ∧
      compiled.params.length = fn.params.length := by
  unfold compileGuardedFunctionSpec at origin
  cases lowered : compileFunctionSpec fields events errors adts selector fn fork internals with
  | error message => simp [lowered, bind, Except.bind] at origin
  | ok before =>
    simp only [lowered, bind, Except.bind] at origin
    obtain ⟨key, payable, params⟩ := guard_metadata fields fn before compiled origin
    obtain ⟨keyBefore, payableBefore, countBefore⟩ :=
      CustomErrorCompilationOrigin.metadata fields events errors adts selector fn fork internals before lowered
    exact ⟨key.trans keyBefore, payable.trans payableBefore, by simpa only [params] using countBefore⟩

/-- A successful real mapM preserves first-match selection and gives the exact
compiler receipt for the selected function. This requires no unique-selector
oracle: duplicate selectors retain their actual first-match order. -/
theorem mapM_selected (lower : (FunctionSpec × Nat) → Except String IRFunction)
    (keys : ∀ entry compiled, lower entry = .ok compiled → compiled.selector = entry.2)
    (entries : List (FunctionSpec × Nat)) (out : List IRFunction)
    (selector : Nat) (entry : FunctionSpec × Nat)
    (origin : entries.mapM lower = .ok out)
    (selected : entries.find? (fun candidate => candidate.2 == selector) = some entry) :
    ∃ compiled, out.find? (fun candidate => candidate.selector == selector) = some compiled ∧
      lower entry = .ok compiled := by
  induction entries generalizing out with
  | nil => simp at selected
  | cons head tail ih =>
    cases first : lower head with
    | error message => simp [List.mapM_cons, first, bind, Except.bind] at origin
    | ok compiled =>
      cases rest : tail.mapM lower with
      | error message => simp [List.mapM_cons, first, rest, bind, Except.bind] at origin
      | ok remaining =>
        simp only [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at origin
        subst out
        have key := keys head compiled first
        by_cases hit : (head.2 == selector) = true
        · simp only [List.find?_cons, hit, ↓reduceIte, Option.some.injEq] at selected
          subst entry
          exact ⟨compiled, by simp [List.find?_cons, key, hit], first⟩
        · have missed : (head.2 == selector) = false := Bool.eq_false_iff.mpr hit
          simp only [List.find?_cons, missed, Bool.false_eq_true, ↓reduceIte] at selected
          obtain ⟨chosen, found, receipt⟩ := ih remaining rest selected
          exact ⟨chosen, by simpa only [List.find?_cons, key, missed, Bool.false_eq_true,
            ↓reduceIte] using found, receipt⟩

/-- The actual guarded external-function map used in compileValidatedCore
selects the same Source function and yields its real guarded compiler receipt. -/
theorem guarded_list_selected (spec : CompilationModel) (selectors : List Nat)
    (fork : HardFork) (out : List IRFunction) (selector : Nat) (fn : FunctionSpec)
    (origin : (SourceSemantics.selectorFunctionPairs spec selectors).mapM
      (fun entry => compileGuardedFunctionSpec (SourceSemantics.effectiveFields spec)
        spec.events spec.errors spec.adtTypes (spec.functions.filter (·.isInternal))
        entry.2 entry.1 fork) = .ok out)
    (selected : SourceSemantics.findFunctionBySelector spec selectors selector = some fn) :
    ∃ compiled, out.find? (fun candidate => candidate.selector == selector) = some compiled ∧
      compileGuardedFunctionSpec (SourceSemantics.effectiveFields spec) spec.events spec.errors
        spec.adtTypes (spec.functions.filter (·.isInternal)) selector fn fork = .ok compiled := by
  unfold SourceSemantics.findFunctionBySelector at selected
  cases found : (SourceSemantics.selectorFunctionPairs spec selectors).find?
      (fun entry => entry.2 == selector) with
  | none => simp only [found, Option.map_none] at selected; cases selected
  | some entry =>
    simp only [found, Option.map_some, Option.some.injEq] at selected
    have same : entry.2 = selector := by
      have hit : (entry.2 == selector) = true := List.find?_some (p := fun candidate : FunctionSpec × Nat => candidate.2 == selector) (a := entry) found
      exact beq_iff_eq.mp hit
    obtain ⟨compiled, chosen, receipt⟩ := mapM_selected
      (fun entry => compileGuardedFunctionSpec (SourceSemantics.effectiveFields spec)
        spec.events spec.errors spec.adtTypes (spec.functions.filter (·.isInternal))
        entry.2 entry.1 fork)
      (fun entry compiled proof => (guarded_metadata (SourceSemantics.effectiveFields spec)
        spec.events spec.errors spec.adtTypes (spec.functions.filter (·.isInternal))
        entry.2 entry.1 fork compiled proof).1)
      (SourceSemantics.selectorFunctionPairs spec selectors) out selector entry origin found
    exact ⟨compiled, chosen, by simpa only [same, selected] using receipt⟩

end Compiler.Proofs.IRGeneration.CustomErrorDispatchCompilation
