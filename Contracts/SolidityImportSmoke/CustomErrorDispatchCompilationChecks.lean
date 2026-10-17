import Compiler.Proofs.IRGeneration.CustomErrorDispatchCompilation

namespace SolidityImportSmoke.CustomErrorDispatchCompilationChecks
open Compiler Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open CustomErrorDispatchCompilation Verity.Core.Intrinsics

example (spec : CompilationModel) (selectors : List Nat)
    (fork : HardFork) (out : List IRFunction) (selector : Nat) (fn : FunctionSpec)
    (origin : (SourceSemantics.selectorFunctionPairs spec selectors).mapM
      (fun entry => compileGuardedFunctionSpec (SourceSemantics.effectiveFields spec)
        spec.events spec.errors spec.adtTypes (spec.functions.filter (·.isInternal))
        entry.2 entry.1 fork) = .ok out)
    (selected : SourceSemantics.findFunctionBySelector spec selectors selector = some fn) :
    ∃ compiled, out.find? (fun candidate => candidate.selector == selector) = some compiled ∧
      compileGuardedFunctionSpec (SourceSemantics.effectiveFields spec) spec.events spec.errors
        spec.adtTypes (spec.functions.filter (·.isInternal)) selector fn fork = .ok compiled :=
  guarded_list_selected spec selectors fork out selector fn origin selected

/-- Guard injection cannot silently change payment admission. -/
example (fields : List Field) (fn : FunctionSpec) (before after : IRFunction)
    (origin : attachNonReentrantGuard fields fn before = .ok after)
    (changed : after.payable ≠ before.payable) : False :=
  changed (guard_metadata fields fn before after origin).2.1

/-- The list theorem covers a missed head followed by a repeated selector.
The actual first match is retained even without collision validation. -/
example (lower : (FunctionSpec × Nat) → Except String IRFunction)
    (keys : ∀ entry compiled, lower entry = .ok compiled → compiled.selector = entry.2)
    (head first second : FunctionSpec × Nat) (out : List IRFunction)
    (selector : Nat) (miss : (head.2 == selector) = false)
    (hit : (first.2 == selector) = true) (duplicate : second.2 = first.2)
    (origin : [head, first, second].mapM lower = .ok out) :
    ∃ compiled, out.find? (fun candidate => candidate.selector == selector) = some compiled ∧
      lower first = .ok compiled := by
  apply mapM_selected lower keys [head, first, second] out selector first origin
  simp only [List.find?_cons, miss, hit, Bool.false_eq_true, ↓reduceIte]

end SolidityImportSmoke.CustomErrorDispatchCompilationChecks
