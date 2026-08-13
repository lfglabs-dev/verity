import Compiler.Proofs.IRGeneration.GuardedCompile
import Compiler.Proofs.IRGeneration.ContractShape
import Compiler.Proofs.IRGeneration.Function

/-!
# Shape lemmas for the guarded whole-contract variant (additive)

The existing whole-contract chain erases `compileGuardedFunctionSpec` down to
`compileFunctionSpec` via the global lock-free rewrite.  The `*_guarded`
variant instead keeps the guarded pipeline: this module provides the
erasure-free `Forall₂` decomposition of the compile mapM and the metadata
preservation facts the dispatcher lookup needs (`attachNonReentrantGuard`
touches only the body).
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel
open Verity.Core.Intrinsics (HardFork)

/-- The guard transformation preserves every metadata field. -/
theorem attachNonReentrantGuard_metadata (fields : List Field)
    (spec : FunctionSpec) (irFn fn' : IRFunction)
    (h : attachNonReentrantGuard fields spec irFn = .ok fn') :
    fn'.name = irFn.name ∧ fn'.selector = irFn.selector ∧
      fn'.params = irFn.params ∧ fn'.ret = irFn.ret ∧
      fn'.payable = irFn.payable := by
  unfold attachNonReentrantGuard at h
  cases hlock : spec.nonReentrantLock with
  | none =>
      rw [hlock] at h
      obtain rfl := Except.ok.inj h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some lockField =>
      rw [hlock] at h
      simp only [bind, Except.bind] at h
      cases hpro : nonReentrantGuardPrologue fields lockField with
      | error e =>
          rw [hpro] at h
          cases h
      | ok guardStmts =>
          rw [hpro] at h
          obtain rfl := Except.ok.inj h
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Guarded-pipeline metadata: selector/params/payable come from the spec
exactly as in the unguarded pipeline. -/
theorem compileGuardedFunctionSpec_ok_metadata (fields : List Field)
    (events : List EventDef) (errors : List ErrorDef)
    (internalFunctions : List FunctionSpec)
    (sel : Nat) (spec : FunctionSpec) (fn : IRFunction)
    (h : compileGuardedFunctionSpec fields events errors [] internalFunctions
      sel spec = .ok fn) :
    fn.params = spec.params.map Param.toIRParam ∧
      fn.selector = sel ∧ fn.payable = spec.isPayable := by
  obtain ⟨irFn, hcompile, hattach⟩ :=
    compileGuardedFunctionSpec_inv fields events errors [] internalFunctions
      sel spec .cancun fn h
  obtain ⟨hparams, hsel, hpay⟩ :=
    Function.compileFunctionSpec_ok_metadata_with_internals fields events errors
      sel spec irFn internalFunctions hcompile
  obtain ⟨_, hsel', hparams', _, hpay'⟩ :=
    attachNonReentrantGuard_metadata fields spec irFn fn hattach
  exact ⟨hparams' ▸ hparams, hsel' ▸ hsel, hpay' ▸ hpay⟩

/-- Erasure-free `Forall₂` decomposition of the guarded compile mapM: no
lock-free hypothesis, each entry is characterized by the guarded pipeline. -/
theorem guarded_functions_forall₂_of_mapM_ok
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (internalFunctions : List FunctionSpec) :
    ∀ (entries : List (FunctionSpec × Nat)) irFns,
      (entries.mapM fun (entry : FunctionSpec × Nat) =>
        compileGuardedFunctionSpec fields events errors [] internalFunctions
          entry.2 entry.1) = Except.ok irFns →
      List.Forall₂
        (fun (entry : FunctionSpec × Nat) irFn =>
          compileGuardedFunctionSpec fields events errors [] internalFunctions
            entry.2 entry.1 = Except.ok irFn)
        entries irFns := by
  intro entries
  induction entries with
  | nil =>
      intro irFns hmap
      cases hmap
      simp
  | cons entry entries ih =>
      intro irFns hmap
      rcases hstep : compileGuardedFunctionSpec fields events errors []
          internalFunctions entry.2 entry.1 with _ | irFn
      · simp only [List.mapM_cons, hstep, bind, Except.bind] at hmap
        cases hmap
      · rcases htail : List.mapM
            (fun (entry : FunctionSpec × Nat) =>
              compileGuardedFunctionSpec fields events errors []
                internalFunctions entry.2 entry.1) entries with _ | irFnsTail
        · simp only [List.mapM_cons, hstep, htail, bind, Except.bind] at hmap
          cases hmap
        · simp only [List.mapM_cons, hstep, htail, bind, Except.bind] at hmap
          cases hmap
          exact List.Forall₂.cons hstep (ih _ htail)

end Compiler.Proofs.IRGeneration
