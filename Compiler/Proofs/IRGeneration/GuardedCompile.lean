import Compiler.Proofs.IRGeneration.SpliceSimulation

/-!
# Inversion lemmas for the guarded compilation pipeline

Make `attachNonReentrantGuard_exec` mechanically consumable from
`compileGuardedFunctionSpec`: the compiled function body always has the
loads-then-body shape (by construction of `compileFunctionSpec`), and the
guarded pipeline is exactly compile-then-attach.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel
open Verity.Core.Intrinsics (HardFork)

/-- `compileFunctionSpec` output always has the loads-then-body shape. -/
theorem compileFunctionSpec_body_shape (fields : List Field)
    (events : List EventDef) (errors : List ErrorDef)
    (adtTypes : List AdtTypeDef) (selector : Nat) (spec : FunctionSpec)
    (targetFork : HardFork) (internalFunctions : List FunctionSpec)
    (irFn : IRFunction)
    (h : compileFunctionSpec fields events errors adtTypes selector spec
      targetFork internalFunctions = .ok irFn) :
    ∃ bodyStmts, irFn.body = genParamLoads spec.params ++ bodyStmts := by
  unfold compileFunctionSpec at h
  cases hv : validateFunctionSpec spec with
  | error e => rw [hv] at h; cases h
  | ok _ =>
      rw [hv] at h
      cases hr : functionReturns spec with
      | error e => rw [hr] at h; cases h
      | ok returns =>
          rw [hr] at h
          cases hb : compileStmtListWithFork fields events errors .calldata [] false
              (spec.params.map (·.name)) adtTypes targetFork spec.body
              internalFunctions with
          | error e => rw [hb] at h; cases h
          | ok bodyStmts =>
              rw [hb] at h
              refine ⟨bodyStmts, ?_⟩
              have := Except.ok.inj h
              rw [← this]

/-- The guarded pipeline is exactly compile-then-attach. -/
theorem compileGuardedFunctionSpec_inv (fields : List Field)
    (events : List EventDef) (errors : List ErrorDef)
    (adtTypes : List AdtTypeDef) (internalFunctions : List FunctionSpec)
    (sel : Nat) (spec : FunctionSpec) (targetFork : HardFork)
    (fn : IRFunction)
    (h : compileGuardedFunctionSpec fields events errors adtTypes
      internalFunctions sel spec targetFork = .ok fn) :
    ∃ irFn, compileFunctionSpec fields events errors adtTypes sel spec
        targetFork internalFunctions = .ok irFn ∧
      attachNonReentrantGuard fields spec irFn = .ok fn := by
  unfold compileGuardedFunctionSpec at h
  cases hc : compileFunctionSpec fields events errors adtTypes sel spec
      targetFork internalFunctions with
  | error e => rw [hc] at h; cases h
  | ok irFn =>
      rw [hc] at h
      exact ⟨irFn, rfl, h⟩

end Compiler.Proofs.IRGeneration
