import Compiler.Proofs.IRGeneration.GuardedCompile
import Compiler.Proofs.IRGeneration.Function
import Compiler.Proofs.YulGeneration.IRFuel

/-!
# The `*_guarded` theorem family (per-function root)

Additive counterparts of `exec_compiledFunctionIR_of_body` for functions
annotated `nonreentrant(lock)`: the guarded compilation unit executes, at the
`IRResult` observable, exactly as the guard's source semantics dictates —
a locked entry reverts (observable rollback to the initial storage/events),
and a free entry behaves as the body executed from the acquired bound state.
Because `IRResult` does not observe transient storage, the lock release is
observably invisible, so the free case's right-hand side is the *plain*
projection of the body's tail result — existing source-correspondence
consumers compose with it unchanged.

Existing theorem statements are untouched (per the additive-family design
decision); this module only adds.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration.Function

/-- The release is observably invisible: `IRResult` ignores transient
storage. -/
theorem execResultToIRResult_releasedResult (init : IRState) (slot : Nat)
    (r : IRExecResult) :
    execResultToIRResult init (releasedResult slot r) =
      execResultToIRResult init r := by
  cases r <;> rfl

/-- Raw-argument prebinding never touches transient storage. -/
theorem prebindRawArgs_transient (state : IRState) (params : List Param) :
    (prebindRawArgs state params).transientStorage = state.transientStorage := by
  unfold prebindRawArgs
  generalize (params.map Param.toIRParam).zip state.calldata = l
  induction l generalizing state with
  | nil => rfl
  | cons p rest ih => exact ih (state.setVar p.1.name p.2)

/-- The state a free guarded entry hands to its body: arguments bound, lock
acquired. -/
def acquiredBoundState (slot : Nat) (state : IRState) (params : List Param)
    (bindings : List (String × Nat)) : IRState :=
  { ParamLoading.applyBindingsToIRState (prebindRawArgs state params) bindings with
    transientStorage := fun o =>
      if o = slot then 1
      else (prebindRawArgs state params).transientStorage o }

/-- Consumer-facing form: the lock overlay reads the ORIGINAL transient
store. -/
theorem acquiredBoundState_eq (slot : Nat) (state : IRState)
    (params : List Param) (bindings : List (String × Nat)) :
    acquiredBoundState slot state params bindings =
      { ParamLoading.applyBindingsToIRState (prebindRawArgs state params)
          bindings with
        transientStorage := fun o =>
          if o = slot then 1 else state.transientStorage o } := by
  simp [acquiredBoundState, prebindRawArgs_transient]

/-- Shape of a guarded compiled function: parameter loads, guard prologue,
then the body with lock releases spliced on every exit. -/
private theorem guardedFn_body_params_eq (fields : List Field) (selector : Nat)
    (spec : FunctionSpec) (returns : List ParamType) (habi : spec.abiDecoding = .standard)
    (body : List YulStmt) (guardedFn : IRFunction) (lockField : String) (field : Field)
    (slot : Nat) (hlock : spec.nonReentrantLock = some lockField)
    (hfield : findFieldWithResolvedSlot fields lockField = some (field, slot))
    (hguard : attachNonReentrantGuard fields spec
      (compiledFunctionIR selector spec returns body) = .ok guardedFn) :
    guardedFn.body = genParamLoads spec.params ++
        (guardPrologueStmts slot ++ applyLockReleaseOnExits (lockReleaseStmt slot) body) ∧
      guardedFn.params = spec.params.map Param.toIRParam := by
  have hshape := attachNonReentrantGuard_some_shape fields spec
    (compiledFunctionIR selector spec returns body) lockField field slot hlock hfield
  rw [hguard] at hshape
  constructor
  · have := congrArg IRFunction.body (Except.ok.inj hshape)
    simpa [compiledFunctionIR, FunctionSpec.bindingParams, habi, List.take_left, List.drop_left,
      List.append_assoc] using this
  · have := congrArg IRFunction.params (Except.ok.inj hshape)
    simpa [compiledFunctionIR] using this

/-- `execIRFunctionFuel` of a function whose body executes, from the prebound
state, to `r` is the `IRResult` projection of `r`. -/
private theorem execIRFunctionFuel_eq_of_prebound (fuel : Nat) (fn : IRFunction)
    (state : IRState) (params : List Param) (body : List YulStmt) (r : IRExecResult)
    (hbodyEq : fn.body = body) (hparamsEq : fn.params = params.map Param.toIRParam)
    (hexec : execIRStmts fuel (prebindRawArgs state params) body = r) :
    Compiler.Proofs.YulGeneration.execIRFunctionFuel fuel fn state.calldata state =
      execResultToIRResult state r := by
  unfold Compiler.Proofs.YulGeneration.execIRFunctionFuel
  rw [hbodyEq, hparamsEq]
  show (match execIRStmts _ (prebindRawArgs state params) _ with
    | .continue s => _
    | .return v s => _
    | .stop s => _
    | .revert s => _) = _
  rw [hexec]
  cases r <;> rfl

/-- A guarded compiled function whose guarded body executes, from the
prebound state, to `r` projects `r`. -/
private theorem exec_guardedFn_eq_of_prebound (fields : List Field) (selector : Nat)
    (spec : FunctionSpec) (returns : List ParamType) (habi : spec.abiDecoding = .standard)
    (body : List YulStmt) (guardedFn : IRFunction) (lockField : String) (field : Field)
    (slot : Nat) (hlock : spec.nonReentrantLock = some lockField)
    (hfield : findFieldWithResolvedSlot fields lockField = some (field, slot))
    (hguard : attachNonReentrantGuard fields spec
      (compiledFunctionIR selector spec returns body) = .ok guardedFn)
    (fuel : Nat) (state : IRState) (r : IRExecResult)
    (hexec : execIRStmts fuel (prebindRawArgs state spec.params) (genParamLoads spec.params ++
        (guardPrologueStmts slot ++ applyLockReleaseOnExits (lockReleaseStmt slot) body)) = r) :
    Compiler.Proofs.YulGeneration.execIRFunctionFuel fuel guardedFn state.calldata state =
      execResultToIRResult state r := by
  obtain ⟨hb, hp⟩ := guardedFn_body_params_eq fields selector spec returns habi body
    guardedFn lockField field slot hlock hfield hguard
  exact execIRFunctionFuel_eq_of_prebound _ _ _ _ _ _ hb hp hexec

/-- Projecting the guarded unit's result: a held lock reverts, a free lock
yields the body's tail result (the release is observably invisible). -/
private theorem execResultToIRResult_guarded (state : IRState) (slot G : Nat)
    (params : List Param) (bindings : List (String × Nat)) (xs : List YulStmt)
    (tailResult : IRExecResult)
    (hbody : execIRStmts G (acquiredBoundState slot state params bindings) xs = tailResult) :
    execResultToIRResult state
        (if (prebindRawArgs state params).transientStorage slot = 1 then
          .revert (ParamLoading.applyBindingsToIRState (prebindRawArgs state params) bindings)
        else
          (match execIRStmts G (acquiredBoundState slot state params bindings) xs with
            | .continue s => .continue (releaseState slot s)
            | .return v s => .return v (releaseState slot s)
            | .stop s => .stop (releaseState slot s)
            | .revert s => .revert s)) =
      if state.transientStorage slot = 1 then execResultToIRResult state (.revert state)
      else execResultToIRResult state tailResult := by
  rw [prebindRawArgs_transient]
  by_cases hl : state.transientStorage slot = 1
  · rw [if_pos hl, if_pos hl]
    rfl
  · rw [if_neg hl, if_neg hl, hbody]
    cases tailResult <;> simp [execResultToIRResult, releaseState]

/-- Guarded per-function root, fall-through bodies: a locked entry reverts
(observable rollback), a free entry projects the body's tail result from the
acquired bound state. -/
theorem exec_compiledGuardedFunctionIR_of_body_fallthrough
    (fields : List Field) (state : IRState) (selector : Nat) (spec : FunctionSpec)
    (returns : List ParamType) {habi : spec.abiDecoding = .standard} (bodyStmts : List YulStmt)
    (bindings : List (String × Nat)) (tailResult : IRExecResult) (guardedFn : IRFunction)
    (lockField : String) (field : Field) (slot : Nat)
    (hlock : spec.nonReentrantLock = some lockField)
    (hfield : findFieldWithResolvedSlot fields lockField = some (field, slot))
    (hguard : attachNonReentrantGuard fields spec
      (compiledFunctionIR selector spec returns bodyStmts) = .ok guardedFn)
    (hslot : slot < Compiler.Constants.evmModulus)
    (hSS : SpliceSimList bodyStmts) (hH : yulFrameHaltsList bodyStmts = false)
    (hsupported : ∀ param ∈ spec.params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams spec.params state.calldata = some bindings)
    (hlock01 : state.transientStorage slot = 0 ∨ state.transientStorage slot = 1)
    (hbody : execIRStmts (stmtsFuelBound bodyStmts)
        (acquiredBoundState slot state spec.params bindings) bodyStmts = tailResult) :
    Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads spec.params).length + (guardPrologueStmts slot ++
            applyLockReleaseOnExits (lockReleaseStmt slot) bodyStmts).length +
          (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) bodyStmts) +
            (spliceLockReleaseList (lockReleaseStmt slot) bodyStmts).length + 4) + 1)
        guardedFn state.calldata state =
      if state.transientStorage slot = 1 then execResultToIRResult state (.revert state)
      else execResultToIRResult state tailResult := by
  refine (exec_guardedFn_eq_of_prebound fields selector spec returns habi _ guardedFn lockField
    field slot hlock hfield hguard _ _ _ (execIRStmts_guardedFunction_fallthrough slot hslot
      spec.params bindings bodyStmts hSS hH _ _ _ hsupported (by simpa using hcalldataSizeFits)
      (by simpa using hbind) (by rw [prebindRawArgs_transient]; exact hlock01) (by omega)
      (le_refl _))).trans (execResultToIRResult_guarded _ _ _ _ _ _ _ hbody)

/-- Guarded per-function root, modeled-halt bodies. -/
theorem exec_compiledGuardedFunctionIR_of_body_halting
    (fields : List Field) (state : IRState) (selector : Nat) (spec : FunctionSpec)
    (returns : List ParamType) {habi : spec.abiDecoding = .standard} (ys : List YulStmt)
    (h : YulStmt) (bindings : List (String × Nat)) (tailResult : IRExecResult)
    (guardedFn : IRFunction) (lockField : String) (field : Field) (slot : Nat)
    (hlock : spec.nonReentrantLock = some lockField)
    (hfield : findFieldWithResolvedSlot fields lockField = some (field, slot))
    (hguard : attachNonReentrantGuard fields spec
      (compiledFunctionIR selector spec returns (ys ++ [h])) = .ok guardedFn)
    (hslot : slot < Compiler.Constants.evmModulus) (hSS : SpliceSimList (ys ++ [h]))
    (hmh : ModeledHalt h)
    (hsupported : ∀ param ∈ spec.params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams spec.params state.calldata = some bindings)
    (hlock01 : state.transientStorage slot = 0 ∨ state.transientStorage slot = 1)
    (hbody : execIRStmts (stmtsFuelBound (ys ++ [h]))
        (acquiredBoundState slot state spec.params bindings) (ys ++ [h]) = tailResult) :
    Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads spec.params).length + (guardPrologueStmts slot ++
            applyLockReleaseOnExits (lockReleaseStmt slot) (ys ++ [h])).length +
          (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) (ys ++ [h])) + 2) + 1)
        guardedFn state.calldata state =
      if state.transientStorage slot = 1 then execResultToIRResult state (.revert state)
      else execResultToIRResult state tailResult := by
  refine (exec_guardedFn_eq_of_prebound fields selector spec returns habi _ guardedFn lockField
    field slot hlock hfield hguard _ _ _ (execIRStmts_guardedFunction_halting slot hslot
      spec.params bindings ys h hSS hmh _ _ _ hsupported (by simpa using hcalldataSizeFits)
      (by simpa using hbind) (by rw [prebindRawArgs_transient]; exact hlock01) (by omega)
      (le_refl _))).trans (execResultToIRResult_guarded _ _ _ _ _ _ _ hbody)

end Compiler.Proofs.IRGeneration
