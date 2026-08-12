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

/-- Guarded per-function root, fall-through bodies: a locked entry reverts
(observable rollback), a free entry projects the body's tail result from the
acquired bound state. -/
theorem exec_compiledGuardedFunctionIR_of_body_fallthrough
    (fields : List Field) (state : IRState) (selector : Nat)
    (spec : FunctionSpec) (returns : List ParamType)
    (bodyStmts : List YulStmt) (bindings : List (String × Nat))
    (tailResult : IRExecResult) (guardedFn : IRFunction)
    (lockField : String) (field : Field) (slot : Nat)
    (hlock : spec.nonReentrantLock = some lockField)
    (hfield : findFieldWithResolvedSlot fields lockField = some (field, slot))
    (hguard : attachNonReentrantGuard fields spec
      (compiledFunctionIR selector spec returns bodyStmts) = .ok guardedFn)
    (hslot : slot < Compiler.Constants.evmModulus)
    (hSS : SpliceSimList bodyStmts)
    (hH : yulFrameHaltsList bodyStmts = false)
    (hsupported : ∀ param ∈ spec.params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 <
      Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams spec.params state.calldata =
      some bindings)
    (hlock01 : state.transientStorage slot = 0 ∨
      state.transientStorage slot = 1)
    (hbody : execIRStmts (stmtsFuelBound bodyStmts)
        (acquiredBoundState slot state spec.params bindings) bodyStmts =
      tailResult) :
    Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads spec.params).length +
          (guardPrologueStmts slot ++
            applyLockReleaseOnExits (lockReleaseStmt slot) bodyStmts).length +
          (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) bodyStmts) +
            (spliceLockReleaseList (lockReleaseStmt slot) bodyStmts).length + 4) + 1)
        guardedFn state.calldata state =
      if state.transientStorage slot = 1 then
        execResultToIRResult state (.revert state)
      else
        execResultToIRResult state tailResult := by
  let preboundState := prebindRawArgs state spec.params
  have hbind' :
      SourceSemantics.bindSupportedParams spec.params preboundState.calldata =
        some bindings := by
    simpa [preboundState] using hbind
  have hfits' : 4 + preboundState.calldata.length * 32 <
      Compiler.Constants.evmModulus := by
    simpa [preboundState] using hcalldataSizeFits
  have htransPre : preboundState.transientStorage = state.transientStorage :=
    prebindRawArgs_transient state spec.params
  have hshape := attachNonReentrantGuard_some_shape fields spec
    (compiledFunctionIR selector spec returns bodyStmts) lockField field slot
    hlock hfield
  rw [hguard] at hshape
  have hbodyEq : guardedFn.body =
      genParamLoads spec.params ++
        (guardPrologueStmts slot ++
          applyLockReleaseOnExits (lockReleaseStmt slot) bodyStmts) := by
    have := congrArg IRFunction.body (Except.ok.inj hshape)
    simpa [compiledFunctionIR, List.take_left, List.drop_left,
      List.append_assoc] using this
  have hparamsEq : guardedFn.params = spec.params.map Param.toIRParam := by
    have := congrArg IRFunction.params (Except.ok.inj hshape)
    simpa [compiledFunctionIR] using this
  have hmain := execIRStmts_guardedFunction_fallthrough slot hslot spec.params
    bindings bodyStmts hSS hH
    (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) bodyStmts) +
      (spliceLockReleaseList (lockReleaseStmt slot) bodyStmts).length + 4)
    (stmtsFuelBound bodyStmts) preboundState hsupported hfits' hbind'
    (by rw [htransPre]; exact hlock01)
    (by omega) (le_refl _)
  unfold Compiler.Proofs.YulGeneration.execIRFunctionFuel
  rw [hbodyEq, hparamsEq]
  have hprebound :
      List.foldl (fun s x => s.setVar x.1.name x.2) state
        ((List.map Param.toIRParam spec.params).zip state.calldata) =
      preboundState := rfl
  rw [hprebound]
  show (match execIRStmts _ preboundState _ with
    | .continue s => _
    | .return v s => _
    | .stop s => _
    | .revert s => _) = _
  rw [hmain, htransPre]
  by_cases hl : state.transientStorage slot = 1
  · rw [if_pos hl, if_pos hl]
    rfl
  · rw [if_neg hl, if_neg hl]
    rw [show ({ ParamLoading.applyBindingsToIRState preboundState bindings with
        transientStorage := fun o => if o = slot then 1
          else state.transientStorage o } : IRState) =
      acquiredBoundState slot state spec.params bindings from
      (acquiredBoundState_eq slot state spec.params bindings).symm]
    rw [hbody]
    cases tailResult <;>
      simp [releasedResult, execResultToIRResult, releaseState]

/-- Guarded per-function root, modeled-halt bodies. -/
theorem exec_compiledGuardedFunctionIR_of_body_halting
    (fields : List Field) (state : IRState) (selector : Nat)
    (spec : FunctionSpec) (returns : List ParamType)
    (ys : List YulStmt) (h : YulStmt) (bindings : List (String × Nat))
    (tailResult : IRExecResult) (guardedFn : IRFunction)
    (lockField : String) (field : Field) (slot : Nat)
    (hlock : spec.nonReentrantLock = some lockField)
    (hfield : findFieldWithResolvedSlot fields lockField = some (field, slot))
    (hguard : attachNonReentrantGuard fields spec
      (compiledFunctionIR selector spec returns (ys ++ [h])) = .ok guardedFn)
    (hslot : slot < Compiler.Constants.evmModulus)
    (hSS : SpliceSimList (ys ++ [h])) (hmh : ModeledHalt h)
    (hsupported : ∀ param ∈ spec.params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 <
      Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams spec.params state.calldata =
      some bindings)
    (hlock01 : state.transientStorage slot = 0 ∨
      state.transientStorage slot = 1)
    (hbody : execIRStmts (stmtsFuelBound (ys ++ [h]))
        (acquiredBoundState slot state spec.params bindings) (ys ++ [h]) =
      tailResult) :
    Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads spec.params).length +
          (guardPrologueStmts slot ++
            applyLockReleaseOnExits (lockReleaseStmt slot) (ys ++ [h])).length +
          (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot)
            (ys ++ [h])) + 2) + 1)
        guardedFn state.calldata state =
      if state.transientStorage slot = 1 then
        execResultToIRResult state (.revert state)
      else
        execResultToIRResult state tailResult := by
  let preboundState := prebindRawArgs state spec.params
  have hbind' :
      SourceSemantics.bindSupportedParams spec.params preboundState.calldata =
        some bindings := by
    simpa [preboundState] using hbind
  have hfits' : 4 + preboundState.calldata.length * 32 <
      Compiler.Constants.evmModulus := by
    simpa [preboundState] using hcalldataSizeFits
  have htransPre : preboundState.transientStorage = state.transientStorage :=
    prebindRawArgs_transient state spec.params
  have hshape := attachNonReentrantGuard_some_shape fields spec
    (compiledFunctionIR selector spec returns (ys ++ [h])) lockField field slot
    hlock hfield
  rw [hguard] at hshape
  have hbodyEq : guardedFn.body =
      genParamLoads spec.params ++
        (guardPrologueStmts slot ++
          applyLockReleaseOnExits (lockReleaseStmt slot) (ys ++ [h])) := by
    have := congrArg IRFunction.body (Except.ok.inj hshape)
    simpa [compiledFunctionIR, List.take_left, List.drop_left,
      List.append_assoc] using this
  have hparamsEq : guardedFn.params = spec.params.map Param.toIRParam := by
    have := congrArg IRFunction.params (Except.ok.inj hshape)
    simpa [compiledFunctionIR] using this
  have hmain := execIRStmts_guardedFunction_halting slot hslot spec.params
    bindings ys h hSS hmh
    (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) (ys ++ [h])) + 2)
    (stmtsFuelBound (ys ++ [h])) preboundState hsupported hfits' hbind'
    (by rw [htransPre]; exact hlock01)
    (by omega) (le_refl _)
  unfold Compiler.Proofs.YulGeneration.execIRFunctionFuel
  rw [hbodyEq, hparamsEq]
  have hprebound :
      List.foldl (fun s x => s.setVar x.1.name x.2) state
        ((List.map Param.toIRParam spec.params).zip state.calldata) =
      preboundState := rfl
  rw [hprebound]
  show (match execIRStmts _ preboundState _ with
    | .continue s => _
    | .return v s => _
    | .stop s => _
    | .revert s => _) = _
  rw [hmain, htransPre]
  by_cases hl : state.transientStorage slot = 1
  · rw [if_pos hl, if_pos hl]
    rfl
  · rw [if_neg hl, if_neg hl]
    rw [show ({ ParamLoading.applyBindingsToIRState preboundState bindings with
        transientStorage := fun o => if o = slot then 1
          else state.transientStorage o } : IRState) =
      acquiredBoundState slot state spec.params bindings from
      (acquiredBoundState_eq slot state spec.params bindings).symm]
    rw [hbody]
    cases tailResult <;>
      simp [releasedResult, execResultToIRResult, releaseState]

end Compiler.Proofs.IRGeneration
