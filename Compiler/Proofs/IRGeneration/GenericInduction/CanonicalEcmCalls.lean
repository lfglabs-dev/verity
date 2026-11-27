import Compiler.CompilationModel.Compile
import Compiler.Proofs.IRGeneration.SupportedFragment

/-!
# Canonical ECM Factorization for External and Low-Level Calls (`G3`)

This module factors `Stmt.externalCallBind`, `Stmt.tryExternalCallBind`, and
low-level call bindings (`Expr.call`, `Expr.staticcall`, `Expr.delegatecall`)
into canonical `ECM.ExternalCallModule` instances wrapped in `Stmt.ecm`.

By lowering raw external call and low-level call bindings to `Stmt.ecm` over
canonical module descriptors, external and low-level calls enter the proven
Layer-2 generic induction core through `CanonicalEcmHeadStepBridgeWithInternals`
and `compiledStmtStepWithHelpersAndHelperIRWithInternals_canonical*`.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-! ## Canonical External Call Module Constructors -/

/-- Canonical Yul statement emitted by a typed external call binding. -/
def canonicalTypedExternalCallYulStmt
    (calleeName : String) (resultVars : List String) (argExprs : List YulExpr) : YulStmt :=
  if resultVars.isEmpty then
    YulStmt.exprStmt (YulExpr.call calleeName argExprs)
  else
    YulStmt.letMany resultVars (YulExpr.call calleeName argExprs)

/-- Canonical `ECM.ExternalCallModule` representing a typed external call
(`Stmt.externalCallBind resultVars calleeName args`). -/
def canonicalTypedExternalCallModule
    (calleeName : String)
    (argCount : Nat)
    (resultVars : List String)
    (isPayable : Bool := false)
    (isStatic : Bool := false) : ECM.ExternalCallModule where
  name := s!"canonical_external_call_{calleeName}"
  numArgs := argCount
  resultVars := resultVars
  writesState := !isStatic
  readsState := true
  compile := fun _ argExprs =>
    pure [canonicalTypedExternalCallYulStmt calleeName resultVars argExprs]
  byteTransport := none
  axioms := []
  proofStatus := .assumed
  summaryName := calleeName
  summarySelector := none
  summaryMutability := if isStatic then .staticcall else .call
  targetArg := none
  valueArg := if isPayable then some 0 else none

/-- Canonical Yul statement emitted by a non-reverting `try` external call binding. -/
def canonicalTryExternalCallYulStmt
    (calleeName : String) (successVar : String) (resultVars : List String)
    (argExprs : List YulExpr) : YulStmt :=
  YulStmt.letMany (successVar :: resultVars) (YulExpr.call s!"{calleeName}_try" argExprs)

/-- Canonical `ECM.ExternalCallModule` representing a `try` external call
(`Stmt.tryExternalCallBind successVar resultVars calleeName args`). -/
def canonicalTryExternalCallModule
    (calleeName : String)
    (argCount : Nat)
    (successVar : String)
    (resultVars : List String)
    (isPayable : Bool := false) : ECM.ExternalCallModule where
  name := s!"canonical_try_external_call_{calleeName}"
  onFailure := .bindZero -- binds the success flag; nothing reverts by itself
  numArgs := argCount
  resultVars := successVar :: resultVars
  writesState := true
  readsState := true
  compile := fun _ argExprs =>
    pure [canonicalTryExternalCallYulStmt calleeName successVar resultVars argExprs]
  byteTransport := none
  axioms := []
  proofStatus := .assumed
  summaryName := s!"{calleeName}_try"
  summarySelector := none
  summaryMutability := .call
  targetArg := none
  valueArg := if isPayable then some 0 else none

/-- Classification of raw EVM low-level call opcodes factored through canonical ECMs. -/
inductive CanonicalLowLevelCallKind where
  | call
  | staticcall
  | delegatecall
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Lowercase alias matching the task specification naming for `CanonicalLowLevelCallKind`. -/
abbrev canonicalLowLevelCallKind := CanonicalLowLevelCallKind

namespace CanonicalLowLevelCallKind

/-- Yul builtin opcode name corresponding to each low-level call kind. -/
def yulOpcode : CanonicalLowLevelCallKind → String
  | .call => "call"
  | .staticcall => "staticcall"
  | .delegatecall => "delegatecall"

/-- Expected operand count for each low-level call kind (`call` takes 7;
`staticcall` and `delegatecall` take 6). -/
def numArgs : CanonicalLowLevelCallKind → Nat
  | .call => 7
  | .staticcall => 6
  | .delegatecall => 6

/-- Whether the low-level call opcode may mutate state (`call` and `delegatecall`
may write state; `staticcall` is read-only). -/
def writesState : CanonicalLowLevelCallKind → Bool
  | .call => true
  | .staticcall => false
  | .delegatecall => true

end CanonicalLowLevelCallKind

/-- Canonical Yul statement emitted by a low-level call binding. -/
def canonicalLowLevelCallYulStmt
    (kind : CanonicalLowLevelCallKind) (resultVar : String) (argExprs : List YulExpr) : YulStmt :=
  YulStmt.let_ resultVar (YulExpr.call kind.yulOpcode argExprs)

/-- Canonical `ECM.ExternalCallModule` representing a low-level EVM call opcode
(`call`, `staticcall`, or `delegatecall`) bound to `resultVar`. -/
def canonicalLowLevelCallModule
    (kind : CanonicalLowLevelCallKind)
    (resultVar : String) : ECM.ExternalCallModule where
  name := s!"canonical_low_level_{kind.yulOpcode}"
  onFailure := .bindZero -- binds the success flag; nothing reverts by itself
  numArgs := kind.numArgs
  resultVars := [resultVar]
  writesState := kind.writesState
  readsState := true
  compile := fun _ argExprs =>
    pure [canonicalLowLevelCallYulStmt kind resultVar argExprs]
  byteTransport := none
  axioms := []
  proofStatus := .assumed
  summaryName := kind.yulOpcode
  summarySelector := none
  summaryMutability := if kind.writesState then .call else .staticcall
  targetArg := some 1
  valueArg := match kind with
    | .call => some 2
    | .staticcall | .delegatecall => none

/-! ## Structural Metadata Lemmas for Canonical ECMs -/

/-- `canonicalTypedExternalCallModule` binds exactly `resultVars`. -/
@[simp] theorem canonicalTypedExternalCallModule_resultVars
    (calleeName : String) (argCount : Nat) (resultVars : List String)
    (isPayable isStatic : Bool) :
    (canonicalTypedExternalCallModule calleeName argCount resultVars isPayable isStatic).resultVars =
      resultVars := rfl

/-- `canonicalTypedExternalCallModule` expects `argCount` arguments. -/
@[simp] theorem canonicalTypedExternalCallModule_numArgs
    (calleeName : String) (argCount : Nat) (resultVars : List String)
    (isPayable isStatic : Bool) :
    (canonicalTypedExternalCallModule calleeName argCount resultVars isPayable isStatic).numArgs =
      argCount := rfl

/-- `canonicalTypedExternalCallModule` writes state iff `isStatic = false`. -/
@[simp] theorem canonicalTypedExternalCallModule_writesState
    (calleeName : String) (argCount : Nat) (resultVars : List String)
    (isPayable isStatic : Bool) :
    (canonicalTypedExternalCallModule calleeName argCount resultVars isPayable isStatic).writesState =
      !isStatic := rfl

/-- `canonicalTryExternalCallModule` binds `successVar :: resultVars`. -/
@[simp] theorem canonicalTryExternalCallModule_resultVars
    (calleeName : String) (argCount : Nat) (successVar : String)
    (resultVars : List String) (isPayable : Bool) :
    (canonicalTryExternalCallModule calleeName argCount successVar resultVars isPayable).resultVars =
      successVar :: resultVars := rfl

/-- `canonicalTryExternalCallModule` expects `argCount` arguments. -/
@[simp] theorem canonicalTryExternalCallModule_numArgs
    (calleeName : String) (argCount : Nat) (successVar : String)
    (resultVars : List String) (isPayable : Bool) :
    (canonicalTryExternalCallModule calleeName argCount successVar resultVars isPayable).numArgs =
      argCount := rfl

/-- `canonicalTryExternalCallModule` is always classified as state-writing. -/
@[simp] theorem canonicalTryExternalCallModule_writesState
    (calleeName : String) (argCount : Nat) (successVar : String)
    (resultVars : List String) (isPayable : Bool) :
    (canonicalTryExternalCallModule calleeName argCount successVar resultVars isPayable).writesState =
      true := rfl

/-- `canonicalLowLevelCallModule` binds the single success flag variable `[resultVar]`. -/
@[simp] theorem canonicalLowLevelCallModule_resultVars
    (kind : CanonicalLowLevelCallKind) (resultVar : String) :
    (canonicalLowLevelCallModule kind resultVar).resultVars = [resultVar] := rfl

/-- `canonicalLowLevelCallModule` expects `kind.numArgs` arguments. -/
@[simp] theorem canonicalLowLevelCallModule_numArgs
    (kind : CanonicalLowLevelCallKind) (resultVar : String) :
    (canonicalLowLevelCallModule kind resultVar).numArgs = kind.numArgs := rfl

/-- `canonicalLowLevelCallModule` writes state iff the call kind is not `.staticcall`
(`call` and `delegatecall` write state; `staticcall` does not). -/
theorem canonicalLowLevelCallModule_writesState_iff
    (kind : CanonicalLowLevelCallKind) (resultVar : String) :
    (canonicalLowLevelCallModule kind resultVar).writesState = true ↔
      kind ≠ .staticcall := by
  cases kind <;> simp [canonicalLowLevelCallModule, CanonicalLowLevelCallKind.writesState]

/-- `canonicalLowLevelCallModule` is read-only (`writesState = false`) iff `kind = .staticcall`. -/
theorem canonicalLowLevelCallModule_writesState_eq_false_iff
    (kind : CanonicalLowLevelCallKind) (resultVar : String) :
    (canonicalLowLevelCallModule kind resultVar).writesState = false ↔
      kind = .staticcall := by
  cases kind <;> simp [canonicalLowLevelCallModule, CanonicalLowLevelCallKind.writesState]

/-! ## Canonical Statement Lowering -/

/-- Extract the canonical low-level call kind and operand list from an `Expr`,
or `none` if the expression is not a raw low-level call (`call`, `staticcall`,
or `delegatecall`). -/
def lowLevelCallExprInfo? : Expr → Option (CanonicalLowLevelCallKind × List Expr)
  | .call gas target val inOffset inSize outOffset outSize =>
      some (.call, [gas, target, val, inOffset, inSize, outOffset, outSize])
  | .staticcall gas target inOffset inSize outOffset outSize =>
      some (.staticcall, [gas, target, inOffset, inSize, outOffset, outSize])
  | .delegatecall gas target inOffset inSize outOffset outSize =>
      some (.delegatecall, [gas, target, inOffset, inSize, outOffset, outSize])
  | _ => none

/-- Predicate recognizing whether an expression is a raw low-level call
(`call`, `staticcall`, or `delegatecall`). -/
def isRawLowLevelCallExpr (e : Expr) : Bool :=
  (lowLevelCallExprInfo? e).isSome

/-- Predicate recognizing whether a statement has a raw `.externalCallBind` or
`.tryExternalCallBind` constructor at its head. -/
def isRawExternalCallBindHead : Stmt → Bool
  | .externalCallBind _ _ _ => true
  | .tryExternalCallBind _ _ _ _ => true
  | _ => false

/-- Predicate recognizing whether a statement is a raw low-level call (`call`,
`staticcall`, or `delegatecall`) bound via `Stmt.letVar`. -/
def isRawLowLevelCallLetHead : Stmt → Bool
  | .letVar _ value => isRawLowLevelCallExpr value
  | _ => false

/-- Lower a `Stmt.letVar` binding whose RHS is a low-level call expression into
its canonical `Stmt.ecm` representation, or leave other `letVar` bindings unchanged. -/
def canonicalizeLowLevelCallLet (resultVar : String) (value : Expr) : Stmt :=
  match lowLevelCallExprInfo? value with
  | some (kind, args) =>
      .ecm (canonicalLowLevelCallModule kind resultVar) args
  | none =>
      .letVar resultVar value

/-- Lower `Stmt.externalCallBind`, `Stmt.tryExternalCallBind`, and `Stmt.letVar`
low-level call bindings (`Expr.call`, `Expr.staticcall`, `Expr.delegatecall`)
into canonical `Stmt.ecm` statements. -/
def canonicalizeExternalCallStmt : Stmt → Stmt
  | .externalCallBind resultVars externalName args =>
      .ecm (canonicalTypedExternalCallModule externalName args.length resultVars) args
  | .tryExternalCallBind successVar resultVars externalName args =>
      .ecm (canonicalTryExternalCallModule externalName args.length successVar resultVars) args
  | .letVar resultVar value =>
      canonicalizeLowLevelCallLet resultVar value
  | stmt => stmt

/-- Pointwise canonicalization of a statement list. -/
def canonicalizeExternalCallStmtList (stmts : List Stmt) : List Stmt :=
  stmts.map canonicalizeExternalCallStmt

/-- `canonicalizeLowLevelCallLet` is fixed by `canonicalizeExternalCallStmt`. -/
private theorem canonicalizeExternalCallStmt_canonicalizeLowLevelCallLet
    (resultVar : String) (value : Expr) :
    canonicalizeExternalCallStmt (canonicalizeLowLevelCallLet resultVar value) =
      canonicalizeLowLevelCallLet resultVar value := by
  unfold canonicalizeLowLevelCallLet
  cases h : lowLevelCallExprInfo? value with
  | none =>
      simp [canonicalizeExternalCallStmt, canonicalizeLowLevelCallLet, h]
  | some info =>
      rcases info with ⟨kind, args⟩
      rfl

/-- `canonicalizeExternalCallStmt` is idempotent on all statements. -/
@[simp] theorem canonicalizeExternalCallStmt_idempotent (s : Stmt) :
    canonicalizeExternalCallStmt (canonicalizeExternalCallStmt s) =
      canonicalizeExternalCallStmt s := by
  cases s with
  | letVar name value =>
      exact canonicalizeExternalCallStmt_canonicalizeLowLevelCallLet name value
  | _ =>
      rfl

/-- `canonicalizeExternalCallStmtList` is idempotent on all statement lists. -/
@[simp] theorem canonicalizeExternalCallStmtList_idempotent (stmts : List Stmt) :
    canonicalizeExternalCallStmtList (canonicalizeExternalCallStmtList stmts) =
      canonicalizeExternalCallStmtList stmts := by
  induction stmts with
  | nil => rfl
  | cons s rest ih =>
      simp [canonicalizeExternalCallStmtList, canonicalizeExternalCallStmt_idempotent]

/-- `canonicalizeLowLevelCallLet` never produces a raw external-call-bind head. -/
private theorem isRawExternalCallBindHead_canonicalizeLowLevelCallLet
    (resultVar : String) (value : Expr) :
    isRawExternalCallBindHead (canonicalizeLowLevelCallLet resultVar value) = false := by
  unfold canonicalizeLowLevelCallLet
  cases lowLevelCallExprInfo? value <;> rfl

/-- `canonicalizeExternalCallStmt` eliminates raw `.externalCallBind` and
`.tryExternalCallBind` constructors at the statement head. -/
@[simp] theorem canonicalizeExternalCallStmt_eliminates_raw_externalCallBind (s : Stmt) :
    isRawExternalCallBindHead (canonicalizeExternalCallStmt s) = false := by
  cases s with
  | letVar name value =>
      exact isRawExternalCallBindHead_canonicalizeLowLevelCallLet name value
  | _ =>
      rfl

/-- `canonicalizeLowLevelCallLet` eliminates raw low-level call `letVar` heads. -/
private theorem isRawLowLevelCallLetHead_canonicalizeLowLevelCallLet
    (resultVar : String) (value : Expr) :
    isRawLowLevelCallLetHead (canonicalizeLowLevelCallLet resultVar value) = false := by
  unfold canonicalizeLowLevelCallLet
  cases h : lowLevelCallExprInfo? value with
  | none =>
      simp [isRawLowLevelCallLetHead, isRawLowLevelCallExpr, h]
  | some info =>
      rcases info with ⟨kind, args⟩
      rfl

/-- `canonicalizeExternalCallStmt` also eliminates raw low-level call `letVar`
bindings at the statement head. -/
@[simp] theorem canonicalizeExternalCallStmt_eliminates_raw_lowLevelCallLet (s : Stmt) :
    isRawLowLevelCallLetHead (canonicalizeExternalCallStmt s) = false := by
  cases s with
  | letVar name value =>
      exact isRawLowLevelCallLetHead_canonicalizeLowLevelCallLet name value
  | _ =>
      rfl

/-- `canonicalizeLowLevelCallLet` preserves bound variable names (`[resultVar]`). -/
private theorem collectStmtBindNames_canonicalizeLowLevelCallLet
    (resultVar : String) (value : Expr) :
    collectStmtBindNames (canonicalizeLowLevelCallLet resultVar value) = [resultVar] := by
  unfold canonicalizeLowLevelCallLet
  cases h : lowLevelCallExprInfo? value with
  | none =>
      simp [collectStmtBindNames]
  | some info =>
      rcases info with ⟨kind, args⟩
      simp [collectStmtBindNames]

/-- Canonicalizing a statement preserves its bound variable names (`collectStmtBindNames`). -/
@[simp] theorem collectStmtBindNames_canonicalizeExternalCallStmt (s : Stmt) :
    collectStmtBindNames (canonicalizeExternalCallStmt s) = collectStmtBindNames s := by
  cases s with
  | externalCallBind resultVars externalName args =>
      simp [canonicalizeExternalCallStmt, collectStmtBindNames]
  | tryExternalCallBind successVar resultVars externalName args =>
      simp [canonicalizeExternalCallStmt, collectStmtBindNames]
  | letVar name value =>
      simpa [canonicalizeExternalCallStmt, collectStmtBindNames] using
        collectStmtBindNames_canonicalizeLowLevelCallLet name value
  | _ =>
      rfl

/-- Canonicalizing a statement preserves `stmtNextScope` identically. -/
@[simp] theorem stmtNextScope_canonicalizeExternalCallStmt
    (scope : List String) (s : Stmt) :
    stmtNextScope scope (canonicalizeExternalCallStmt s) = stmtNextScope scope s := by
  simp [stmtNextScope, collectStmtBindNames_canonicalizeExternalCallStmt]

/-! ## Canonical Compilation and Layer-2 Step Bridge Instantiations -/

/-- `compileCanonical` for `canonicalTypedExternalCallModule` always succeeds and emits
the singleton `canonicalTypedExternalCallYulStmt`. -/
@[simp] theorem compileCanonical_canonicalTypedExternalCallModule
    (calleeName : String) (argCount : Nat) (resultVars : List String)
    (isPayable isStatic : Bool) (ctx : ECM.CompilationContext) (argExprs : List YulExpr) :
    (canonicalTypedExternalCallModule calleeName argCount resultVars isPayable isStatic).compileCanonical
      ctx argExprs =
      Except.ok [canonicalTypedExternalCallYulStmt calleeName resultVars argExprs] := rfl

/-- `compileCanonical` for `canonicalTryExternalCallModule` always succeeds and emits
the singleton `canonicalTryExternalCallYulStmt`. -/
@[simp] theorem compileCanonical_canonicalTryExternalCallModule
    (calleeName : String) (argCount : Nat) (successVar : String)
    (resultVars : List String) (isPayable : Bool)
    (ctx : ECM.CompilationContext) (argExprs : List YulExpr) :
    (canonicalTryExternalCallModule calleeName argCount successVar resultVars isPayable).compileCanonical
      ctx argExprs =
      Except.ok [canonicalTryExternalCallYulStmt calleeName successVar resultVars argExprs] := rfl

/-- `compileCanonical` for `canonicalLowLevelCallModule` always succeeds and emits
the singleton `canonicalLowLevelCallYulStmt`. -/
@[simp] theorem compileCanonical_canonicalLowLevelCallModule
    (kind : CanonicalLowLevelCallKind) (resultVar : String)
    (ctx : ECM.CompilationContext) (argExprs : List YulExpr) :
    (canonicalLowLevelCallModule kind resultVar).compileCanonical ctx argExprs =
      Except.ok [canonicalLowLevelCallYulStmt kind resultVar argExprs] := rfl

/-- Shape decomposition for `CompilationModel.compileStmt` on `Stmt.ecm mod args`
under an explicit internal-function environment. -/
theorem compileStmt_canonical_ecm_shape_with_internals
    {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    {scope : List String} {internalFunctions : List FunctionSpec}
    {mod : ECM.ExternalCallModule} {args : List Expr}
    {compiledIR : List YulStmt}
    (hok :
      CompilationModel.compileStmt fields events errors .calldata [] false scope []
        (Stmt.ecm mod args) internalFunctions = Except.ok compiledIR) :
    args.length = mod.numArgs ∧
    ∃ argExprs generated,
      CompilationModel.compileExprListWithInternals fields .calldata internalFunctions args =
        Except.ok argExprs ∧
      mod.compileCanonical { isDynamicFromCalldata := true } argExprs =
        Except.ok generated := by
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    bind, Except.bind] at hok
  by_cases hlen : args.length = mod.numArgs
  · refine ⟨hlen, ?_⟩
    have hne : (args.length != mod.numArgs) = false := by simp [hlen]
    have hctx :
        ({ isDynamicFromCalldata := (DynamicDataSource.calldata == DynamicDataSource.calldata) } :
          ECM.CompilationContext) = { isDynamicFromCalldata := true } := rfl
    simp only [hne, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, hctx] at hok
    cases hargs :
        CompilationModel.compileExprListWithInternals fields .calldata internalFunctions args with
    | error e =>
        simp [hargs] at hok
    | ok argExprs =>
        simp only [hargs] at hok
        cases hgen :
            mod.compileCanonical { isDynamicFromCalldata := true } argExprs with
        | error e =>
            simp [hgen] at hok
        | ok generated =>
            exact ⟨argExprs, generated, rfl, hgen⟩
  · have hne : (args.length != mod.numArgs) = true := by simp [hlen]
    simp [hne, throw] at hok

/-- Generic `compileStmt` success lemma for any `Stmt.ecm mod args` whose argument count
matches `mod.numArgs`, whose argument expressions compile, and whose `compileCanonical`
succeeds. -/
theorem compileStmt_ecm_ok_of_compileCanonical
    {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    {scope : List String} {internalFunctions : List FunctionSpec}
    {mod : ECM.ExternalCallModule} {args : List Expr}
    {argExprs : List YulExpr} {generated : List YulStmt}
    (hlen : args.length = mod.numArgs)
    (hargs :
      CompilationModel.compileExprListWithInternals fields .calldata internalFunctions args =
        Except.ok argExprs)
    (hcanonical :
      mod.compileCanonical { isDynamicFromCalldata := true } argExprs =
        Except.ok generated) :
    ∃ compiledIR,
      CompilationModel.compileStmt fields events errors .calldata [] false scope []
        (Stmt.ecm mod args) internalFunctions = Except.ok compiledIR := by
  cases h :
      CompilationModel.compileStmt fields events errors .calldata [] false scope []
        (Stmt.ecm mod args) internalFunctions with
  | ok compiledIR =>
      exact ⟨compiledIR, rfl⟩
  | error err =>
      have hne : (args.length != mod.numArgs) = false := by simp [hlen]
      have hctx :
          ({ isDynamicFromCalldata := (DynamicDataSource.calldata == DynamicDataSource.calldata) } :
            ECM.CompilationContext) = { isDynamicFromCalldata := true } := rfl
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        bind, Except.bind, hne, Bool.false_eq_true, ↓reduceIte,
        pure, Except.pure, hctx, hargs, hcanonical] at h
      cases h

/-- Lightweight Layer-2 compiled-step interface for `Stmt.ecm` parameterized over
an abstract post-scope step-alignment relation `stepAlign`. -/
structure CanonicalCompiledStmtStepWithInternals
    (spec : CompilationModel)
    (fields : List Field)
    (scope : List String)
    (stmt : Stmt)
    (compiledIR : List YulStmt)
    (stepAlign : List String → Stmt → List YulStmt → Prop) : Prop where
  compileOk :
    CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      stmt spec.functions = Except.ok compiledIR
  preserves :
    stepAlign (stmtNextScope scope stmt) stmt compiledIR

/-- Lightweight Layer-2 head-step bridge for an `ECM.ExternalCallModule` statement
compiled under `spec.functions`, isolating compilation and canonical shape extraction
from the semantic step alignment `stepAlign`. -/
structure CanonicalEcmHeadStepBridgeWithInternals
    (spec : CompilationModel)
    (fields : List Field)
    (scope : List String)
    (mod : ECM.ExternalCallModule)
    (args : List Expr)
    (stepAlign : List String → Stmt → List YulStmt → Prop) : Prop where
  compile :
    ∃ compiledIR,
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.ecm mod args) spec.functions = Except.ok compiledIR
  bridge :
    ∀ {compiledIR : List YulStmt} {argExprs : List YulExpr} {generated : List YulStmt},
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.ecm mod args) spec.functions = Except.ok compiledIR →
      args.length = mod.numArgs →
      CompilationModel.compileExprListWithInternals fields .calldata spec.functions args =
        Except.ok argExprs →
      mod.compileCanonical { isDynamicFromCalldata := true } argExprs =
        Except.ok generated →
      stepAlign (stmtNextScope scope (Stmt.ecm mod args)) (Stmt.ecm mod args) compiledIR

/-- Construct `CanonicalCompiledStmtStepWithInternals` for `Stmt.ecm mod args` from
compilation and the module's step alignment. -/
theorem canonicalCompiledStmtStepWithInternals_ecm
    {spec : CompilationModel} {fields : List Field}
    {scope : List String} {mod : ECM.ExternalCallModule} {args : List Expr}
    {compiledIR : List YulStmt} {argExprs : List YulExpr} {generated : List YulStmt}
    {stepAlign : List String → Stmt → List YulStmt → Prop}
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.ecm mod args) spec.functions = Except.ok compiledIR)
    (_hlen : args.length = mod.numArgs)
    (_hargCompile :
      CompilationModel.compileExprListWithInternals fields .calldata spec.functions args =
        Except.ok argExprs)
    (_hcanonical :
      mod.compileCanonical { isDynamicFromCalldata := true } argExprs =
        Except.ok generated)
    (hbridge :
      stepAlign (stmtNextScope scope (Stmt.ecm mod args)) (Stmt.ecm mod args) compiledIR) :
    CanonicalCompiledStmtStepWithInternals
      spec fields scope (Stmt.ecm mod args) compiledIR stepAlign :=
  { compileOk := hcompile, preserves := hbridge }

/-- Package a `CanonicalEcmHeadStepBridgeWithInternals` into the Layer-2
`CanonicalCompiledStmtStepWithInternals` head-step interface by extracting the
`Stmt.ecm` compilation shape invariants. -/
theorem canonicalCompiledStmtStepWithInternals_of_ecmBridge
    {spec : CompilationModel} {fields : List Field}
    {scope : List String} {mod : ECM.ExternalCallModule} {args : List Expr}
    {stepAlign : List String → Stmt → List YulStmt → Prop}
    (hbridge :
      CanonicalEcmHeadStepBridgeWithInternals spec fields scope mod args stepAlign) :
    ∃ compiledIR,
      CanonicalCompiledStmtStepWithInternals
        spec fields scope (Stmt.ecm mod args) compiledIR stepAlign := by
  rcases hbridge.compile with ⟨compiledIR, hcompile⟩
  obtain ⟨hlen, argExprs, generated, hargCompile, hcanonical⟩ :=
    compileStmt_canonical_ecm_shape_with_internals hcompile
  exact ⟨compiledIR,
    canonicalCompiledStmtStepWithInternals_ecm
      hcompile hlen hargCompile hcanonical
      (hbridge.bridge hcompile hlen hargCompile hcanonical)⟩

/-- Instantiate `CanonicalEcmHeadStepBridgeWithInternals` for
`canonicalTypedExternalCallModule` from compiled argument expressions and the
step-alignment obligation. -/
theorem ecmHeadStepBridgeWithInternals_canonicalTypedExternalCallModule
    {spec : CompilationModel} {fields : List Field}
    {scope : List String} {calleeName : String} {resultVars : List String}
    {isPayable isStatic : Bool} {args : List Expr} {argExprs : List YulExpr}
    {stepAlign : List String → Stmt → List YulStmt → Prop}
    (hargs :
      CompilationModel.compileExprListWithInternals fields .calldata spec.functions args =
        Except.ok argExprs)
    (halign :
      ∀ {compiledIR : List YulStmt},
        CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
          (Stmt.ecm
            (canonicalTypedExternalCallModule calleeName args.length resultVars isPayable isStatic)
            args)
          spec.functions = Except.ok compiledIR →
        stepAlign
          (stmtNextScope scope
            (Stmt.ecm
              (canonicalTypedExternalCallModule calleeName args.length resultVars isPayable isStatic)
              args))
          (Stmt.ecm
            (canonicalTypedExternalCallModule calleeName args.length resultVars isPayable isStatic)
            args)
          compiledIR) :
    CanonicalEcmHeadStepBridgeWithInternals spec fields scope
      (canonicalTypedExternalCallModule calleeName args.length resultVars isPayable isStatic)
      args stepAlign where
  compile :=
    compileStmt_ecm_ok_of_compileCanonical rfl hargs
      (compileCanonical_canonicalTypedExternalCallModule
        calleeName args.length resultVars isPayable isStatic _ argExprs)
  bridge hcompile _ _ _ := halign hcompile

/-- Layer-2 compiled-step theorem for `canonicalTypedExternalCallModule`. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_canonicalTypedExternalCallModule
    {spec : CompilationModel} {fields : List Field}
    {scope : List String} {calleeName : String} {resultVars : List String}
    {isPayable isStatic : Bool} {args : List Expr}
    {compiledIR : List YulStmt} {argExprs : List YulExpr}
    {stepAlign : List String → Stmt → List YulStmt → Prop}
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.ecm
          (canonicalTypedExternalCallModule calleeName args.length resultVars isPayable isStatic)
          args)
        spec.functions = Except.ok compiledIR)
    (hargs :
      CompilationModel.compileExprListWithInternals fields .calldata spec.functions args =
        Except.ok argExprs)
    (halign :
      stepAlign
        (stmtNextScope scope
          (Stmt.ecm
            (canonicalTypedExternalCallModule calleeName args.length resultVars isPayable isStatic)
            args))
        (Stmt.ecm
          (canonicalTypedExternalCallModule calleeName args.length resultVars isPayable isStatic)
          args)
        compiledIR) :
    CanonicalCompiledStmtStepWithInternals spec fields scope
      (Stmt.ecm
        (canonicalTypedExternalCallModule calleeName args.length resultVars isPayable isStatic)
        args)
      compiledIR stepAlign := by
  exact canonicalCompiledStmtStepWithInternals_ecm
    hcompile rfl hargs
    (compileCanonical_canonicalTypedExternalCallModule
      calleeName args.length resultVars isPayable isStatic _ argExprs)
    halign

/-- Instantiate `CanonicalEcmHeadStepBridgeWithInternals` for
`canonicalTryExternalCallModule` from compiled argument expressions and the
step-alignment obligation. -/
theorem ecmHeadStepBridgeWithInternals_canonicalTryExternalCallModule
    {spec : CompilationModel} {fields : List Field}
    {scope : List String} {calleeName : String} {successVar : String}
    {resultVars : List String} {isPayable : Bool}
    {args : List Expr} {argExprs : List YulExpr}
    {stepAlign : List String → Stmt → List YulStmt → Prop}
    (hargs :
      CompilationModel.compileExprListWithInternals fields .calldata spec.functions args =
        Except.ok argExprs)
    (halign :
      ∀ {compiledIR : List YulStmt},
        CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
          (Stmt.ecm
            (canonicalTryExternalCallModule calleeName args.length successVar resultVars isPayable)
            args)
          spec.functions = Except.ok compiledIR →
        stepAlign
          (stmtNextScope scope
            (Stmt.ecm
              (canonicalTryExternalCallModule calleeName args.length successVar resultVars isPayable)
              args))
          (Stmt.ecm
            (canonicalTryExternalCallModule calleeName args.length successVar resultVars isPayable)
            args)
          compiledIR) :
    CanonicalEcmHeadStepBridgeWithInternals spec fields scope
      (canonicalTryExternalCallModule calleeName args.length successVar resultVars isPayable)
      args stepAlign where
  compile :=
    compileStmt_ecm_ok_of_compileCanonical rfl hargs
      (compileCanonical_canonicalTryExternalCallModule
        calleeName args.length successVar resultVars isPayable _ argExprs)
  bridge hcompile _ _ _ := halign hcompile

/-- Layer-2 compiled-step theorem for `canonicalTryExternalCallModule`. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_canonicalTryExternalCallModule
    {spec : CompilationModel} {fields : List Field}
    {scope : List String} {calleeName : String} {successVar : String}
    {resultVars : List String} {isPayable : Bool} {args : List Expr}
    {compiledIR : List YulStmt} {argExprs : List YulExpr}
    {stepAlign : List String → Stmt → List YulStmt → Prop}
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.ecm
          (canonicalTryExternalCallModule calleeName args.length successVar resultVars isPayable)
          args)
        spec.functions = Except.ok compiledIR)
    (hargs :
      CompilationModel.compileExprListWithInternals fields .calldata spec.functions args =
        Except.ok argExprs)
    (halign :
      stepAlign
        (stmtNextScope scope
          (Stmt.ecm
            (canonicalTryExternalCallModule calleeName args.length successVar resultVars isPayable)
            args))
        (Stmt.ecm
          (canonicalTryExternalCallModule calleeName args.length successVar resultVars isPayable)
          args)
        compiledIR) :
    CanonicalCompiledStmtStepWithInternals spec fields scope
      (Stmt.ecm
        (canonicalTryExternalCallModule calleeName args.length successVar resultVars isPayable)
        args)
      compiledIR stepAlign := by
  exact canonicalCompiledStmtStepWithInternals_ecm
    hcompile rfl hargs
    (compileCanonical_canonicalTryExternalCallModule
      calleeName args.length successVar resultVars isPayable _ argExprs)
    halign

/-- Instantiate `CanonicalEcmHeadStepBridgeWithInternals` for
`canonicalLowLevelCallModule` from argument arity, compiled argument expressions,
and the step-alignment obligation. -/
theorem ecmHeadStepBridgeWithInternals_canonicalLowLevelCallModule
    {spec : CompilationModel} {fields : List Field}
    {scope : List String} {kind : CanonicalLowLevelCallKind} {resultVar : String}
    {args : List Expr} {argExprs : List YulExpr}
    {stepAlign : List String → Stmt → List YulStmt → Prop}
    (hlen : args.length = kind.numArgs)
    (hargs :
      CompilationModel.compileExprListWithInternals fields .calldata spec.functions args =
        Except.ok argExprs)
    (halign :
      ∀ {compiledIR : List YulStmt},
        CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
          (Stmt.ecm (canonicalLowLevelCallModule kind resultVar) args)
          spec.functions = Except.ok compiledIR →
        stepAlign
          (stmtNextScope scope (Stmt.ecm (canonicalLowLevelCallModule kind resultVar) args))
          (Stmt.ecm (canonicalLowLevelCallModule kind resultVar) args)
          compiledIR) :
    CanonicalEcmHeadStepBridgeWithInternals spec fields scope
      (canonicalLowLevelCallModule kind resultVar) args stepAlign where
  compile :=
    compileStmt_ecm_ok_of_compileCanonical hlen hargs
      (compileCanonical_canonicalLowLevelCallModule kind resultVar _ argExprs)
  bridge hcompile _ _ _ := halign hcompile

/-- Layer-2 compiled-step theorem for `canonicalLowLevelCallModule`. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_canonicalLowLevelCallModule
    {spec : CompilationModel} {fields : List Field}
    {scope : List String} {kind : CanonicalLowLevelCallKind} {resultVar : String}
    {args : List Expr} {compiledIR : List YulStmt} {argExprs : List YulExpr}
    {stepAlign : List String → Stmt → List YulStmt → Prop}
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.ecm (canonicalLowLevelCallModule kind resultVar) args)
        spec.functions = Except.ok compiledIR)
    (hlen : args.length = kind.numArgs)
    (hargs :
      CompilationModel.compileExprListWithInternals fields .calldata spec.functions args =
        Except.ok argExprs)
    (halign :
      stepAlign
        (stmtNextScope scope (Stmt.ecm (canonicalLowLevelCallModule kind resultVar) args))
        (Stmt.ecm (canonicalLowLevelCallModule kind resultVar) args)
        compiledIR) :
    CanonicalCompiledStmtStepWithInternals spec fields scope
      (Stmt.ecm (canonicalLowLevelCallModule kind resultVar) args)
      compiledIR stepAlign := by
  exact canonicalCompiledStmtStepWithInternals_ecm
    hcompile hlen hargs
    (compileCanonical_canonicalLowLevelCallModule kind resultVar _ argExprs)
    halign

end Compiler.Proofs.IRGeneration
