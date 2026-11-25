import Compiler.CompilationModel.Dispatch
import Compiler.Proofs.IRGeneration.FunctionShape
import Compiler.Proofs.IRGeneration.FunctionBody
import Compiler.Proofs.IRGeneration.GenericInduction
import Compiler.Proofs.IRGeneration.GenericInduction.EventBridge
import Compiler.Proofs.IRGeneration.ParamLoading
import Compiler.Proofs.IRGeneration.SourceSemantics
import Compiler.Proofs.IRGeneration.SupportedSpec
import Compiler.Proofs.YulGeneration.IRFuel

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

namespace Function

/-- Generic transaction well-formedness needed by the current param-loading proof:
the ABI-style calldata byte size must not wrap modulo the EVM word modulus. -/
def TxCalldataSizeFitsEvm (tx : IRTransaction) : Prop :=
  4 + tx.args.length * 32 < Compiler.Constants.evmModulus

/-- Constructor calldata is deploy-time ABI data without the 4-byte selector
prefix used by external function calls. -/
def TxConstructorCalldataSizeFitsEvm (tx : IRTransaction) : Prop :=
  tx.args.length * 32 < Compiler.Constants.evmModulus

/-- Source-side transaction context stores addresses as 160-bit values and the
remaining observed environment fields as `Uint256`s. The generic Layer-2 proof
therefore needs the IR transaction payload to already fit those bounds. -/
def TxContextNormalized (tx : IRTransaction) : Prop :=
  tx.sender < Compiler.Constants.addressModulus ∧
  tx.thisAddress < Compiler.Constants.addressModulus ∧
  tx.msgValue < Compiler.Constants.evmModulus ∧
  tx.blockTimestamp < Compiler.Constants.evmModulus ∧
  tx.blockNumber < Compiler.Constants.evmModulus ∧
  tx.chainId < Compiler.Constants.evmModulus ∧
  tx.blobBaseFee < Compiler.Constants.evmModulus ∧
  tx.txOrigin < Compiler.Constants.addressModulus

def compiledFunctionIR
    (selector : Nat) (spec : FunctionSpec) (returns : List ParamType) (bodyStmts : List YulStmt) :
    IRFunction :=
  { name := spec.name
    selector := selector
    params := spec.params.map Param.toIRParam
    ret := match returns with
      | [single] => single.toIRType
      | _ => IRType.unit
    payable := spec.isPayable
    body := genParamLoads spec.params ++ bodyStmts }

def prebindRawArgs (state : IRState) (params : List Param) : IRState :=
  (params.map Param.toIRParam).zip state.calldata |>.foldl
    (fun s (p, v) => s.setVar p.name v)
    state

theorem prebindRawArgs_revertData (state : IRState) (params : List Param) :
    (prebindRawArgs state params).revertData = state.revertData := by
  unfold prebindRawArgs
  generalize (params.map Param.toIRParam).zip state.calldata = l
  induction l generalizing state with
  | nil => rfl
  | cons p rest ih => exact ih (state.setVar p.1.name p.2)

def rawArgBindings (params : List Param) (args : List Nat) : List (String × Nat) :=
  ((params.map Param.toIRParam).zip args).map (fun entry => (entry.1.name, entry.2))

private theorem yulStmtList_length_le_sizeOf : (stmts : List YulStmt) → stmts.length ≤ sizeOf stmts
  | [] => by simp
  | _ :: rest => by
      have hrest := yulStmtList_length_le_sizeOf rest
      simp
      omega

private theorem compiledFunctionIR_body_length_le_sizeOf
    (selector : Nat) (spec : FunctionSpec) (returns : List ParamType) (bodyStmts : List YulStmt) :
    (compiledFunctionIR selector spec returns bodyStmts).body.length + 1 ≤
      sizeOf (compiledFunctionIR selector spec returns bodyStmts).body + 1 := by
  simpa [compiledFunctionIR] using Nat.add_le_add_right
    (yulStmtList_length_le_sizeOf (genParamLoads spec.params ++ bodyStmts)) 1

private theorem yulStmtList_extraFuel_append_ge
    (pre body : List YulStmt) :
    sizeOf (pre ++ body) - (pre ++ body).length ≥ sizeOf body - body.length := by
  induction pre with
  | nil =>
      simp
  | cons stmt rest ih =>
      simp [List.length_append] at ih ⊢
      omega

@[simp] theorem prebindRawArgs_calldata (state : IRState) (params : List Param) :
    (prebindRawArgs state params).calldata = state.calldata := by
  unfold prebindRawArgs
  induction (params.map Param.toIRParam).zip state.calldata generalizing state with
  | nil =>
      rfl
  | cons entry rest ih =>
      simpa [List.foldl, IRState.setVar] using ih (state.setVar entry.1.name entry.2)

theorem prebindRawArgs_exact_rawArgBindings
    {state : IRState}
    {bindings0 : List (String × Nat)}
    (hexact : FunctionBody.bindingsExactlyMatchIRVars bindings0 state)
    (params : List Param) :
    FunctionBody.bindingsExactlyMatchIRVars
      ((rawArgBindings params state.calldata).foldl
        (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) bindings0)
      (prebindRawArgs state params) := by
  unfold prebindRawArgs rawArgBindings
  induction (List.zip (List.map Param.toIRParam params) state.calldata) generalizing bindings0 state with
  | nil =>
      simpa
  | cons entry rest ih =>
      have hstep :
          FunctionBody.bindingsExactlyMatchIRVars
            (SourceSemantics.bindValue bindings0 entry.1.name entry.2)
            (state.setVar entry.1.name entry.2) :=
        FunctionBody.bindingsExactlyMatchIRVars_setVar_bindValue hexact entry.1.name entry.2
      simpa [List.foldl, SourceSemantics.bindValue] using
        ih (bindings0 := SourceSemantics.bindValue bindings0 entry.1.name entry.2)
          (state := state.setVar entry.1.name entry.2) hstep

theorem rawArgBindings_names_of_length_le
    (params : List Param)
    (args : List Nat)
    (hlen : params.length ≤ args.length) :
    (rawArgBindings params args).map Prod.fst = params.map Param.name := by
  induction params generalizing args with
  | nil =>
      simp [rawArgBindings]
  | cons param rest ih =>
      cases args with
      | nil =>
          cases Nat.not_succ_le_zero _ hlen
      | cons arg restArgs =>
          have htail :
              (rawArgBindings rest restArgs).map Prod.fst = rest.map Param.name :=
            ih restArgs (Nat.le_of_succ_le_succ hlen)
          have hcons :
              param.toIRParam.name = param.name ∧
                (rawArgBindings rest restArgs).map Prod.fst = rest.map Param.name :=
            ⟨rfl, htail⟩
          simpa [rawArgBindings] using hcons

theorem rawArgBindings_names_of_bindSupportedParams
    {params : List Param}
    {args : List Nat}
    {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings) :
    (rawArgBindings params args).map Prod.fst = bindings.map Prod.fst := by
  rw [rawArgBindings_names_of_length_le params args
    (ParamLoading.bindSupportedParams_some_length hbind)]
  symm
  exact ParamLoading.bindSupportedParams_names hbind

def execResultToIRResult (initialState : IRState) : IRExecResult → IRResult
  | .continue s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .return v s =>
      { success := true
        returnValue := some v
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .stop s =>
      { success := true
        returnValue := none
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .revert s =>
      { success := false
        returnValue := none
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events
        revertData := s.revertData }

theorem compileFunctionSpec_ok_of_components
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec)
    {habi : spec.abiDecoding = .standard}
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (hvalidate : validateFunctionSpec spec = Except.ok ())
    (hreturns : functionReturns spec = Except.ok returns)
    (hbody :
      compileStmtList fields events errors .calldata [] false
        (spec.params.map (·.name)) [] spec.body = Except.ok bodyStmts) :
    compileFunctionSpec fields events errors [] selector spec =
      Except.ok (compiledFunctionIR selector spec returns bodyStmts) := by
  unfold CompilationModel.compileFunctionSpec
  simp only [FunctionSpec.bindingParams, habi]
  rw [hvalidate, hreturns, FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hbody]
  rfl

/-- Populated-internal-table variant of `compileFunctionSpec_ok_of_components`.
The body equation and the enclosing function compilation must use the same
caller-supplied internal function table. -/
theorem compileFunctionSpec_ok_of_components_with_internals
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (internalFunctions : List FunctionSpec)
    (selector : Nat) (spec : FunctionSpec)
    {habi : spec.abiDecoding = .standard}
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (hvalidate : validateFunctionSpec spec = Except.ok ())
    (hreturns : functionReturns spec = Except.ok returns)
    (hbody :
      compileStmtList fields events errors .calldata [] false
        (spec.params.map (·.name)) [] spec.body internalFunctions = Except.ok bodyStmts) :
    compileFunctionSpec fields events errors [] selector spec
        (internalFunctions := internalFunctions) =
      Except.ok (compiledFunctionIR selector spec returns bodyStmts) := by
  unfold CompilationModel.compileFunctionSpec
  simp only [FunctionSpec.bindingParams, habi]
  rw [hvalidate, hreturns]
  change
    (do
      let compiledBody ←
        compileStmtList fields events errors .calldata [] false
          (spec.params.map (fun p : Param => p.name)) [] spec.body internalFunctions
      pure (compiledFunctionIR selector spec returns compiledBody)) = _
  rw [hbody]
  rfl

theorem compileFunctionSpec_ok_params
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (hcompile : compileFunctionSpec fields events errors [] selector spec = Except.ok irFn) :
    irFn.params = spec.params.map Param.toIRParam := by
  unfold CompilationModel.compileFunctionSpec at hcompile
  cases hvalidate : validateFunctionSpec spec
  · rw [hvalidate] at hcompile
    cases hcompile
  case ok _ =>
    cases hreturns : functionReturns spec
    · rw [hvalidate, hreturns] at hcompile
      cases hcompile
    case ok returns =>
      cases hbody :
          compileStmtList fields events errors .calldata [] false
            (spec.bindingParams.map (·.name)) [] spec.body
      · rw [hvalidate, hreturns, FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hbody] at hcompile
        cases hcompile
      case ok bodyStmts =>
        rw [hvalidate, hreturns, FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hbody] at hcompile
        injection hcompile with hEq
        simpa using congrArg IRFunction.params hEq.symm

theorem compileFunctionSpec_ok_selector
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (hcompile : compileFunctionSpec fields events errors [] selector spec = Except.ok irFn) :
    irFn.selector = selector := by
  unfold CompilationModel.compileFunctionSpec at hcompile
  cases hvalidate : validateFunctionSpec spec
  · rw [hvalidate] at hcompile
    cases hcompile
  case ok _ =>
    cases hreturns : functionReturns spec
    · rw [hvalidate, hreturns] at hcompile
      cases hcompile
    case ok returns =>
      cases hbody :
          compileStmtList fields events errors .calldata [] false
            (spec.bindingParams.map (·.name)) [] spec.body
      · rw [hvalidate, hreturns, FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hbody] at hcompile
        cases hcompile
      case ok bodyStmts =>
        rw [hvalidate, hreturns, FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hbody] at hcompile
        injection hcompile with hEq
        simpa using congrArg IRFunction.selector hEq.symm

theorem compileFunctionSpec_ok_payable
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (hcompile : compileFunctionSpec fields events errors [] selector spec = Except.ok irFn) :
    irFn.payable = spec.isPayable := by
  unfold CompilationModel.compileFunctionSpec at hcompile
  cases hvalidate : validateFunctionSpec spec
  · rw [hvalidate] at hcompile
    cases hcompile
  case ok _ =>
    cases hreturns : functionReturns spec
    · rw [hvalidate, hreturns] at hcompile
      cases hcompile
    case ok returns =>
      cases hbody :
          compileStmtList fields events errors .calldata [] false
            (spec.bindingParams.map (·.name)) [] spec.body
      · rw [hvalidate, hreturns, FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hbody] at hcompile
        cases hcompile
      case ok bodyStmts =>
        rw [hvalidate, hreturns, FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hbody] at hcompile
        injection hcompile with hEq
        simpa using congrArg IRFunction.payable hEq.symm

/-- Structural fields of a compiled function do not depend on whether its body
is compiled against an empty or populated internal-function table. -/
theorem compileFunctionSpec_ok_metadata_with_internals
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (internalFunctions : List FunctionSpec)
    (hcompile :
      compileFunctionSpec fields events errors [] selector spec
        (internalFunctions := internalFunctions) =
        Except.ok irFn) :
    irFn.params = spec.params.map Param.toIRParam ∧
      irFn.selector = selector ∧ irFn.payable = spec.isPayable := by
  unfold CompilationModel.compileFunctionSpec at hcompile
  cases hvalidate : validateFunctionSpec spec
  · rw [hvalidate] at hcompile
    cases hcompile
  case ok _ =>
    cases hreturns : functionReturns spec
    · rw [hvalidate, hreturns] at hcompile
      cases hcompile
    case ok returns =>
      cases hbody :
          compileStmtList fields events errors .calldata [] false
            (spec.bindingParams.map (·.name)) [] spec.body internalFunctions
      · rw [hvalidate, hreturns,
          FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList
            (internalFunctions := internalFunctions), hbody] at hcompile
        cases hcompile
      case ok bodyStmts =>
        rw [hvalidate, hreturns,
          FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList
            (internalFunctions := internalFunctions), hbody] at hcompile
        injection hcompile with hEq
        exact ⟨by simpa using congrArg IRFunction.params hEq.symm,
          by simpa using congrArg IRFunction.selector hEq.symm,
          by simpa using congrArg IRFunction.payable hEq.symm⟩

theorem compileFunctionSpec_ok_components
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec)
    {habi : spec.abiDecoding = .standard} (irFn : IRFunction)
    (hcompile : compileFunctionSpec fields events errors [] selector spec = Except.ok irFn) :
    ∃ returns bodyStmts,
      validateFunctionSpec spec = Except.ok () ∧
      functionReturns spec = Except.ok returns ∧
      compileStmtList fields events errors .calldata [] false
        (spec.params.map (·.name)) [] spec.body = Except.ok bodyStmts ∧
      irFn = compiledFunctionIR selector spec returns bodyStmts := by
  unfold CompilationModel.compileFunctionSpec at hcompile
  simp only [FunctionSpec.bindingParams, habi] at hcompile
  cases hvalidate : validateFunctionSpec spec
  · rw [hvalidate] at hcompile
    cases hcompile
  case ok _ =>
    cases hreturns : functionReturns spec
    · rw [hvalidate, hreturns] at hcompile
      cases hcompile
    case ok returns =>
      cases hbody :
          compileStmtList fields events errors .calldata [] false
            (spec.params.map (·.name)) [] spec.body
      · rw [hvalidate, hreturns, FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hbody] at hcompile
        cases hcompile
      case ok bodyStmts =>
        rw [hvalidate, hreturns, FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hbody] at hcompile
        injection hcompile with hEq
        refine ⟨returns, bodyStmts, ?_⟩
        exact ⟨by simpa using hvalidate, by simpa using hreturns,
          by simpa using hbody, hEq.symm⟩

theorem compileConstructor_some_ok_of_body
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (ctor : ConstructorSpec) (bodyStmts : List YulStmt)
      (hbody :
        compileStmtList fields events errors .memory [] false
          (constructorBodyScope ctor.params) [] ctor.body [] = Except.ok bodyStmts) :
      compileConstructor fields events errors [] (some ctor) =
        Except.ok (genConstructorArgLoads ctor.params ++ bodyStmts) := by
  simp [CompilationModel.compileConstructor,
    FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hbody]

theorem compileConstructor_ok_components
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (ctor : ConstructorSpec) (deployStmts : List YulStmt)
      (hcompile :
        compileConstructor fields events errors [] (some ctor) = Except.ok deployStmts) :
    ∃ bodyStmts,
        compileStmtList fields events errors .memory [] false
          (constructorBodyScope ctor.params) [] ctor.body [] = Except.ok bodyStmts ∧
        deployStmts = genConstructorArgLoads ctor.params ++ bodyStmts := by
    cases hbody :
        compileStmtList fields events errors .memory [] false
          (constructorBodyScope ctor.params) [] ctor.body [] with
  | error err =>
      simp [CompilationModel.compileConstructor,
        FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hbody] at hcompile
  | ok bodyStmts =>
      have hEq :
          deployStmts = genConstructorArgLoads ctor.params ++ bodyStmts := by
        simpa [CompilationModel.compileConstructor,
          FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hbody] using hcompile.symm
      exact ⟨bodyStmts, by simpa using hbody, hEq⟩

/-- The generated parameter loads run to completion on the prebound state,
leaving the body to execute on the state with the decoded bindings applied. -/
private theorem execIRStmts_genParamLoads_prebindRawArgs_extraFuel
    (state : IRState) (spec : FunctionSpec) (bodyStmts : List YulStmt)
    (bindings : List (String × Nat)) (extraFuel : Nat)
    (hsupported : ∀ param ∈ spec.params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams spec.params state.calldata = some bindings) :
    execIRStmts ((genParamLoads spec.params).length + bodyStmts.length + extraFuel + 1)
        (prebindRawArgs state spec.params) (genParamLoads spec.params ++ bodyStmts) =
      execIRStmts (bodyStmts.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState (prebindRawArgs state spec.params) bindings)
        bodyStmts := by
  have hprefix :=
    ParamLoading.exec_genParamLoads_supported_then_extraFuel
      (state := prebindRawArgs state spec.params) (params := spec.params)
      (bindings := bindings) (rest := bodyStmts) (extraFuel := extraFuel)
      hsupported (by simpa using hcalldataSizeFits) (by simpa using hbind)
  simpa [List.length_append, Nat.add_assoc] using hprefix

theorem exec_compiledFunctionIR_of_body_extraFuel
    (state : IRState) (selector : Nat) (spec : FunctionSpec)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (bindings : List (String × Nat)) (tailResult : IRExecResult)
    (extraFuel : Nat)
    (hsupported : ∀ param ∈ spec.params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams spec.params state.calldata = some bindings)
    (hbody :
      execIRStmts (bodyStmts.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState (prebindRawArgs state spec.params) bindings)
        bodyStmts = tailResult) :
    Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads spec.params ++ bodyStmts).length + extraFuel + 1)
        (compiledFunctionIR selector spec returns bodyStmts)
        state.calldata state =
      execResultToIRResult state tailResult := by
  have hprefix := execIRStmts_genParamLoads_prebindRawArgs_extraFuel
    state spec bodyStmts bindings extraFuel hsupported hcalldataSizeFits hbind
  have hprebound :
      List.foldl (fun s x => s.setVar x.1.name x.2) state
        ((List.map Param.toIRParam spec.params).zip state.calldata) =
        prebindRawArgs state spec.params := rfl
  unfold Compiler.Proofs.YulGeneration.execIRFunctionFuel
  unfold Compiler.Proofs.YulGeneration.execIRStmtsFuel
  simp [compiledFunctionIR, execResultToIRResult]
  rw [hprebound, hprefix, hbody]
  rfl

theorem exec_compiledFunctionIR_of_body
    (state : IRState) (selector : Nat) (spec : FunctionSpec)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (bindings : List (String × Nat)) (tailResult : IRExecResult)
    (hsupported : ∀ param ∈ spec.params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams spec.params state.calldata = some bindings)
    (hbody :
      execIRStmts (bodyStmts.length + 1)
        (ParamLoading.applyBindingsToIRState (prebindRawArgs state spec.params) bindings)
        bodyStmts = tailResult) :
    Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads spec.params ++ bodyStmts).length + 1)
        (compiledFunctionIR selector spec returns bodyStmts)
        state.calldata state =
      execResultToIRResult state tailResult :=
  exec_compiledFunctionIR_of_body_extraFuel state selector spec returns bodyStmts bindings
    tailResult 0 hsupported hcalldataSizeFits hbind hbody

/-- A function body's fuel covers its parameter-load prefix and the rest with
some slack. -/
private theorem body_fuel_eq_extraFuel (pre rest : List YulStmt) :
    ∃ extraFuel, sizeOf (pre ++ rest) = pre.length + rest.length + extraFuel := by
  have hle := yulStmtList_length_le_sizeOf (pre ++ rest)
  simp only [List.length_append] at hle
  exact ⟨_, (Nat.add_sub_cancel' hle).symm⟩

/-- When the source binder rejects arguments that cover every parameter (a
dirty scalar head word), a function whose body starts with the generated
parameter loads reverts: storage and events roll back to the initial state,
whatever follows the loads. -/
theorem execIRFunction_revert_of_bind_none
    (state : IRState) (irFn : IRFunction) (params : List Param) (rest : List YulStmt)
    (hparams : irFn.params = params.map Param.toIRParam)
    (hbody : irFn.body = genParamLoads params ++ rest)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hlen : params.length ≤ state.calldata.length)
    (hnone : SourceSemantics.bindSupportedParams params state.calldata = none) :
    execIRFunction irFn state.calldata state =
      { success := false, returnValue := none, finalStorage := state.storage
        finalMappings := Compiler.Proofs.storageAsMappings state.storage
        events := state.events, revertData := state.revertData } := by
  obtain ⟨extraFuel, hfuel⟩ := body_fuel_eq_extraFuel (genParamLoads params) rest
  obtain ⟨reverted, hexec, hdata⟩ := ParamLoading.exec_genParamLoads_supported_revert
    (prebindRawArgs state params) params rest extraFuel hsupported
    (by simpa using hlen) (by simpa using hnone)
  have hprebound :
      List.foldl (fun s x => s.setVar x.1.name x.2) state
        ((List.map Param.toIRParam params).zip state.calldata) =
        prebindRawArgs state params := rfl
  rw [← prebindRawArgs_revertData state params, ← hdata]
  unfold execIRFunction
  rw [hparams, hbody, hfuel]
  dsimp only
  rw [hprebound, hexec]

/-- A prefix that reverts makes the whole statement list revert. -/
theorem execIRStmtsWithInternals_append_of_prefix_revert :
    ∀ (contract : IRContract) (pre rest : List YulStmt) (fuel : Nat)
      (state reverted : IRState),
      execIRStmtsWithInternals contract fuel state pre = .revert reverted →
      execIRStmtsWithInternals contract fuel state (pre ++ rest) = .revert reverted
  | _, [], _, _, _, _, hprefix => by simp [execIRStmtsWithInternals] at hprefix
  | _, _ :: _, _, 0, _, _, hprefix => by simpa [execIRStmtsWithInternals] using hprefix
  | contract, stmt :: pre, rest, fuel + 1, state, reverted, hprefix => by
      simp only [List.cons_append, execIRStmtsWithInternals] at hprefix ⊢
      cases hstep : execIRStmtWithInternals contract fuel state stmt <;>
        simp only [hstep] at hprefix ⊢ <;>
        first
        | exact hprefix
        | exact execIRStmtsWithInternals_append_of_prefix_revert contract pre rest fuel _ _ hprefix

/-- Helper-aware analogue of `execIRFunction_revert_of_bind_none`: the
parameter loads call no internal helper, so a rejected argument still reverts
before the rest of the body runs. -/
theorem execIRFunctionWithInternals_revert_of_bind_none
    (runtimeContract : IRContract) (helperFuel : Nat)
    (state : IRState) (irFn : IRFunction) (params : List Param) (rest : List YulStmt)
    (hparams : irFn.params = params.map Param.toIRParam)
    (hbody : irFn.body = genParamLoads params ++ rest)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hlen : params.length ≤ state.calldata.length)
    (hnone : SourceSemantics.bindSupportedParams params state.calldata = none)
    (hparamDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract (genParamLoads params)) :
    execIRFunctionWithInternals runtimeContract helperFuel irFn state.calldata state =
      { success := false, returnValue := none, finalStorage := state.storage
        finalMappings := Compiler.Proofs.storageAsMappings state.storage
        events := state.events, revertData := state.revertData } := by
  obtain ⟨extraFuel, hfuel⟩ := body_fuel_eq_extraFuel (genParamLoads params) rest
  obtain ⟨reverted, hexec, hdata⟩ := ParamLoading.exec_genParamLoads_supported_revert
    (prebindRawArgs state params) params [] (rest.length + extraFuel + helperFuel)
    hsupported (by simpa using hlen) (by simpa using hnone)
  simp only [List.length_nil, Nat.add_zero, List.append_nil] at hexec
  have hprefix := execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
    ((genParamLoads params).length + (rest.length + extraFuel + helperFuel) + 1)
    (prebindRawArgs state params) (genParamLoads params) hparamDisjoint
  rw [hexec] at hprefix
  dsimp only at hprefix
  have hprebound :
      List.foldl (fun s x => s.setVar x.1.name x.2) state
        ((List.map Param.toIRParam params).zip state.calldata) =
        prebindRawArgs state params := rfl
  rw [← prebindRawArgs_revertData state params, ← hdata]
  unfold execIRFunctionWithInternals
  rw [hparams, hbody, hfuel]
  dsimp only
  rw [hprebound, show (genParamLoads params).length + rest.length + extraFuel + helperFuel + 1 =
      (genParamLoads params).length + (rest.length + extraFuel + helperFuel) + 1 by omega,
    execIRStmtsWithInternals_append_of_prefix_revert runtimeContract _ _ _ _ _ hprefix]

theorem execIRStmtsWithInternals_append_of_prefix_continue :
    ∀ (contract : IRContract) (pre rest : List YulStmt) (fuel : Nat)
      (state state' : IRState),
      execIRStmtsWithInternals contract (pre.length + fuel) state pre = .continue state' →
      execIRStmtsWithInternals contract (pre.length + fuel) state (pre ++ rest) =
        execIRStmtsWithInternals contract fuel state' rest
  | contract, [], rest, fuel, state, state', hprefix => by
      simp only [List.length_nil, zero_add, execIRStmtsWithInternals] at hprefix
      cases hprefix
      simp
  | contract, stmt :: pre, rest, fuel, state, state', hprefix => by
      have hprefixNorm :
          execIRStmtsWithInternals contract (Nat.succ (pre.length + fuel))
            state (stmt :: pre) = .continue state' := by
        simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hprefix
      simp only [List.length_cons, List.cons_append]
      rw [show Nat.succ pre.length + fuel = Nat.succ (pre.length + fuel) by omega]
      rw [execIRStmtsWithInternals]
      cases hstep : execIRStmtWithInternals contract (pre.length + fuel) state stmt with
      | «continue» next =>
          have htail :
              execIRStmtsWithInternals contract (pre.length + fuel) next pre =
                .continue state' := by
            simpa [execIRStmtsWithInternals, hstep] using hprefixNorm
          exact execIRStmtsWithInternals_append_of_prefix_continue
            contract pre rest fuel next state' htail
      | «return» value next =>
          simp [execIRStmtsWithInternals, hstep] at hprefixNorm
      | stop next =>
          simp [execIRStmtsWithInternals, hstep] at hprefixNorm
      | revert next =>
          simp [execIRStmtsWithInternals, hstep] at hprefixNorm
      | «leave» next =>
          simp [execIRStmtsWithInternals, hstep] at hprefixNorm

theorem exec_genParamLoads_supported_then_extraFuel_withInternals
    (runtimeContract : IRContract)
    (state : IRState) (params : List Param) (bindings : List (String × Nat))
    (rest : List YulStmt) (extraFuel : Nat)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams params state.calldata = some bindings)
    (hparamDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract (genParamLoads params)) :
    execIRStmtsWithInternals runtimeContract
        ((genParamLoads params).length + rest.length + extraFuel + 1) state
        (genParamLoads params ++ rest) =
      execIRStmtsWithInternals runtimeContract
        (rest.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState state bindings) rest := by
  let tailFuel := rest.length + extraFuel + 1
  have hlegacyPrefix :
      execIRStmts ((genParamLoads params).length + tailFuel) state (genParamLoads params) =
        .continue (ParamLoading.applyBindingsToIRState state bindings) := by
    have hlegacy :=
      ParamLoading.exec_genParamLoads_supported_then_extraFuel
        (state := state) (params := params) (bindings := bindings)
        (rest := []) (extraFuel := rest.length + extraFuel)
        hsupported hcalldataSizeFits hbind
    simpa [tailFuel, execIRStmts, Nat.add_assoc] using hlegacy
  have hprefix :
      execIRStmtsWithInternals runtimeContract ((genParamLoads params).length + tailFuel)
          state (genParamLoads params) =
        .continue (ParamLoading.applyBindingsToIRState state bindings) := by
    have hcompat :=
      execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint
        runtimeContract ((genParamLoads params).length + tailFuel)
        state (genParamLoads params) hparamDisjoint
    rw [hcompat, hlegacyPrefix]
  have happend :=
    execIRStmtsWithInternals_append_of_prefix_continue runtimeContract
      (genParamLoads params) rest tailFuel state
      (ParamLoading.applyBindingsToIRState state bindings) hprefix
  simpa [tailFuel, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using happend

theorem exec_compiledFunctionIR_withInternals_of_body_extraFuel
    (runtimeContract : IRContract)
    (state : IRState) (selector : Nat) (spec : FunctionSpec)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (bindings : List (String × Nat)) (tailResult : IRExecResultWithInternals)
    (extraFuel : Nat)
    (hsupported : ∀ param ∈ spec.params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams spec.params state.calldata = some bindings)
    (hparamDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract (genParamLoads spec.params))
    (hbody :
      execIRStmtsWithInternals runtimeContract (bodyStmts.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState (prebindRawArgs state spec.params) bindings)
        bodyStmts = tailResult) :
    execIRStmtsWithInternals runtimeContract
        ((genParamLoads spec.params ++ bodyStmts).length + extraFuel + 1)
        (prebindRawArgs state spec.params)
        (compiledFunctionIR selector spec returns bodyStmts).body =
      tailResult := by
  have hprefix :=
    exec_genParamLoads_supported_then_extraFuel_withInternals runtimeContract
      (prebindRawArgs state spec.params) spec.params bindings bodyStmts extraFuel hsupported
      (by simpa using hcalldataSizeFits) (by simpa using hbind) hparamDisjoint
  rw [← hbody]
  simpa [compiledFunctionIR, List.length_append, Nat.add_assoc] using hprefix

theorem interpretFunction_eq_execResultToIRResult_of_body
    (model : CompilationModel)
    (fn : FunctionSpec) {habi : fn.abiDecoding = .standard}
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult)
    (rollback : IRState) (irResult : IRExecResult) (bindings : List (String × Nat))
    (hbind :
      SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hnoEvents : model.events = [])
    (hsource :
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector, errors := model.errors }
        fn.body = sourceResult)
    (hrollbackStorage :
        rollback.storage = fun s =>
          Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
            (SourceSemantics.encodeStorage model
              (SourceSemantics.withTransactionContext initialWorld tx) s.toNat))
    (hrollbackEvents :
      rollback.events =
        SourceSemantics.encodeEvents
          (SourceSemantics.withTransactionContext initialWorld tx).events)
    (hmatch :
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irResult) :
      FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (execResultToIRResult rollback irResult) := by
  have hsourceWithEvents :
      SourceSemantics.execStmtListWithEvents (SourceSemantics.effectiveFields model) model.events
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector, errors := model.errors }
        fn.body = sourceResult := by
    simpa [hnoEvents] using hsource
  have hpack :=
    FunctionBody.stmtResultToSourceResult_matches_irExecResult
      (spec := model)
      (fields := SourceSemantics.effectiveFields model)
      (initialWorld := SourceSemantics.withTransactionContext initialWorld tx)
      (rollback := rollback)
      (sourceResult := sourceResult)
      (irResult := irResult)
      hrollbackStorage hrollbackEvents rfl hmatch
  simp only [SourceSemantics.interpretFunction, FunctionSpec.bindingParams, habi,
    SourceSemantics.bindExternalParams_eq_some_of_bindSupportedParams _ hbind]
  rw [hsourceWithEvents]; exact hpack

theorem interpretFunctionWithHelpers_eq_execResultToIRResultWithInternals_of_body
    (model : CompilationModel) (fn : FunctionSpec)
    {habi : fn.abiDecoding = .standard}
    (helperFuel : Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult)
    (rollback : IRState) (irResult : IRExecResultWithInternals)
    (bindings : List (String × Nat))
    (hbind :
      SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hsource :
      SourceSemantics.execStmtListWithHelpers model (SourceSemantics.effectiveFields model)
        helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector, errors := model.errors }
        fn.body = sourceResult)
    (hrollbackStorage :
        rollback.storage = fun s =>
          Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
            (SourceSemantics.encodeStorage model
              (SourceSemantics.withTransactionContext initialWorld tx) s.toNat))
    (hrollbackEvents :
      rollback.events =
        SourceSemantics.encodeEvents
          (SourceSemantics.withTransactionContext initialWorld tx).events)
    (hmatch :
      stmtResultMatchesIRExecWithInternals
        (SourceSemantics.effectiveFields model) sourceResult irResult) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunctionWithHelpers model helperFuel fn tx initialWorld)
      (FunctionBody.irResultOfExecResultWithInternals rollback irResult) := by
  simp only [SourceSemantics.interpretFunctionWithHelpers, FunctionSpec.bindingParams, habi,
    SourceSemantics.bindExternalParams_eq_some_of_bindSupportedParams _ hbind, hsource]
  cases sourceResult <;> cases irResult <;>
    simp [stmtResultMatchesIRExecWithInternals, FunctionBody.stmtResultMatchesIRExec,
      FunctionBody.runtimeStateMatchesIR] at hmatch <;>
    simp [FunctionBody.sourceResultMatchesIRResult,
      FunctionBody.irResultOfExecResultWithInternals, SourceSemantics.successResult,
      SourceSemantics.revertedResult, SourceSemantics.encodeStorage, hmatch, hrollbackStorage,
      hrollbackEvents]

theorem runtimeStateMatchesIR_applyBindingsToIRState
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (bindings : List (String × Nat)) :
    FunctionBody.runtimeStateMatchesIR fields runtime
      (ParamLoading.applyBindingsToIRState state bindings) := by
  induction bindings generalizing state with
  | nil =>
      simpa [ParamLoading.applyBindingsToIRState]
  | cons entry rest ih =>
      simpa [ParamLoading.applyBindingsToIRState, IRState.setVar] using
        ih (state := state.setVar entry.1 entry.2) hmatch

theorem constructorRuntimeStateMatchesIR_applyBindingsToIRState
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : FunctionBody.constructorRuntimeStateMatchesIR fields runtime state)
    (bindings : List (String × Nat)) :
    FunctionBody.constructorRuntimeStateMatchesIR fields runtime
      (ParamLoading.applyBindingsToIRState state bindings) := by
  induction bindings generalizing state with
  | nil =>
      simpa [ParamLoading.applyBindingsToIRState]
  | cons entry rest ih =>
      simpa [ParamLoading.applyBindingsToIRState, IRState.setVar] using
        ih (state := state.setVar entry.1 entry.2) hmatch

theorem runtimeStateMatchesIR_prebindRawArgs
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (params : List Param) :
    FunctionBody.runtimeStateMatchesIR fields runtime (prebindRawArgs state params) := by
  unfold prebindRawArgs
  induction (List.zip (List.map Param.toIRParam params) state.calldata) generalizing state with
  | nil =>
      simpa
  | cons entry rest ih =>
      simpa [List.foldl, IRState.setVar] using
        ih (state := state.setVar entry.1.name entry.2) hmatch

/-- Folding `bindValue` over names that never mention `queryName` leaves its
lookup unchanged. -/
private theorem lookupBinding?_foldl_bindValue_not_mem
    (bindings : List (String × Nat))
    (init : List (String × Nat))
    (queryName : String)
    (hnotmem : queryName ∉ bindings.map Prod.fst) :
    FunctionBody.lookupBinding?
      (bindings.foldl (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) init)
      queryName =
    FunctionBody.lookupBinding? init queryName := by
  induction bindings generalizing init with
  | nil =>
      simp
  | cons entry rest ih =>
      have hqueryNe : queryName ≠ entry.1 := by
        intro hEq
        apply hnotmem
        simp [hEq]
      have hrestNotMem : queryName ∉ rest.map Prod.fst := by
        intro hmem
        apply hnotmem
        simp [hmem]
      rw [List.foldl, ih _ hrestNotMem,
        FunctionBody.lookupBinding?_bindValue_ne init entry.1 queryName entry.2 hqueryNe]

/-- If a name occurs in the final binding list with unique parameter names,
folding `bindValue` over any initial environment reconstructs that lookup
exactly. -/
private theorem lookupBinding?_foldl_bindValue_mem
    (bindings : List (String × Nat))
    (init : List (String × Nat))
    (queryName : String)
    (hmem : queryName ∈ bindings.map Prod.fst)
    (hnodup : (bindings.map Prod.fst).Nodup) :
    FunctionBody.lookupBinding?
      (bindings.foldl (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) init)
      queryName =
    FunctionBody.lookupBinding? bindings queryName := by
  induction bindings generalizing init with
  | nil =>
      cases hmem
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hheadNotMem, hrestNodup⟩
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with hEq | hmemRest
      · subst hEq
        have hrestNotMem : entry.1 ∉ rest.map Prod.fst := hheadNotMem
        rw [List.foldl]
        rw [lookupBinding?_foldl_bindValue_not_mem rest
          (SourceSemantics.bindValue init entry.1 entry.2) entry.1 hrestNotMem]
        rw [FunctionBody.lookupBinding?_bindValue_eq]
        unfold FunctionBody.lookupBinding?
        simp
      · have hqueryNe : queryName ≠ entry.1 := by
          intro hEq
          apply hheadNotMem
          simpa [hEq] using hmemRest
        rw [List.foldl]
        rw [ih (SourceSemantics.bindValue init entry.1 entry.2) hmemRest hrestNodup]
        have hbeq : (entry.1 == queryName) = false := by
          have hqueryNe' : ¬ entry.1 = queryName := by
            intro hEq
            exact hqueryNe hEq.symm
          simp [hqueryNe']
        unfold FunctionBody.lookupBinding?
        simp [List.find?, hbeq]

theorem supported_constructor_param_state_exact
    (state : IRState)
    (params : List Param)
    (bindings : List (String × Nat))
    (hinit : FunctionBody.bindingsExactlyMatchIRVars [] state)
    (hparamNamesNodup : (params.map (·.name)).Nodup)
    (hbind : SourceSemantics.bindSupportedParams params state.calldata = some bindings) :
    FunctionBody.bindingsExactlyMatchIRVars bindings
      (ParamLoading.applyBindingsToIRState state bindings) := by
  have hfinal :
      FunctionBody.bindingsExactlyMatchIRVars
        (bindings.foldl (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) [])
        (ParamLoading.applyBindingsToIRState state bindings) :=
    FunctionBody.bindingsExactlyMatchIRVars_applyBindingsToIRState hinit
  intro queryName
  rw [hfinal queryName]
  by_cases hmem : queryName ∈ bindings.map Prod.fst
  · exact lookupBinding?_foldl_bindValue_mem bindings [] queryName hmem
      (ParamLoading.bindSupportedParams_names_nodup hparamNamesNodup hbind)
  · rw [lookupBinding?_foldl_bindValue_not_mem bindings [] queryName hmem]
    have hfindNone : List.find? (fun entry => entry.1 == queryName) bindings = none := by
      apply (List.find?_eq_none).2
      intro entry hentry
      have hentryName : entry.1 ∈ bindings.map Prod.fst := by
        exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
      have hne : entry.1 ≠ queryName := by
        intro hEq
        apply hmem
        simpa [hEq] using hentryName
      simp [hne]
    simpa [FunctionBody.lookupBinding?, hfindNone]

/-- The raw prebinding fold starts from an empty environment, so names absent
from the raw ABI prefix stay absent afterwards. -/
private theorem lookupBinding?_rawArgBindings_fold_not_mem
    (params : List Param)
    (args : List Nat)
    (queryName : String)
    (hnotmem : queryName ∉ (rawArgBindings params args).map Prod.fst) :
    FunctionBody.lookupBinding?
      ((rawArgBindings params args).foldl
        (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) [])
      queryName = none := by
  rw [lookupBinding?_foldl_bindValue_not_mem (rawArgBindings params args) [] queryName hnotmem]
  simp [FunctionBody.lookupBinding?]

private theorem lookupBinding?_eq_none_of_not_mem
    (bindings : List (String × Nat))
    (queryName : String)
    (hnotmem : queryName ∉ bindings.map Prod.fst) :
    FunctionBody.lookupBinding? bindings queryName = none := by
  unfold FunctionBody.lookupBinding?
  induction bindings with
  | nil =>
      simp
  | cons entry rest ih =>
      have hqueryNe : queryName ≠ entry.1 := by
        intro hEq
        apply hnotmem
        simp [hEq]
      have hrestNotMem : queryName ∉ rest.map Prod.fst := by
        intro hmem
        apply hnotmem
        simp [hmem]
      have hbeq : (entry.1 == queryName) = false := by
        have hqueryNe' : ¬ entry.1 = queryName := by
          intro hEq
          exact hqueryNe hEq.symm
        simp [hqueryNe']
      simp [List.find?, hbeq, ih hrestNotMem]

private theorem lookupBinding?_some_of_mem
    (bindings : List (String × Nat))
    (queryName : String)
    (hmem : queryName ∈ bindings.map Prod.fst) :
    ∃ value, FunctionBody.lookupBinding? bindings queryName = some value := by
  induction bindings with
  | nil =>
      cases hmem
  | cons entry rest ih =>
      simp only [List.map_cons, List.mem_cons] at hmem
      by_cases hEq : entry.1 = queryName
      · refine ⟨entry.2, ?_⟩
        subst hEq
        unfold FunctionBody.lookupBinding?
        simp
      · rcases hmem with hhead | htail
        · cases hEq hhead.symm
        · rcases ih htail with ⟨value, hvalue⟩
          refine ⟨value, ?_⟩
          have hbeq : (entry.1 == queryName) = false := by
            simp [hEq]
          unfold FunctionBody.lookupBinding? at hvalue ⊢
          cases hfind : List.find? (fun candidate => candidate.1 == queryName) rest with
          | none =>
              simp [List.find?, hbeq, hfind] at hvalue
          | some found =>
              cases found with
              | mk foundName foundValue =>
                  simp [List.find?, hbeq, hfind] at hvalue ⊢
                  cases hvalue
                  rfl

/-- An address-ranged transaction-context word survives the word/address
normalization round trip. -/
private theorem addressWord_roundtrip_of_lt_addressModulus
    {v : Nat} (h : v < Compiler.Constants.addressModulus) :
    v % Compiler.Constants.evmModulus % Verity.Core.Address.modulus = v := by
  have hEvm : v < Compiler.Constants.evmModulus := by
    dsimp [Compiler.Constants.addressModulus, Compiler.Constants.evmModulus] at h ⊢
    omega
  have hAddr : v < Verity.Core.Address.modulus := by
    simpa [Verity.Core.Address.modulus, Compiler.Constants.addressModulus,
      Verity.Core.ADDRESS_MODULUS] using h
  rw [Nat.mod_eq_of_lt hEvm, Nat.mod_eq_of_lt hAddr]

/-- The selector-prefixed calldata size word of a fitting transaction is exact. -/
private theorem calldataSize_val_of_txCalldataSizeFitsEvm
    {tx : IRTransaction} (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    (Verity.Core.Uint256.ofNat 4 + Verity.Core.Uint256.ofNat (tx.args.length * 32)).val =
      4 + tx.args.length * 32 := by
  have hsize : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
  simp only [Verity.Core.Uint256.ofNat, hsize]
  change (4 % _ + tx.args.length * 32 % _) % _ = _
  rw [hsize, ← Nat.add_mod]
  exact Nat.mod_eq_of_lt hcalldataSizeFits

/-- The initial IR state matches the source runtime once the transaction
context already fits the bounded source-level numeric domains. -/
theorem initialIRStateForTx_matches_runtime
    (model : CompilationModel)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.runtimeStateMatchesIR
      (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := []
        selector := tx.functionSelector, errors := model.errors }
      (FunctionBody.initialIRStateForTx model tx initialWorld) := by
  obtain ⟨hsender, hthis, hmsgValue, htimestamp, hnumber, hchain, hblob, htxOrigin⟩ :=
    htxNormalized
  refine ⟨?_, ?_⟩
  · simpa [FunctionBody.initialIRStateForTx, SourceSemantics.effectiveFields,
      SourceSemantics.encodeStorage] using
      (FunctionBody.encodeStorage_withTransactionContext model initialWorld tx).symm
  · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext,
      Verity.wordToAddress, addressWord_roundtrip_of_lt_addressModulus hsender,
      addressWord_roundtrip_of_lt_addressModulus hthis,
      addressWord_roundtrip_of_lt_addressModulus htxOrigin, Nat.mod_eq_of_lt hmsgValue,
      Nat.mod_eq_of_lt htimestamp, Nat.mod_eq_of_lt hnumber, Nat.mod_eq_of_lt hchain,
      Nat.mod_eq_of_lt hblob, calldataSize_val_of_txCalldataSizeFitsEvm hcalldataSizeFits]
    rfl

/-- The same initial IR state matches constructor source execution when the
source runtime is initialized with constructor-shaped calldata size, i.e. no
external-call selector prefix. -/
theorem initialIRStateForTx_matches_constructor_runtime
    (model : CompilationModel)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxConstructorCalldataSizeFitsEvm tx) :
    FunctionBody.constructorRuntimeStateMatchesIR
      (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withConstructorTransactionContext initialWorld tx
        bindings := []
        selector := tx.functionSelector, errors := model.errors }
      (FunctionBody.initialIRStateForTx model tx initialWorld) := by
  rcases htxNormalized with
    ⟨hsender, hthis, hmsgValue, htimestamp, hnumber, hchain, hblob, htxOrigin⟩
  have hsenderEvm : tx.sender < Compiler.Constants.evmModulus := by
    dsimp [Compiler.Constants.addressModulus, Compiler.Constants.evmModulus] at hsender ⊢
    omega
  have hthisEvm : tx.thisAddress < Compiler.Constants.evmModulus := by
    dsimp [Compiler.Constants.addressModulus, Compiler.Constants.evmModulus] at hthis ⊢
    omega
  have hsenderAddr : tx.sender < Verity.Core.Address.modulus := by
    simpa [Verity.Core.Address.modulus, Compiler.Constants.addressModulus,
      Verity.Core.ADDRESS_MODULUS] using hsender
  have hthisAddr : tx.thisAddress < Verity.Core.Address.modulus := by
    simpa [Verity.Core.Address.modulus, Compiler.Constants.addressModulus,
      Verity.Core.ADDRESS_MODULUS] using hthis
  have hsenderWord :
      tx.sender % Compiler.Constants.evmModulus % Verity.Core.Address.modulus = tx.sender := by
    rw [Nat.mod_eq_of_lt hsenderEvm, Nat.mod_eq_of_lt hsenderAddr]
  have hthisWord :
      tx.thisAddress % Compiler.Constants.evmModulus % Verity.Core.Address.modulus =
        tx.thisAddress := by
    rw [Nat.mod_eq_of_lt hthisEvm, Nat.mod_eq_of_lt hthisAddr]
  have hcalldataSizeFits' : tx.args.length * 32 < Verity.Core.Uint256.modulus := by
    simpa [TxConstructorCalldataSizeFitsEvm, Verity.Core.Uint256.modulus,
      Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using
        hcalldataSizeFits
  have htxOriginWord := addressWord_roundtrip_of_lt_addressModulus htxOrigin
  refine ⟨?_, ?_⟩
  · simpa [FunctionBody.initialIRStateForTx, SourceSemantics.effectiveFields,
      SourceSemantics.encodeStorage] using
      (SourceSemantics.encodeStorage_withConstructorTransactionContext model initialWorld tx).symm
  · simp [FunctionBody.initialIRStateForTx,
      SourceSemantics.withConstructorTransactionContext, Verity.wordToAddress, hsenderWord,
      hthisWord, htxOriginWord, Nat.mod_eq_of_lt hmsgValue, Nat.mod_eq_of_lt htimestamp,
      Nat.mod_eq_of_lt hnumber, Nat.mod_eq_of_lt hchain, Nat.mod_eq_of_lt hblob]
    exact ⟨rfl, hcalldataSizeFits'⟩

theorem initialIRStateForTx_matches_bound_constructor_runtime
    (model : CompilationModel)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxConstructorCalldataSizeFitsEvm tx) :
    FunctionBody.constructorRuntimeStateMatchesIR
      (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withConstructorTransactionContext initialWorld tx
        bindings := []
        selector := tx.functionSelector, errors := model.errors }
      (ParamLoading.applyBindingsToIRState
        (FunctionBody.initialIRStateForTx model tx initialWorld)
        bindings) := by
  exact constructorRuntimeStateMatchesIR_applyBindingsToIRState
    (bindings := bindings)
    (initialIRStateForTx_matches_constructor_runtime
      model tx initialWorld htxNormalized hcalldataSizeFits)

/-- The ABI parameter-loading prefix reconstructs exactly the decoded source
bindings for any supported function with pairwise-distinct parameter names. -/
theorem supported_function_param_state_exact
    (state : IRState)
    (params : List Param)
    (bindings : List (String × Nat))
    (hinit : FunctionBody.bindingsExactlyMatchIRVars [] state)
    (hparamNamesNodup : (params.map (·.name)).Nodup)
    (hbind : SourceSemantics.bindSupportedParams params state.calldata = some bindings) :
    FunctionBody.bindingsExactlyMatchIRVars bindings
      (ParamLoading.applyBindingsToIRState (prebindRawArgs state params) bindings) := by
  let rawInitBindings :=
    (rawArgBindings params state.calldata).foldl
      (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) []
  have hprebound :
      FunctionBody.bindingsExactlyMatchIRVars rawInitBindings
        (prebindRawArgs state params) := by
    simpa [rawInitBindings] using prebindRawArgs_exact_rawArgBindings hinit params
  have hfinal :
      FunctionBody.bindingsExactlyMatchIRVars
        (bindings.foldl (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2)
          rawInitBindings)
        (ParamLoading.applyBindingsToIRState (prebindRawArgs state params) bindings) :=
    FunctionBody.bindingsExactlyMatchIRVars_applyBindingsToIRState hprebound
  intro queryName
  rw [hfinal queryName]
  by_cases hmem : queryName ∈ bindings.map Prod.fst
  · exact lookupBinding?_foldl_bindValue_mem bindings rawInitBindings queryName hmem
      (ParamLoading.bindSupportedParams_names_nodup hparamNamesNodup hbind)
  · rw [lookupBinding?_foldl_bindValue_not_mem bindings rawInitBindings queryName hmem]
    have hrawNames :
        (rawArgBindings params state.calldata).map Prod.fst = bindings.map Prod.fst :=
      rawArgBindings_names_of_bindSupportedParams hbind
    have hrawNotMem : queryName ∉ (rawArgBindings params state.calldata).map Prod.fst := by
      rw [hrawNames]
      exact hmem
    rw [lookupBinding?_rawArgBindings_fold_not_mem params state.calldata queryName hrawNotMem]
    symm
    exact lookupBinding?_eq_none_of_not_mem bindings queryName hmem

/-- Decoded supported parameters bind every declared parameter name. -/
private theorem exactState_scopeNamesPresent_of_bindSupportedParams
    {params : List Param} {args : List Nat} {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings) :
    FunctionBody.scopeNamesPresent (params.map (·.name)) bindings := by
  intro name hmem
  have hmemBindings : name ∈ bindings.map Prod.fst := by
    rw [ParamLoading.bindSupportedParams_names hbind]
    simpa using hmem
  exact lookupBinding?_some_of_mem bindings name hmemBindings

/-- Runtime/IR state alignment does not inspect the source binding list. -/
private theorem exactState_runtimeStateMatchesIR_rebind
    {fields : List Field} {world : Verity.ContractState} {selector : Nat}
    {errors : List ErrorDef} {state : IRState} (bindings : List (String × Nat))
    (h : FunctionBody.runtimeStateMatchesIR fields
      { world := world, bindings := [], selector := selector, errors := errors } state) :
    FunctionBody.runtimeStateMatchesIR fields
      { world := world, bindings := bindings, selector := selector, errors := errors } state := by
  simpa [FunctionBody.runtimeStateMatchesIR] using h

/-- Under normalized fields and empty event/error catalogs, body compilation is
the effective-field compilation used by the generic statement-list lemmas. -/
private theorem exactState_compileStmtList_effectiveFields
    {model : CompilationModel} {scope : List String} {stmts : List Stmt}
    {bodyStmts : List YulStmt}
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (h : compileStmtList model.fields model.events model.errors .calldata [] false
      scope [] stmts = Except.ok bodyStmts) :
    compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
      scope [] stmts = Except.ok bodyStmts := by
  simpa [hnormalized, hnoEvents, hnoErrors] using h

theorem supported_function_body_correct_from_exact_state_core_extraFuel
    (model : CompilationModel) (fn : FunctionSpec) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcore : FunctionBody.StmtListCompileCore (fn.params.map (·.name)) fn.body)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hstateRuntime : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := [], selector := tx.functionSelector, errors := model.errors } state)
    (hstateBindings : FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hfuel : sizeOf bodyStmts ≤ bodyStmts.length + extraFuel) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings, selector := tx.functionSelector,
          errors := model.errors } fn.body = sourceResult ∧
      execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
  rcases FunctionBody.exec_compileStmtList_core_extraFuel
      (fields := SourceSemantics.effectiveFields model) (state := state)
      (inScopeNames := fn.params.map (·.name)) extraFuel hcore
      (exactState_scopeNamesPresent_of_bindSupportedParams hbind) hstateBindings
      (FunctionBody.bindingsBounded_of_bindSupportedParams hbind)
      (exactState_runtimeStateMatchesIR_rebind bindings hstateRuntime) with
    ⟨bodyIR, hbodyCoreCompile, hcoreSem⟩
  rw [exactState_compileStmtList_effectiveFields hnormalized hnoEvents hnoErrors
    hbodyCompile] at hbodyCoreCompile
  cases hbodyCoreCompile
  exact ⟨_, _, rfl, rfl, (hcoreSem hfuel).1⟩

/-- Terminal-core fuel slack: running at `sizeOf` plus the leftover slack is the
same as running at the body length plus the full extra fuel. -/
private theorem exactState_terminal_fuel_eq
    (bodyStmts : List YulStmt) {extraFuel : Nat}
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel) :
    sizeOf bodyStmts + (extraFuel - (sizeOf bodyStmts - bodyStmts.length)) + 1 =
      bodyStmts.length + extraFuel + 1 := by
  have hlenle : bodyStmts.length ≤ sizeOf bodyStmts := yulStmtList_length_le_sizeOf bodyStmts
  omega

theorem supported_function_body_correct_from_exact_state_terminal_core_extraFuel
    (model : CompilationModel) (fn : FunctionSpec) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hstateRuntime : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := [], selector := tx.functionSelector, errors := model.errors } state)
    (hstateBindings : FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings, selector := tx.functionSelector,
          errors := model.errors } fn.body = sourceResult ∧
      execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
  rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
      (fields := SourceSemantics.effectiveFields model) (state := state)
      (inScopeNames := fn.params.map (·.name))
      (extraFuel - (sizeOf bodyStmts - bodyStmts.length)) hterminal
      FunctionBody.scopeNamesIncluded_refl
      (exactState_scopeNamesPresent_of_bindSupportedParams hbind)
      (FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings)
      (FunctionBody.bindingsBounded_of_bindSupportedParams hbind)
      (exactState_runtimeStateMatchesIR_rebind bindings hstateRuntime) with
    ⟨bodyIR, hbodyTerminalCompile, hterminalSem⟩
  rw [exactState_compileStmtList_effectiveFields hnormalized hnoEvents hnoErrors
    hbodyCompile] at hbodyTerminalCompile
  cases hbodyTerminalCompile
  rw [← exactState_terminal_fuel_eq bodyStmts hextraFuel]
  exact ⟨_, _, rfl, rfl, hterminalSem⟩

private theorem firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs
    {spec : CompilationModel}
    {selectors : List Nat}
    (hvalidate : validateCompileInputs spec selectors = Except.ok ()) :
    firstFieldWriteSlotConflict
        (applySlotAliasRanges spec.fields spec.slotAliasRanges) = none := by
  exact validateCompileInputs_firstFieldWriteSlotConflict_eq_none hvalidate

/-- Successful compilation of a function spec with a known body is exactly the
generated `compiledFunctionIR` wrapper. -/
private theorem compileFunctionSpec_eq_compiledFunctionIR_of_body
    {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    {selector : Nat} {fn : FunctionSpec} {habi : fn.abiDecoding = .standard}
    {irFn : IRFunction} {returns : List ParamType} {bodyStmts : List YulStmt}
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList fields events errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec fields events errors [] selector fn = Except.ok irFn) :
    irFn = compiledFunctionIR selector fn returns bodyStmts := by
  have hcompiled := compileFunctionSpec_ok_of_components (habi := habi) fields events errors
    selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  rw [hcompile] at hcompiled
  injection hcompiled

/-- Packages a body-level source/IR match into the function-level result, for any
function execution that yields the body's IR outcome from the initial state. -/
private theorem compileFunctionSpec_sourceResultMatches_of_exec
    (model : CompilationModel) (fn : FunctionSpec) {habi : fn.abiDecoding = .standard}
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    {sourceResult : SourceSemantics.StmtResult} {irExec : IRExecResult}
    {bindings : List (String × Nat)} {fuel : Nat} {irFn : IRFunction}
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hnoEvents : model.events = [])
    (hsource : SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := bindings, selector := tx.functionSelector,
        errors := model.errors } fn.body = sourceResult)
    (hmatch : FunctionBody.stmtResultMatchesIRExec
      (SourceSemantics.effectiveFields model) sourceResult irExec)
    (hexec : Compiler.Proofs.YulGeneration.execIRFunctionFuel fuel irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      execResultToIRResult (FunctionBody.initialIRStateForTx model tx initialWorld) irExec) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (Compiler.Proofs.YulGeneration.execIRFunctionFuel fuel irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rw [hexec]
  refine interpretFunction_eq_execResultToIRResult_of_body (habi := habi) model fn tx
    initialWorld sourceResult _ irExec bindings hbind hnoEvents hsource ?_ ?_ hmatch
  · funext s
    simp [FunctionBody.initialIRStateForTx, FunctionBody.encodeStorage_withTransactionContext]
  · simp [FunctionBody.initialIRStateForTx]

theorem compileFunctionSpec_correct_of_body
    (model : CompilationModel)
    (selector : Nat) (fn : FunctionSpec)
    {habi : fn.abiDecoding = .standard} (irFn : IRFunction)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult) (irExec : IRExecResult)
    (bindings : List (String × Nat))
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec model.fields model.events model.errors [] selector fn =
      Except.ok irFn)
    (hparamsSupported : ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hnoEvents : model.events = [])
    (hsource : SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := bindings, selector := tx.functionSelector,
        errors := model.errors } fn.body = sourceResult)
    (hbodyExec :
      execIRStmts (bodyStmts.length + 1)
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bodyStmts = irExec)
    (hmatch : FunctionBody.stmtResultMatchesIRExec
      (SourceSemantics.effectiveFields model) sourceResult irExec) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads fn.params ++ bodyStmts).length + 1)
        irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rw [compileFunctionSpec_eq_compiledFunctionIR_of_body (habi := habi)
    hvalidate hreturns hbodyCompile hcompile]
  refine compileFunctionSpec_sourceResultMatches_of_exec (habi := habi) model fn tx
    initialWorld hbind hnoEvents hsource hmatch ?_
  exact exec_compiledFunctionIR_of_body _ selector fn returns bodyStmts bindings irExec
    hparamsSupported hcalldataSizeFits hbind hbodyExec

theorem compileFunctionSpec_correct_of_body_normalized_extraFuel
    (model : CompilationModel)
    (hnormalized : applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (selector : Nat) (fn : FunctionSpec)
    {habi : fn.abiDecoding = .standard} (irFn : IRFunction)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult) (irExec : IRExecResult)
    (bindings : List (String × Nat)) (extraFuel : Nat)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList (applySlotAliasRanges model.fields model.slotAliasRanges)
        model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec (applySlotAliasRanges model.fields model.slotAliasRanges)
        model.events model.errors [] selector fn = Except.ok irFn)
    (hparamsSupported : ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hnoEvents : model.events = [])
    (hsource : SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := bindings, selector := tx.functionSelector,
        errors := model.errors } fn.body = sourceResult)
    (hbodyExec :
      execIRStmts (bodyStmts.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bodyStmts = irExec)
    (hmatch : FunctionBody.stmtResultMatchesIRExec
      (SourceSemantics.effectiveFields model) sourceResult irExec) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1)
        irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rw [hnormalized] at hbodyCompile hcompile
  obtain rfl := compileFunctionSpec_eq_compiledFunctionIR_of_body (habi := habi)
    hvalidate hreturns hbodyCompile hcompile
  exact compileFunctionSpec_sourceResultMatches_of_exec (habi := habi) model fn tx initialWorld
    hbind hnoEvents hsource hmatch (exec_compiledFunctionIR_of_body_extraFuel _ selector fn
      returns bodyStmts bindings irExec extraFuel hparamsSupported hcalldataSizeFits hbind
      hbodyExec)

theorem compileFunctionSpec_correct_of_body_supported_extraFuel
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (selector : Nat) (fn : FunctionSpec)
    {habi : fn.abiDecoding = .standard} (irFn : IRFunction)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult) (irExec : IRExecResult)
    (bindings : List (String × Nat)) (extraFuel : Nat)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList (applySlotAliasRanges model.fields model.slotAliasRanges)
        model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec (applySlotAliasRanges model.fields model.slotAliasRanges)
        model.events model.errors [] selector fn = Except.ok irFn)
    (hparamsSupported : ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hsource : SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := bindings, selector := tx.functionSelector,
        errors := model.errors } fn.body = sourceResult)
    (hbodyExec :
      execIRStmts (bodyStmts.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bodyStmts = irExec)
    (hmatch : FunctionBody.stmtResultMatchesIRExec
      (SourceSemantics.effectiveFields model) sourceResult irExec) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1)
        irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact compileFunctionSpec_correct_of_body_normalized_extraFuel (habi := habi)
    model
    hSupported.normalizedFields
    selector fn irFn returns bodyStmts tx initialWorld sourceResult irExec
    bindings extraFuel hvalidate hreturns hbodyCompile hcompile hparamsSupported
    hcalldataSizeFits hbind hSupported.noEvents hsource hbodyExec hmatch

/-- Body-level source/IR agreement from the exact parameter-loaded initial state,
running the compiled body at `bodyStmts.length + extraFuel + 1` fuel. -/
private abbrev SupportedFunctionBodyExecMatches
    (model : CompilationModel) (fn : FunctionSpec) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (bodyStmts : List YulStmt) (extraFuel : Nat) : Prop :=
  ∃ sourceResult irExec,
    SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := bindings
        selector := tx.functionSelector, errors := model.errors }
      fn.body = sourceResult ∧
    execIRStmts (bodyStmts.length + extraFuel + 1)
      (ParamLoading.applyBindingsToIRState
        (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
        bindings)
      bodyStmts = irExec ∧
    FunctionBody.stmtResultMatchesIRExec
      (SourceSemantics.effectiveFields model) sourceResult irExec

/-- The parameter-loaded initial state exactly reflects the decoded bindings. -/
private theorem supported_function_correct_state_bindings
    {model : CompilationModel} {selectors : List Nat} (hSupported : SupportedSpec model selectors)
    {fn : FunctionSpec} {tx : IRTransaction} {initialWorld : Verity.ContractState}
    {bindings : List (String × Nat)} (hfn : fn ∈ selectorDispatchedFunctions model)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings) :
    FunctionBody.bindingsExactlyMatchIRVars bindings
      (ParamLoading.applyBindingsToIRState
        (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
        bindings) :=
  supported_function_param_state_exact _ fn.params bindings
    (FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld)
    (hSupported.selectorFunctionParamNamesNodup hfn) hbind

/-- The parameter-loaded initial state matches the transaction's source runtime. -/
private theorem supported_function_correct_state_runtime
    (model : CompilationModel) (fn : FunctionSpec) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := [], selector := tx.functionSelector, errors := model.errors }
      (ParamLoading.applyBindingsToIRState
        (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
        bindings) :=
  runtimeStateMatchesIR_applyBindingsToIRState
    (runtimeStateMatchesIR_prebindRawArgs
      (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized
        hcalldataSizeFits) fn.params) bindings

/-- Compile-core bodies satisfy the body-level agreement at any extra fuel. -/
private theorem supported_function_correct_bodyExecMatches_of_core
    {model : CompilationModel} {selectors : List Nat} (hSupported : SupportedSpec model selectors)
    {fn : FunctionSpec} {bodyStmts : List YulStmt} {tx : IRTransaction}
    {initialWorld : Verity.ContractState} {bindings : List (String × Nat)} (extraFuel : Nat)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcore : FunctionBody.StmtListCompileCore (fn.params.map (·.name)) fn.body)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hfuel : sizeOf bodyStmts ≤ bodyStmts.length + extraFuel) :
    SupportedFunctionBodyExecMatches model fn tx initialWorld bindings bodyStmts extraFuel :=
  supported_function_body_correct_from_exact_state_core_extraFuel model fn bodyStmts tx
    initialWorld _ bindings extraFuel
    (by simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
    hSupported.noEvents hSupported.noErrors hbind hcore hbodyCompile
    (supported_function_correct_state_runtime model fn tx initialWorld bindings htxNormalized
      hcalldataSizeFits)
    (supported_function_correct_state_bindings hSupported hfn hbind) hfuel

/-- Terminal-core bodies satisfy the body-level agreement above the body's own
size slack. -/
private theorem supported_function_correct_bodyExecMatches_of_terminal
    {model : CompilationModel} {selectors : List Nat} (hSupported : SupportedSpec model selectors)
    {fn : FunctionSpec} {bodyStmts : List YulStmt} {tx : IRTransaction}
    {initialWorld : Verity.ContractState} {bindings : List (String × Nat)} {extraFuel : Nat}
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts) :
    SupportedFunctionBodyExecMatches model fn tx initialWorld bindings bodyStmts extraFuel :=
  supported_function_body_correct_from_exact_state_terminal_core_extraFuel model fn bodyStmts
    tx initialWorld _ bindings extraFuel hextraFuel
    (by simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
    hSupported.noEvents hSupported.noErrors hbind hterminal hbodyCompile
    (supported_function_correct_state_runtime model fn tx initialWorld bindings htxNormalized
      hcalldataSizeFits)
    (supported_function_correct_state_bindings hSupported hfn hbind)

/-- Validated supported functions expose the helper-free step interface over the
effective fields. -/
private theorem supported_function_correct_helperFreeStepInterface
    {model : CompilationModel} {selectors : List Nat} (hSupported : SupportedSpec model selectors)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    {fn : FunctionSpec} (hfn : fn ∈ selectorDispatchedFunctions model) :
    StmtListHelperFreeStepInterface (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body := by
  have hnoConflict : firstFieldWriteSlotConflict model.fields = none := by
    simpa [SourceSemantics.effectiveFields, hSupported.normalizedFields] using
      firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs hvalidateInputs
  simpa [SourceSemantics.effectiveFields, hSupported.normalizedFields] using
    (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperFreeStepInterface
      hnoConflict

/-- Helper-surface-closed supported bodies run the same with or without the
helper table. -/
private theorem supported_function_correct_execStmtList_of_withHelpers
    {model : CompilationModel} {selectors : List Nat} (hSupported : SupportedSpec model selectors)
    {fn : FunctionSpec} (hfn : fn ∈ selectorDispatchedFunctions model)
    {state : SourceSemantics.RuntimeState} {result : SourceSemantics.StmtResult}
    (h : SourceSemantics.execStmtListWithHelpers model (SourceSemantics.effectiveFields model)
      hSupported.helperFuel state fn.body = result) :
    SourceSemantics.execStmtList (SourceSemantics.effectiveFields model) state fn.body =
      result := by
  simpa [hSupported.noEvents] using
    (SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
      model _ hSupported.helperFuel _ _
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed).symm.trans h

/-- General supported bodies satisfy the body-level agreement through the
helper-aware generic induction, since helper-closed bodies ignore the helper
table. -/
private theorem supported_function_correct_bodyExecMatches_of_helperFree
    {model : CompilationModel} {selectors : List Nat} (hSupported : SupportedSpec model selectors)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    {fn : FunctionSpec} {bodyStmts : List YulStmt} {tx : IRTransaction}
    {initialWorld : Verity.ContractState} {bindings : List (String × Nat)} {extraFuel : Nat}
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts) :
    SupportedFunctionBodyExecMatches model fn tx initialWorld bindings bodyStmts extraFuel := by
  rcases supported_function_body_correct_from_exact_state_generic_with_helpers model fn
      bodyStmts hSupported.helperFuel tx initialWorld _ bindings extraFuel hextraFuel
      (by simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
      hSupported.noEvents hSupported.noErrors hSupported.noAdtTypes
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed
      (supported_function_correct_helperFreeStepInterface hSupported hvalidateInputs hfn)
      (by rw [hSupported.noAdtTypes]; exact hbodyCompile)
      (exactState_scopeNamesPresent_of_bindSupportedParams hbind)
      (FunctionBody.bindingsBounded_of_bindSupportedParams hbind)
      (supported_function_correct_state_runtime model fn tx initialWorld bindings htxNormalized
        hcalldataSizeFits)
      (supported_function_correct_state_bindings hSupported hfn hbind) with
    ⟨sourceResult, irExec, hsrc, hexec, hmatch⟩
  exact ⟨sourceResult, irExec,
    supported_function_correct_execStmtList_of_withHelpers hSupported hfn hsrc, hexec, hmatch⟩

/-- The compiled function's own size slack dominates the body's size slack. -/
private theorem supported_function_correct_extraFuel_le
    {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    {selector : Nat} {fn : FunctionSpec} {habi : fn.abiDecoding = .standard}
    {irFn : IRFunction} {returns : List ParamType} {bodyStmts : List YulStmt}
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList fields events errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec fields events errors [] selector fn = Except.ok irFn) :
    sizeOf bodyStmts - bodyStmts.length ≤ sizeOf irFn.body - irFn.body.length := by
  obtain rfl := compileFunctionSpec_eq_compiledFunctionIR_of_body (habi := habi)
    hvalidate hreturns hbodyCompile hcompile
  simpa [compiledFunctionIR] using
    yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts

/-- Non-core supported bodies satisfy the body-level agreement at the compiled
function's size slack, via the terminal-core or the helper-aware generic route. -/
private theorem supported_function_correct_bodyExecMatches_of_compile
    {model : CompilationModel} {selectors : List Nat} (hSupported : SupportedSpec model selectors)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    {fn : FunctionSpec} {selector : Nat} {returns : List ParamType} {bodyStmts : List YulStmt}
    {irFn : IRFunction} {tx : IRTransaction} {initialWorld : Verity.ContractState}
    {bindings : List (String × Nat)} (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec model.fields model.events model.errors [] selector fn =
      Except.ok irFn)
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings) :
    SupportedFunctionBodyExecMatches model fn tx initialWorld bindings bodyStmts
      (sizeOf irFn.body - irFn.body.length) := by
  have hlower := supported_function_correct_extraFuel_le
    (habi := (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi)
    hvalidate hreturns hbodyCompile hcompile
  by_cases hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body
  · exact supported_function_correct_bodyExecMatches_of_terminal hSupported hlower hfn
      htxNormalized hcalldataSizeFits hbind hterminal hbodyCompile
  · exact supported_function_correct_bodyExecMatches_of_helperFree hSupported hvalidateInputs
      hlower hfn htxNormalized hcalldataSizeFits hbind hbodyCompile

/-- Running the compiled function at its own size slack is the adequate fuel. -/
private theorem supported_function_correct_execIRFunction_eq
    (selector : Nat) (fn : FunctionSpec) (returns : List ParamType) (bodyStmts : List YulStmt)
    (args : List Nat) (state : IRState) :
    execIRFunction (compiledFunctionIR selector fn returns bodyStmts) args state =
      Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads fn.params ++ bodyStmts).length +
          (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body -
            (compiledFunctionIR selector fn returns bodyStmts).body.length) + 1)
        (compiledFunctionIR selector fn returns bodyStmts) args state := by
  have hlenle := yulStmtList_length_le_sizeOf (genParamLoads fn.params ++ bodyStmts)
  have hfuel :
      (genParamLoads fn.params ++ bodyStmts).length +
          (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body -
            (compiledFunctionIR selector fn returns bodyStmts).body.length) + 1 =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1 := by
    simp only [compiledFunctionIR]
    omega
  rw [hfuel]
  exact (Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate _ _ _).symm

/-- Shared tail of `supported_function_correct`: body-level agreement at the
compiled function's size slack lifts to the total function executor. -/
private theorem supported_function_correct_of_bodyExecMatches
    {model : CompilationModel} {selectors : List Nat} (hSupported : SupportedSpec model selectors)
    {fn : FunctionSpec} {selector : Nat} {returns : List ParamType} {bodyStmts : List YulStmt}
    {irFn : IRFunction} {tx : IRTransaction} {initialWorld : Verity.ContractState}
    {bindings : List (String × Nat)} (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec model.fields model.events model.errors [] selector fn =
      Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbody : SupportedFunctionBodyExecMatches model fn tx initialWorld bindings bodyStmts
      (sizeOf irFn.body - irFn.body.length)) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have habi := (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi
  rcases hbody with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  obtain rfl := compileFunctionSpec_eq_compiledFunctionIR_of_body (habi := habi)
    hvalidate hreturns hbodyCompile hcompile
  rw [supported_function_correct_execIRFunction_eq]
  exact compileFunctionSpec_sourceResultMatches_of_exec (habi := habi) model fn tx initialWorld
    hbind hSupported.noEvents hsource hmatch (exec_compiledFunctionIR_of_body_extraFuel _
      selector fn returns bodyStmts bindings irExec _
      (hSupported.selectorFunctionParamsSupported hfn) hcalldataSizeFits hbind hbodyExec)

theorem supported_function_correct
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec) (selector : Nat) (returns : List ParamType)
    (bodyStmts : List YulStmt) (irFn : IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
    (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  refine supported_function_correct_of_bodyExecMatches hSupported hfn hvalidate hreturns
    hbodyCompile hcompile hbind hcalldataSizeFits ?_
  by_cases hcore : FunctionBody.StmtListCompileCore (fn.params.map (·.name)) fn.body
  · have hslack := supported_function_correct_extraFuel_le
      (habi := (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi)
      hvalidate hreturns hbodyCompile hcompile
    have hlen := yulStmtList_length_le_sizeOf bodyStmts
    exact supported_function_correct_bodyExecMatches_of_core hSupported _ hfn htxNormalized
      hcalldataSizeFits hbind hcore hbodyCompile (by omega)
  · exact supported_function_correct_bodyExecMatches_of_compile hSupported hvalidateInputs hfn
      hvalidate hreturns hbodyCompile hcompile htxNormalized hcalldataSizeFits hbind

/-- The initial IR state's storage is the encoded transaction-context source storage. -/
private theorem bodyGoal_initialIRStateForTx_storage_eq
    (model : CompilationModel) (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    (FunctionBody.initialIRStateForTx model tx initialWorld).storage = fun s =>
      Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
        (SourceSemantics.encodeStorage model
          (SourceSemantics.withTransactionContext initialWorld tx) s.toNat) := by
  funext s
  simp [FunctionBody.initialIRStateForTx, FunctionBody.encodeStorage_withTransactionContext]

/-- The initial IR state's event log is the encoded transaction-context source log. -/
private theorem bodyGoal_initialIRStateForTx_events_eq
    (model : CompilationModel) (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    (FunctionBody.initialIRStateForTx model tx initialWorld).events =
      SourceSemantics.encodeEvents
        (SourceSemantics.withTransactionContext initialWorld tx).events := by
  simp [FunctionBody.initialIRStateForTx]

/-- A successful `compileFunctionSpec` run is the canonical compiled function. -/
private theorem bodyGoal_irFn_eq {model : CompilationModel} {selector : Nat}
    {fn : FunctionSpec} {returns : List ParamType} {bodyStmts : List YulStmt}
    {irFn : IRFunction} (habi : fn.abiDecoding = .standard)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn) :
    irFn = compiledFunctionIR selector fn returns bodyStmts := by
  have hcompiled := compileFunctionSpec_ok_of_components (habi := habi) model.fields
    model.events model.errors selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  rw [hcompile] at hcompiled
  injection hcompiled

/-- Helper-aware source semantics matches the legacy IR result packaging of a
body execution that matches the source body result. -/
private theorem bodyGoal_source_match
    (model : CompilationModel) (fn : FunctionSpec) {habi : fn.abiDecoding = .standard}
    (helperFuel : Nat) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat)) (sourceResult : SourceSemantics.StmtResult)
    (irExec : IRExecResult)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hsource :
      SourceSemantics.execStmtListWithHelpers model (SourceSemantics.effectiveFields model)
        helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector, errors := model.errors } fn.body = sourceResult)
    (hmatch : FunctionBody.stmtResultMatchesIRExec (SourceSemantics.effectiveFields model)
      sourceResult irExec) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunctionWithHelpers model helperFuel fn tx initialWorld)
      (execResultToIRResult (FunctionBody.initialIRStateForTx model tx initialWorld) irExec) := by
  have hpack :=
    FunctionBody.stmtResultToSourceResult_matches_irExecResult
      (spec := model) (fields := SourceSemantics.effectiveFields model)
      (initialWorld := SourceSemantics.withTransactionContext initialWorld tx)
      (rollback := FunctionBody.initialIRStateForTx model tx initialWorld) sourceResult irExec
      (bodyGoal_initialIRStateForTx_storage_eq model tx initialWorld)
      (bodyGoal_initialIRStateForTx_events_eq model tx initialWorld) rfl hmatch
  simp only [SourceSemantics.interpretFunctionWithHelpers, FunctionSpec.bindingParams, habi,
    SourceSemantics.bindExternalParams_eq_some_of_bindSupportedParams _ hbind, hsource]
  exact hpack

/-- Fuel adequacy: an exact-`sizeOf`-fuel source match transfers to `execIRFunction`. -/
private theorem bodyGoal_execIRFunction_of_fuel {src : SourceSemantics.SourceContractResult}
    (selector : Nat) (fn : FunctionSpec) (returns : List ParamType)
    (bodyStmts : List YulStmt) (args : List Nat) (initialState : IRState)
    (extraFuel : Nat) (irExec : IRExecResult)
    (hfuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
    (hexec :
      Compiler.Proofs.YulGeneration.execIRFunctionFuel
          ((genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1)
          (compiledFunctionIR selector fn returns bodyStmts) args initialState =
        execResultToIRResult initialState irExec)
    (hmatch :
      FunctionBody.sourceResultMatchesIRResult src (execResultToIRResult initialState irExec)) :
    FunctionBody.sourceResultMatchesIRResult src
      (execIRFunction (compiledFunctionIR selector fn returns bodyStmts) args initialState) := by
  have hadequacy := Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
    (compiledFunctionIR selector fn returns bodyStmts) args initialState
  unfold Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal at hadequacy
  rw [hfuel] at hexec
  rw [← hadequacy, hexec]
  exact hmatch

theorem supported_function_correct_with_helper_proofs_body_goal
    (model : CompilationModel) (selectors : List Nat) (hSupported : SupportedSpec model selectors)
    (_hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (_hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec) (selector : Nat) (returns : List ParamType) (bodyStmts : List YulStmt)
    (irFn : IRFunction) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat)) (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (_htxNormalized : TxContextNormalized tx) (extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersIRPreservationGoal
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have habi := (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi
  rcases hbodyCorrect with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  rw [bodyGoal_irFn_eq habi hvalidate hreturns hbodyCompile hcompile]
  exact bodyGoal_execIRFunction_of_fuel selector fn returns bodyStmts tx.args _ extraFuel irExec
    hcompiledBodyFuel
    (exec_compiledFunctionIR_of_body_extraFuel _ selector fn returns bodyStmts bindings irExec
      extraFuel (hSupported.selectorFunctionParamsSupported hfn) hcalldataSizeFits hbind hbodyExec)
    (bodyGoal_source_match (habi := habi) model fn hSupported.helperFuel tx initialWorld bindings
      sourceResult irExec hbind hsource hmatch)

private theorem supported_function_correct_with_scalar_events_body_goal_source_match
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors)
    (fn : FunctionSpec)
    {habi : fn.abiDecoding = .standard} (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (initialState : IRState) (irExec : IRExecResult) (sourceResult : SourceSemantics.StmtResult)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hsource :
      SourceSemantics.execStmtListWithHelpers model (SourceSemantics.effectiveFields model)
        hSupported.helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector, errors := model.errors } fn.body = sourceResult)
    (hmatch : FunctionBody.stmtResultMatchesIRExec (SourceSemantics.effectiveFields model)
      sourceResult irExec)
    (hinitialState : initialState = FunctionBody.initialIRStateForTx model tx initialWorld) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemanticsWithScalarEvents model selectors hSupported fn tx initialWorld)
      (execResultToIRResult initialState irExec) := by
  subst hinitialState
  have hrollbackStorage :
        (FunctionBody.initialIRStateForTx model tx initialWorld).storage = fun s =>
          Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
            (SourceSemantics.encodeStorage model
              (SourceSemantics.withTransactionContext initialWorld tx) s.toNat) := by
    funext s
    simp [FunctionBody.initialIRStateForTx,
      FunctionBody.encodeStorage_withTransactionContext]
  have hrollbackEvents :
      (FunctionBody.initialIRStateForTx model tx initialWorld).events =
        SourceSemantics.encodeEvents
          (SourceSemantics.withTransactionContext initialWorld tx).events := by
    simp [FunctionBody.initialIRStateForTx]
  have hpack :=
    FunctionBody.stmtResultToSourceResult_matches_irExecResult
      (spec := model) (fields := SourceSemantics.effectiveFields model)
      (initialWorld := SourceSemantics.withTransactionContext initialWorld tx)
      (rollback := FunctionBody.initialIRStateForTx model tx initialWorld)
      (sourceResult := sourceResult) (irResult := irExec)
      hrollbackStorage hrollbackEvents rfl hmatch
  simp only [supportedSourceFunctionSemanticsWithScalarEvents,
    SourceSemantics.interpretFunctionWithHelpers, FunctionSpec.bindingParams, habi,
    SourceSemantics.bindExternalParams_eq_some_of_bindSupportedParams _ hbind]
  rw [hsource]
  exact hpack

private theorem supported_function_correct_with_scalar_events_body_goal_compiled_exec
    (model : CompilationModel) (selectors : List Nat) (hSupported : SupportedSpecWithScalarEvents model selectors)
    (fn : FunctionSpec) (selector : Nat) (returns : List ParamType) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) (extraFuel : Nat) (irExec : IRExecResult)
    (hbodyExec : execIRStmts (bodyStmts.length + extraFuel + 1)
      (ParamLoading.applyBindingsToIRState
        (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params) bindings)
      bodyStmts = irExec) :
    Compiler.Proofs.YulGeneration.execIRFunctionFuel
      ((genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1)
      (compiledFunctionIR selector fn returns bodyStmts) tx.args
      (FunctionBody.initialIRStateForTx model tx initialWorld) =
    execResultToIRResult (FunctionBody.initialIRStateForTx model tx initialWorld) irExec := by
  exact exec_compiledFunctionIR_of_body_extraFuel
    (state := FunctionBody.initialIRStateForTx model tx initialWorld)
    (selector := selector) (spec := fn) (returns := returns) (bodyStmts := bodyStmts)
    (bindings := bindings) (tailResult := irExec) (extraFuel := extraFuel)
    (hSupported.selectorFunctionParamsSupported hfn) hcalldataSizeFits hbind hbodyExec

private theorem supported_function_correct_with_scalar_events_body_goal_fuel
    (model : CompilationModel) (selectors : List Nat) (hSupported : SupportedSpecWithScalarEvents model selectors)
    (fn : FunctionSpec) {habi : fn.abiDecoding = .standard}
    (selector : Nat) (returns : List ParamType) (bodyStmts : List YulStmt)
    (irFn : IRFunction) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hvalidate : validateFunctionSpec fn = Except.ok ()) (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (extraFuel : Nat) (hcompiledBodyFuel : (genParamLoads fn.params ++ bodyStmts).length + extraFuel = sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
    (irExec : IRExecResult)
    (hcompiledExec : Compiler.Proofs.YulGeneration.execIRFunctionFuel
      ((genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1)
      (compiledFunctionIR selector fn returns bodyStmts) tx.args
      (FunctionBody.initialIRStateForTx model tx initialWorld) =
      execResultToIRResult (FunctionBody.initialIRStateForTx model tx initialWorld) irExec)
    (hsourceMatch :
      FunctionBody.sourceResultMatchesIRResult (supportedSourceFunctionSemanticsWithScalarEvents model selectors hSupported fn tx initialWorld)
        (execResultToIRResult (FunctionBody.initialIRStateForTx model tx initialWorld) irExec)) :
    FunctionBody.sourceResultMatchesIRResult (supportedSourceFunctionSemanticsWithScalarEvents model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hcompiled := compileFunctionSpec_ok_of_components (habi := habi) model.fields model.events model.errors selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled
  subst hirFn
  have hfuelEq'' :
      extraFuel + (bodyStmts.length + (1 + (genParamLoads fn.params).length)) =
        1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by
    have hbodyFuel'' :
        (genParamLoads fn.params).length + bodyStmts.length + extraFuel =
          sizeOf (genParamLoads fn.params ++ bodyStmts) := by
      simpa [compiledFunctionIR, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using hcompiledBodyFuel
    omega
  have hadequacy := Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
    (compiledFunctionIR selector fn returns bodyStmts) tx.args
    (FunctionBody.initialIRStateForTx model tx initialWorld)
  rw [← hcompiledExec] at hsourceMatch
  have hfuel' :
      FunctionBody.sourceResultMatchesIRResult
        (supportedSourceFunctionSemanticsWithScalarEvents model selectors hSupported fn tx initialWorld)
        (Compiler.Proofs.YulGeneration.execIRFunctionFuel
          (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
          (compiledFunctionIR selector fn returns bodyStmts) tx.args
          (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    simpa [compiledFunctionIR, hfuelEq'', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using hsourceMatch
  simpa [Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal] using
    (hadequacy ▸ hfuel')

theorem supported_function_correct_with_scalar_events_body_goal
    (model : CompilationModel) (selectors : List Nat) (hSupported : SupportedSpecWithScalarEvents model selectors)
    (fn : FunctionSpec) (selector : Nat) (returns : List ParamType) (bodyStmts : List YulStmt)
    (irFn : IRFunction) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (_htxNormalized : TxContextNormalized tx)
    (extraFuel : Nat)
    (hcompiledBodyFuel : (genParamLoads fn.params ++ bodyStmts).length + extraFuel = sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersIRPreservationGoal
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params) bindings)
        bindings extraFuel)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemanticsWithScalarEvents model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have habi : fn.abiDecoding = .standard :=
    (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  rcases hbodyCorrect with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hsourceMatch :
      FunctionBody.sourceResultMatchesIRResult
        (supportedSourceFunctionSemanticsWithScalarEvents model selectors hSupported fn tx initialWorld)
        (execResultToIRResult initialState irExec) :=
    supported_function_correct_with_scalar_events_body_goal_source_match (habi := habi)
      model selectors hSupported fn tx initialWorld bindings initialState irExec sourceResult
      hbind hsource hmatch rfl
  have hcompiledExec := supported_function_correct_with_scalar_events_body_goal_compiled_exec
    model selectors hSupported fn selector returns bodyStmts tx initialWorld bindings hfn hbind
    hcalldataSizeFits extraFuel irExec hbodyExec
  exact supported_function_correct_with_scalar_events_body_goal_fuel (habi := habi)
    model selectors hSupported fn selector returns bodyStmts irFn tx initialWorld hvalidate hreturns
    hbodyCompile hcompile extraFuel hcompiledBodyFuel irExec hcompiledExec hsourceMatch
theorem supported_function_correct_with_helper_proofs_body_goal_and_helper_ir
    (model : CompilationModel) (selectors : List Nat) (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract) (fn : FunctionSpec) (selector : Nat)
    (returns : List ParamType) (bodyStmts : List YulStmt) (irFn : IRFunction)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx) (extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal runtimeContract
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hbodyDisjoint : YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts)
    (hhelperIR :
      execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld))
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rw [hhelperIR]
  exact supported_function_correct_with_helper_proofs_body_goal
    model selectors hSupported hHelperProofs hvalidateInputs fn selector returns
    bodyStmts irFn tx initialWorld bindings hfn hvalidate hreturns hbodyCompile
    hcompile hbind htxNormalized extraFuel hcompiledBodyFuel
    (supported_function_body_with_helpers_ir_goal_of_helper_ir_goal_callsDisjoint
      runtimeContract model fn bodyStmts hSupported.helperFuel tx initialWorld _
      bindings extraFuel hbodyCorrect hbodyDisjoint)
    hcalldataSizeFits

/-- A successful helper-aware `compileFunctionSpec` run is the canonical compiled function. -/
private theorem bodyGoal_irFn_eq_with_internals {model : CompilationModel}
    {internalFunctions : List FunctionSpec} {selector : Nat} {fn : FunctionSpec}
    {returns : List ParamType} {bodyStmts : List YulStmt} {irFn : IRFunction}
    (habi : fn.abiDecoding = .standard)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body internalFunctions = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn
        (internalFunctions := internalFunctions) = Except.ok irFn) :
    irFn = compiledFunctionIR selector fn returns bodyStmts := by
  have hcompiled := compileFunctionSpec_ok_of_components_with_internals (habi := habi)
    model.fields model.events model.errors internalFunctions selector fn returns bodyStmts
    hvalidate hreturns hbodyCompile
  rw [hcompile] at hcompiled
  injection hcompiled

/-- The ABI param-load prefix followed by the helper-aware body runs, at the
compiled function's `sizeOf` fuel plus slack, to the body's result. -/
private theorem bodyGoal_withInternals_prefix_exec
    (runtimeContract : IRContract) (state : IRState) (selector : Nat) (fn : FunctionSpec)
    (returns : List ParamType) (bodyStmts : List YulStmt) (bindings : List (String × Nat))
    (irFuelSlack extraFuel : Nat) (irExec : IRExecResultWithInternals)
    (hsupported : ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams fn.params state.calldata = some bindings)
    (hparamDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract (genParamLoads fn.params))
    (hfuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + irFuelSlack)
    (hbodyExec :
      execIRStmtsWithInternals runtimeContract (bodyStmts.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState (prebindRawArgs state fn.params) bindings)
        bodyStmts = irExec) :
    execIRStmtsWithInternals runtimeContract
        (sizeOf (genParamLoads fn.params ++ bodyStmts) + irFuelSlack + 1)
        (prebindRawArgs state fn.params) (genParamLoads fn.params ++ bodyStmts) = irExec := by
  have hprefix := exec_compiledFunctionIR_withInternals_of_body_extraFuel runtimeContract
    state selector fn returns bodyStmts bindings irExec extraFuel hsupported
    hcalldataSizeFits hbind hparamDisjoint hbodyExec
  have hfuel' :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (genParamLoads fn.params ++ bodyStmts) + irFuelSlack := by
    simpa [compiledFunctionIR] using hfuel
  simpa [compiledFunctionIR, ← hfuel'] using hprefix

/-- Function-level `WithInternals` execution packages the compiled body run. -/
private theorem bodyGoal_execIRFunctionWithInternals_eq
    (runtimeContract : IRContract) (model : CompilationModel) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (selector : Nat) (fn : FunctionSpec)
    (returns : List ParamType) (bodyStmts : List YulStmt) (irFuelSlack : Nat)
    (irExec : IRExecResultWithInternals)
    (hexec :
      execIRStmtsWithInternals runtimeContract
          (sizeOf (genParamLoads fn.params ++ bodyStmts) + irFuelSlack + 1)
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          (genParamLoads fn.params ++ bodyStmts) = irExec) :
    execIRFunctionWithInternals runtimeContract irFuelSlack
        (compiledFunctionIR selector fn returns bodyStmts) tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      FunctionBody.irResultOfExecResultWithInternals
        (FunctionBody.initialIRStateForTx model tx initialWorld) irExec := by
  have hstate :
      List.foldl (fun s x => s.setVar x.1.name x.2)
          (FunctionBody.initialIRStateForTx model tx initialWorld)
          ((List.map Param.toIRParam fn.params).zip tx.args) =
        prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params := by
    simp [prebindRawArgs, FunctionBody.initialIRStateForTx]
  rw [execIRFunctionWithInternals]
  simp [compiledFunctionIR, hstate]
  rw [hexec]
  rfl

/-- Helper-aware source semantics matches the `WithInternals` IR result packaging. -/
private theorem bodyGoal_withInternals_source_match
    (model : CompilationModel) (fn : FunctionSpec) {habi : fn.abiDecoding = .standard}
    (helperFuel : Nat) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat)) (sourceResult : SourceSemantics.StmtResult)
    (irExec : IRExecResultWithInternals)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hsource :
      SourceSemantics.execStmtListWithHelpers model (SourceSemantics.effectiveFields model)
        helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector, errors := model.errors } fn.body = sourceResult)
    (hmatch : stmtResultMatchesIRExecWithInternals (SourceSemantics.effectiveFields model)
      sourceResult irExec) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunctionWithHelpers model helperFuel fn tx initialWorld)
      (FunctionBody.irResultOfExecResultWithInternals
        (FunctionBody.initialIRStateForTx model tx initialWorld) irExec) :=
  interpretFunctionWithHelpers_eq_execResultToIRResultWithInternals_of_body (habi := habi)
    model fn helperFuel tx initialWorld sourceResult _ irExec bindings hbind hsource
    (bodyGoal_initialIRStateForTx_storage_eq model tx initialWorld)
    (bodyGoal_initialIRStateForTx_events_eq model tx initialWorld) hmatch

/-- Direct helper-aware function theorem for compiled bodies that already prove
the exact `execIRStmtsWithInternals` preservation goal. This is the function
level analogue of the legacy param-load/body execution bridge: the generated
ABI param-load prefix runs first under `WithInternals`, then execution continues
with the helper-aware compiled body. -/
theorem supported_function_correct_with_helper_proofs_body_goal_with_internals
    (model : CompilationModel) (selectors : List Nat) (hSupported : SupportedSpec model selectors)
    (_hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (_hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract) (fn : FunctionSpec) (selector : Nat)
    (returns : List ParamType) (bodyStmts : List YulStmt) (irFn : IRFunction)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (internalFunctions : List FunctionSpec) (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body internalFunctions = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn
        (internalFunctions := internalFunctions) = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (_htxNormalized : TxContextNormalized tx) (irFuelSlack : Nat) (extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + irFuelSlack)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal runtimeContract
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hparamDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract (genParamLoads fn.params))
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract irFuelSlack irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have habi := (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi
  rcases hbodyCorrect with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  rw [bodyGoal_irFn_eq_with_internals habi hvalidate hreturns hbodyCompile hcompile,
    bodyGoal_execIRFunctionWithInternals_eq runtimeContract model tx initialWorld selector fn
      returns bodyStmts irFuelSlack irExec
      (bodyGoal_withInternals_prefix_exec runtimeContract _ selector fn returns bodyStmts
        bindings irFuelSlack extraFuel irExec (hSupported.selectorFunctionParamsSupported hfn)
        hcalldataSizeFits hbind hparamDisjoint hcompiledBodyFuel hbodyExec)]
  exact bodyGoal_withInternals_source_match (habi := habi) model fn hSupported.helperFuel tx
    initialWorld bindings sourceResult irExec hbind hsource hmatch

/-- Helper-rich Function consumer.  Unlike the legacy wrapper above, this
theorem is gated by `SupportedSpecWithHelpers`, whose function inventory may
carry a `SupportedHelperRichBodyFragment`; no `SupportedStmtList` or
helper-free body witness is required. -/
theorem supported_function_correct_with_helper_rich_support_body_goal_with_internals
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecWithHelpers model selectors)
    (_hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract) (fn : FunctionSpec) (selector : Nat)
    (returns : List ParamType) (bodyStmts : List YulStmt) (irFn : IRFunction)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (internalFunctions : List FunctionSpec) (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body internalFunctions = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn
        (internalFunctions := internalFunctions) = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (_htxNormalized : TxContextNormalized tx) (irFuelSlack extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + irFuelSlack)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hparamDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract (genParamLoads fn.params))
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemanticsWithHelpers model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract irFuelSlack irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have habi := (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi
  rcases hbodyCorrect with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  rw [bodyGoal_irFn_eq_with_internals habi hvalidate hreturns hbodyCompile hcompile,
    bodyGoal_execIRFunctionWithInternals_eq runtimeContract model tx initialWorld selector fn
      returns bodyStmts irFuelSlack irExec
      (bodyGoal_withInternals_prefix_exec runtimeContract _ selector fn returns bodyStmts
        bindings irFuelSlack extraFuel irExec (hSupported.selectorFunctionParamsSupported hfn)
        hcalldataSizeFits hbind hparamDisjoint hcompiledBodyFuel hbodyExec)]
  exact bodyGoal_withInternals_source_match (habi := habi) model fn hSupported.helperFuel tx
    initialWorld bindings sourceResult irExec hbind hsource hmatch

/-- Structured exact helper-aware function/IR wrapper under compiled-body
disjointness. The exact helper-aware body theorem can now be reused all the way
up to function-level results without requiring callers to restate the
conservative-extension equality manually. -/
theorem supported_function_correct_with_helper_proofs_body_goal_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel) (selectors : List Nat) (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract) (fn : FunctionSpec) (selector : Nat)
    (returns : List ParamType) (bodyStmts : List YulStmt) (irFn : IRFunction)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx) (extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal runtimeContract
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hfnBodyDisjoint : YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have habi : fn.abiDecoding = .standard :=
    (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi
  have hbodyDisjoint : YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts := by
    rw [bodyGoal_irFn_eq habi hvalidate hreturns hbodyCompile hcompile] at hfnBodyDisjoint
    simpa [compiledFunctionIR] using
      YulStmtListCallsDisjointFromInternalTable.of_append_prefix (contract := runtimeContract)
        (pre := genParamLoads fn.params) (suf := bodyStmts) hfnBodyDisjoint
  exact supported_function_correct_with_helper_proofs_body_goal_and_helper_ir
    model selectors hSupported hHelperProofs hvalidateInputs runtimeContract
    fn selector returns bodyStmts irFn tx initialWorld bindings hfn hvalidate
    hreturns hbodyCompile hcompile hbind htxNormalized extraFuel hcompiledBodyFuel hbodyCorrect
    hbodyDisjoint
    (execIRFunctionWithInternals_eq_execIRFunction_of_bodyCallsDisjoint runtimeContract irFn
      tx.args (FunctionBody.initialIRStateForTx model tx initialWorld) hfnBodyDisjoint)
    hcalldataSizeFits

private theorem function_body_scopeNamesPresent_of_bindSupportedParams
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (bindings : List (String × Nat))
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings) :
    FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
  intro name hmem
  have hmemBindings : name ∈ bindings.map Prod.fst := by
    rw [ParamLoading.bindSupportedParams_names hbind]
    simpa using hmem
  exact lookupBinding?_some_of_mem bindings name hmemBindings

private theorem function_body_state_runtime_of_bindSupportedParams
    (model : CompilationModel)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.runtimeStateMatchesIR
      (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := []
        selector := tx.functionSelector, errors := model.errors }
      (ParamLoading.applyBindingsToIRState
        (prebindRawArgs
          (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
        bindings) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  have hpreboundRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector, errors := model.errors }
        (prebindRawArgs initialState fn.params) := by
    simpa [initialState] using
      runtimeStateMatchesIR_prebindRawArgs
        (state := initialState)
        (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx,
                      bindings := [],
                      selector := tx.functionSelector, errors := model.errors })
        (fields := SourceSemantics.effectiveFields model)
        (params := fn.params)
        (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized
          hcalldataSizeFits)
  exact runtimeStateMatchesIR_applyBindingsToIRState
    (state := prebindRawArgs initialState fn.params)
    (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx,
                  bindings := [],
                  selector := tx.functionSelector, errors := model.errors })
    (fields := SourceSemantics.effectiveFields model)
    (bindings := bindings)
    hpreboundRuntime

private theorem function_body_state_bindings_of_bindSupportedParams
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings) :
    FunctionBody.bindingsExactlyMatchIRVars bindings
      (ParamLoading.applyBindingsToIRState
        (prebindRawArgs
          (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
        bindings) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  have hinitBindings :
      FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
    simpa [initialState] using
      FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
  have hparamNamesNodup :
      (fn.params.map (·.name)).Nodup :=
    hSupported.selectorFunctionParamNamesNodup hfn
  exact supported_function_param_state_exact
    initialState fn.params bindings hinitBindings hparamNamesNodup hbind

/-- Helper-aware `compileFunctionSpec` success in the `model.functions` world exposes
the body compile fact and the canonical compiled-function shape. -/
private theorem bodyGoal_compile_components_with_internals {model : CompilationModel}
    {selectors : List Nat} {hSupported : SupportedSpec model selectors}
    {fn : FunctionSpec} {selector : Nat} {irFn : IRFunction}
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors model.adtTypes
        selector fn .cancun model.functions = Except.ok irFn) :
    ∃ returns bodyStmts,
      compileStmtList model.fields model.events model.errors .calldata [] false
          (fn.params.map (·.name)) model.adtTypes fn.body model.functions =
        Except.ok bodyStmts ∧
      irFn = compiledFunctionIR selector fn returns bodyStmts := by
  have habi : fn.abiDecoding = .standard :=
    (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi
  rcases FunctionShape.compileFunctionSpec_ok_components_with_internals
      model.fields model.events model.errors model.adtTypes model.functions
      selector fn irFn hcompile with
    ⟨returns, bodyStmts, _hvalidate, _hreturns, hbodyCompile, hirFn⟩
  refine ⟨returns, bodyStmts, ?_, ?_⟩
  · simpa only [FunctionSpec.bindingParams, habi] using hbodyCompile
  · rw [hirFn]
    unfold FunctionShape.compiledFunctionIR compiledFunctionIR
    simp only [FunctionSpec.bindingParams, habi]
    cases returns with
    | nil => rfl
    | cons first rest => cases rest <;> rfl

/-- The canonical extra-fuel budget of a compiled function covers its body's slack. -/
private theorem bodyGoal_extraFuel_lower {irFn : IRFunction} {selector : Nat}
    {fn : FunctionSpec} {returns : List ParamType} {bodyStmts : List YulStmt}
    (hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts) :
    sizeOf bodyStmts - bodyStmts.length ≤ sizeOf irFn.body - irFn.body.length := by
  subst hirFn
  simpa [compiledFunctionIR] using
    yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts

/-- Function-level bridge from helper-aware `compileFunctionSpec` facts to the
mixed `WithInternals` body consumer.

The compile fact is reconstructed in the `model.functions` helper world and is
then threaded directly into the split-interface body theorem introduced for the
mixed helper-IR path. This packages the state/binding plumbing that callers
otherwise had to rebuild before they could consume
`supported_function_body_correct_from_exact_state_generic_split_helper_steps_and_helper_ir_with_internals`.
-/
theorem supported_function_body_with_internals_goal_of_compileFunctionSpec_with_internals
    (runtimeContract : IRContract) (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec model selectors) (fn : FunctionSpec) (selector : Nat)
    (irFn : IRFunction) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat)) (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors model.adtTypes
        selector fn .cancun model.functions = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hfuelPos : 0 < hSupported.helperFuel)
    (hhelperFree : StmtListHelperFreeStepInterfaceWithInternals runtimeContract model
      (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hcall : StmtListDirectInternalHelperCallStepInterfaceWithInternals runtimeContract model
      (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hassign : StmtListDirectInternalHelperAssignStepInterfaceWithInternals runtimeContract
      model (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hexpr : StmtListExprInternalHelperStepInterfaceWithInternals runtimeContract model
      (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hstruct : StmtListStructuralInternalHelperStepInterfaceWithInternals runtimeContract
      model (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hresidual : StmtListResidualHelperSurfaceStepInterfaceWithInternals runtimeContract
      model (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body) :
    ∃ returns bodyStmts extraFuel,
      irFn = compiledFunctionIR selector fn returns bodyStmts ∧
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal runtimeContract
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel := by
  obtain ⟨returns, bodyStmts, hbodyCompile, hirFn⟩ :=
    bodyGoal_compile_components_with_internals (hSupported := hSupported) hfn hcompile
  refine ⟨returns, bodyStmts, sizeOf irFn.body - irFn.body.length, hirFn, ?_⟩
  exact
    supported_function_body_correct_from_exact_state_generic_split_helper_steps_and_helper_ir_with_internals
      runtimeContract model fn bodyStmts hSupported.helperFuel tx initialWorld _ bindings _
      (bodyGoal_extraFuel_lower hirFn) hfuelPos
      (by simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
      hSupported.noEvents hSupported.noErrors hSupported.noAdtTypes
      hhelperFree hcall hassign hexpr hstruct hresidual hbodyCompile
      (function_body_scopeNamesPresent_of_bindSupportedParams fn tx bindings hbind)
      (FunctionBody.bindingsBounded_of_bindSupportedParams hbind)
      (function_body_state_runtime_of_bindSupportedParams
        model fn tx initialWorld bindings htxNormalized hcalldataSizeFits)
      (function_body_state_bindings_of_bindSupportedParams
        model selectors hSupported fn tx initialWorld bindings hfn hbind)

/-- Scalar-event sibling of the helper-aware body-goal wrapper. -/
theorem supported_function_correct_with_scalar_events_body_goal_and_helper_ir
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors)
    (runtimeContract : IRContract) (fn : FunctionSpec) (selector : Nat)
    (returns : List ParamType) (bodyStmts : List YulStmt) (irFn : IRFunction)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat)) (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx) (extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
    (hbodyCorrect : SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal runtimeContract
      model fn bodyStmts hSupported.helperFuel tx initialWorld
      (ParamLoading.applyBindingsToIRState
        (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
        bindings) bindings extraFuel)
    (hbodyDisjoint : YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts)
    (hhelperIR : execIRFunctionWithInternals runtimeContract 0 irFn tx.args
      (FunctionBody.initialIRStateForTx model tx initialWorld) =
      execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld))
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemanticsWithScalarEvents model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacyBody := supported_function_body_with_helpers_ir_goal_of_helper_ir_goal_callsDisjoint
    runtimeContract model fn bodyStmts hSupported.helperFuel tx initialWorld
    (ParamLoading.applyBindingsToIRState
      (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params) bindings)
    bindings extraFuel hbodyCorrect hbodyDisjoint
  have hlegacy := supported_function_correct_with_scalar_events_body_goal
    model selectors hSupported fn selector returns bodyStmts irFn tx initialWorld bindings hfn
    hvalidate hreturns hbodyCompile hcompile hbind htxNormalized extraFuel
    hcompiledBodyFuel hlegacyBody hcalldataSizeFits
  simpa [hhelperIR] using hlegacy

theorem stmtListHelperFreeNonEventStepInterface_of_helperFreeStepInterface
    {fields : List Field} :
    ∀ {scope : List String} {stmts : List Stmt},
      StmtListHelperFreeStepInterface fields scope stmts →
        StmtListHelperFreeNonEventStepInterface fields scope stmts
  | _, [], .nil => .nil
  | _, _ :: _, .cons hhead htail =>
      .cons (fun hhelper _hevent => hhead hhelper)
        (stmtListHelperFreeNonEventStepInterface_of_helperFreeStepInterface htail)

theorem stmtListHelperFreeCompiledCallsDisjoint_of_internalFunctions_nil
    (runtimeContract : IRContract)
    (hinternal : runtimeContract.internalFunctions = [])
    {fields : List Field} :
    ∀ {scope : List String} {stmts : List Stmt},
      StmtListHelperFreeCompiledLegacyCompatible fields scope stmts →
        StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts
  | _, [], .nil => .nil
  | _, _ :: _, .cons hhead htail =>
      .cons
        (fun hhelper compiledIR hcompile =>
          YulStmtListCallsDisjointFromInternalTable_of_internalFunctions_nil
            runtimeContract hinternal compiledIR (hhead hhelper compiledIR hcompile))
        (stmtListHelperFreeCompiledCallsDisjoint_of_internalFunctions_nil runtimeContract hinternal htail)

private theorem legacyCompatibleExternalStmtList_append
    {front back : List YulStmt}
    (hfront : LegacyCompatibleExternalStmtList front)
    (hback : LegacyCompatibleExternalStmtList back) :
    LegacyCompatibleExternalStmtList (front ++ back) := by
  induction hfront generalizing back with
  | nil => simpa using hback
  | comment msg rest _ ih => exact .comment msg (rest ++ back) (ih hback)
  | let_ name value rest _ ih => exact .let_ name value (rest ++ back) (ih hback)
  | assign name value rest _ ih => exact .assign name value (rest ++ back) (ih hback)
  | exprStmt value rest _ ih => exact .exprStmt value (rest ++ back) (ih hback)
  | if_ cond body rest hbody _ _ ihRest =>
      exact .if_ cond body (rest ++ back) hbody (ihRest hback)
  | block body rest hbody _ _ ihRest =>
      exact .block body (rest ++ back) hbody (ihRest hback)
  | for_ init cond post body rest hinit hpost hbody _ _ _ _ ihRest =>
      exact .for_ init cond post body (rest ++ back) hinit hpost hbody (ihRest hback)
  | funcDef name params rets body rest hbody _ _ ihRest =>
      exact .funcDef name params rets body (rest ++ back) hbody (ihRest hback)

private theorem yulStmtListCallsDisjoint_append
    {runtimeContract : IRContract} {front back : List YulStmt}
    (hfront : YulStmtListCallsDisjointFromInternalTable runtimeContract front)
    (hback : YulStmtListCallsDisjointFromInternalTable runtimeContract back) :
    YulStmtListCallsDisjointFromInternalTable runtimeContract (front ++ back) := by
  induction hfront generalizing back with
  | nil => simpa using hback
  | comment msg rest _ ih => exact .comment msg (rest ++ back) (ih hback)
  | let_ name value rest hval _ ih => exact .let_ name value (rest ++ back) hval (ih hback)
  | assign name value rest hval _ ih => exact .assign name value (rest ++ back) hval (ih hback)
  | exprStmt value rest hval _ ih => exact .exprStmt value (rest ++ back) hval (ih hback)
  | if_ cond body rest hcond hbody _ _ ihRest =>
      exact .if_ cond body (rest ++ back) hcond hbody (ihRest hback)
  | block body rest hbody _ _ ihRest =>
      exact .block body (rest ++ back) hbody (ihRest hback)
  | funcDef name params rets body rest hbody _ _ ihRest =>
      exact .funcDef name params rets body (rest ++ back) hbody (ihRest hback)
  | switch_ expr cases defaultCase rest hexpr hcases hdefault _ _ _ ihRest =>
      exact .switch_ expr cases defaultCase (rest ++ back) hexpr hcases hdefault (ihRest hback)
  | for_ init cond post body rest hinit hcond hpost hbody _ _ _ _ ihRest =>
      exact .for_ init cond post body (rest ++ back) hinit hcond hpost hbody (ihRest hback)

private theorem genScalarLoad_legacy
    (loadWord : YulExpr → YulExpr) (name : String) (ty : ParamType) (offset : Nat)
    (hsupported : SupportedExternalScalarParamType ty) :
    LegacyCompatibleExternalStmtList (genScalarLoad loadWord name ty offset) := by
  cases ty <;> simp [SupportedExternalScalarParamType] at hsupported ⊢
  all_goals
    first
    | exact .let_ _ _ [] .nil
    | exact .let_ _ _ _ (.if_ _ _ [] (.exprStmt _ _ .nil) .nil)

private theorem genParamLoadBodyFrom_scalar_legacy
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr) (headSize baseOffset : Nat) :
    ∀ (params : List Param) (headOffset : Nat),
      (∀ param ∈ params, SupportedExternalScalarParamType param.ty) →
        LegacyCompatibleExternalStmtList
          (genParamLoadBodyFrom loadWord sizeExpr headSize baseOffset params headOffset)
  | [], _, _ => .nil
  | param :: rest, headOffset, hsupported => by
      have htail := genParamLoadBodyFrom_scalar_legacy loadWord sizeExpr headSize
        baseOffset rest (headOffset + paramHeadSize param.ty)
        (by intro p hp; exact hsupported p (by simp [hp]))
      have hhead := genScalarLoad_legacy loadWord param.name param.ty headOffset
        (hsupported param (by simp))
      cases hty : param.ty <;> simp [SupportedExternalScalarParamType, hty] at hsupported
      all_goals
        simpa [genParamLoadBodyFrom, genSingleParamLoad, hty]
          using legacyCompatibleExternalStmtList_append hhead htail

private theorem genParamLoads_scalar_legacy
    (params : List Param)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty) :
    LegacyCompatibleExternalStmtList (genParamLoads params) := by
  have hbody := genParamLoadBodyFrom_scalar_legacy
    (fun pos => YulExpr.call "calldataload" [pos]) (YulExpr.call "calldatasize" [])
    ((params.map (fun p => paramHeadSize p.ty)).foldl (· + ·) 0) 4 params 4 hsupported
  simp [genParamLoads, genParamLoadsFrom]
  exact .if_ _ _ _ (.exprStmt _ _ .nil) hbody

/-- Legacy-compatibility analog of `compileStmtList_scalar_events_callsDisjoint`:
turn a per-statement compiled legacy-compatibility interface
(`StmtListCompiledLegacyCompatible`) into a whole-list legacy-compatibility
witness for the emitted Yul body. This is the missing list-composition bridge
that lifts the per-statement legacy obligations (the remaining #2080 discharge
target) to a `LegacyCompatibleExternalStmtList` for the compiled body, mirroring
the already-proven disjoint composition. -/
private theorem compileStmtList_legacyCompatible_of_interface
    {fields : List Field} :
    ∀ {scope : List String} {stmts : List Stmt} {compiledIR : List YulStmt},
      StmtListCompiledLegacyCompatible fields scope stmts →
      CompilationModel.compileStmtList fields [] [] .calldata [] false scope [] stmts =
          Except.ok compiledIR →
      LegacyCompatibleExternalStmtList compiledIR
  | _, [], _, _, hcompile => by
      try unfold CompilationModel.compileStmtList at hcompile
      unfold CompilationModel.compileStmtListWithFork at hcompile
      cases hcompile
      exact .nil
  | _, _ :: _, _, hInterface, hcompile => by
      obtain ⟨headIR, tailIR, hheadCompile, htailCompile, hbody⟩ :=
        FunctionBody.compileStmtList_cons_ok_inv hcompile
      cases hInterface with
      | cons hhead htail =>
          rw [hbody]
          exact legacyCompatibleExternalStmtList_append
            (hhead headIR hheadCompile)
            (compileStmtList_legacyCompatible_of_interface htail htailCompile)

private theorem legacyCompatibleExternalStmtList_map_exprStmt
    {α : Type} (f : α → YulExpr) :
    ∀ xs : List α,
      LegacyCompatibleExternalStmtList (xs.map (fun x => YulStmt.exprStmt (f x)))
  | [] => .nil
  | _ :: rest => .exprStmt _ _ (legacyCompatibleExternalStmtList_map_exprStmt f rest)

private theorem legacyCompatibleExternalStmtList_map_exprStmt_call
    {α : Type} (f : α → YulExpr) (name : String) :
    ∀ xs : List α,
      LegacyCompatibleExternalStmtList
        (xs.map (fun x => YulStmt.exprStmt (YulExpr.call name [f x, YulExpr.ident "__compat_value"])))
  | [] => .nil
  | _ :: rest => .exprStmt _ _
      (legacyCompatibleExternalStmtList_map_exprStmt_call f name rest)

private theorem legacyCompatibleExternalStmtList_map_let
    {α : Type} (name : α → String) (value : α → YulExpr) :
    ∀ xs : List α,
      LegacyCompatibleExternalStmtList
        (xs.map (fun x => YulStmt.let_ (name x) (value x)))
  | [] => .nil
  | _ :: rest => .let_ _ _ _
      (legacyCompatibleExternalStmtList_map_let name value rest)

private theorem legacyCompatibleExternalStmtList_block_value_writes
    {α : Type} (f : α → YulExpr) (name : String) (value : YulExpr) (xs : List α) :
    LegacyCompatibleExternalStmtList
      [YulStmt.block
        (YulStmt.let_ "__compat_value" value ::
          xs.map (fun x =>
            YulStmt.exprStmt
              (YulExpr.call name [f x, YulExpr.ident "__compat_value"])))] := by
  exact .block _ _ (.let_ _ _ _
    (legacyCompatibleExternalStmtList_map_exprStmt_call f name xs)) .nil

private theorem legacyCompatibleExternalStmtList_block_key_value_writes
    {α : Type} (f : α → YulExpr) (name : String)
    (key value : YulExpr) (xs : List α) :
    LegacyCompatibleExternalStmtList
      [YulStmt.block
        ([YulStmt.let_ "__compat_key" key, YulStmt.let_ "__compat_value" value] ++
          xs.map (fun x =>
            YulStmt.exprStmt
              (YulExpr.call name [f x, YulExpr.ident "__compat_value"])))] := by
  exact .block _ _ (.let_ _ _ _ (.let_ _ _ _
    (legacyCompatibleExternalStmtList_map_exprStmt_call f name xs))) .nil

private theorem legacyCompatibleExternalStmtList_block_key1_key2_value_writes
    {α : Type} (f : α → YulExpr) (name : String)
    (key1 key2 value : YulExpr) (xs : List α) :
    LegacyCompatibleExternalStmtList
      [YulStmt.block
        ([YulStmt.let_ "__compat_key1" key1, YulStmt.let_ "__compat_key2" key2,
          YulStmt.let_ "__compat_value" value] ++
          xs.map (fun x =>
            YulStmt.exprStmt
              (YulExpr.call name [f x, YulExpr.ident "__compat_value"])))] := by
  exact .block _ _ (.let_ _ _ _ (.let_ _ _ _ (.let_ _ _ _
    (legacyCompatibleExternalStmtList_map_exprStmt_call f name xs)))) .nil

private theorem legacyCompatibleExternalStmtList_block_value_lets_writes
    {α β : Type} (letName : α → String) (letValue : α → YulExpr)
    (f : β → YulExpr) (name : String) (value : YulExpr) (lets : List α) (xs : List β) :
    LegacyCompatibleExternalStmtList
      [YulStmt.block
        ([YulStmt.let_ "__compat_value" value] ++
          lets.map (fun x => YulStmt.let_ (letName x) (letValue x)) ++
          xs.map (fun x =>
            YulStmt.exprStmt
              (YulExpr.call name [f x, YulExpr.ident "__compat_value"])))] := by
  exact .block _ _ (.let_ _ _ _
    (legacyCompatibleExternalStmtList_append
      (legacyCompatibleExternalStmtList_map_let letName letValue lets)
      (legacyCompatibleExternalStmtList_map_exprStmt_call f name xs))) .nil

private theorem revertWithMessage_legacyCompatible
    (message : String) :
    LegacyCompatibleExternalStmtList (CompilationModel.revertWithMessage message) := by
  simp only [CompilationModel.revertWithMessage]
  exact .exprStmt _ _
    (.exprStmt _ _
      (.exprStmt _ _
        (legacyCompatibleExternalStmtList_append
          (legacyCompatibleExternalStmtList_map_exprStmt
            (fun x : List UInt8 × Nat =>
              YulExpr.call "mstore"
                [YulExpr.lit (68 + x.2 * 32), YulExpr.hex (wordFromBytes x.1)])
            (chunkBytes32 (bytesFromString message)).zipIdx)
          (.exprStmt _ _ .nil))))

/-- A single statement head whose legacy-context compilation only ever emits
legacy-compatible external Yul. This is the head obligation of
`StmtListCompiledLegacyCompatible.cons`. -/
private abbrev CompiledHeadLegacyCompatible
    (fields : List Field) (scope : List String) (stmt : Stmt) : Prop :=
  ∀ compiledIR,
    CompilationModel.compileStmt fields [] [] .calldata [] false scope [] stmt =
        Except.ok compiledIR →
      LegacyCompatibleExternalStmtList compiledIR

private theorem compiledHeadLegacyCompatible_letVar
    (fields : List Field) (scope : List String) (name : String) (value : Expr) :
    CompiledHeadLegacyCompatible fields scope (.letVar name value) := by
  intro compiledIR hcompile
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    bind, Except.bind] at hcompile
  split at hcompile <;> cases hcompile
  exact .let_ _ _ [] .nil

private theorem compiledHeadLegacyCompatible_assignVar
    (fields : List Field) (scope : List String) (name : String) (value : Expr) :
    CompiledHeadLegacyCompatible fields scope (.assignVar name value) := by
  intro compiledIR hcompile
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    bind, Except.bind] at hcompile
  split at hcompile <;> cases hcompile
  exact .assign _ _ [] .nil

private theorem compiledHeadLegacyCompatible_require
    (fields : List Field) (scope : List String) (cond : Expr) (message : String) :
    CompiledHeadLegacyCompatible fields scope (.require cond message) := by
  intro compiledIR hcompile
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    bind, Except.bind] at hcompile
  split at hcompile <;> cases hcompile
  exact .if_ _ _ [] (revertWithMessage_legacyCompatible message) .nil

private theorem compiledHeadLegacyCompatible_return
    (fields : List Field) (scope : List String) (value : Expr) :
    CompiledHeadLegacyCompatible fields scope (.return value) := by
  intro compiledIR hcompile
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    bind, Except.bind] at hcompile
  split at hcompile <;> cases hcompile
  exact .exprStmt _ _ (.exprStmt _ _ .nil)

private theorem compiledHeadLegacyCompatible_stop
    (fields : List Field) (scope : List String) :
    CompiledHeadLegacyCompatible fields scope .stop := by
  intro compiledIR hcompile
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hcompile
  cases hcompile
  exact .exprStmt _ _ .nil

private theorem compiledHeadLegacyCompatible_mstore
    (fields : List Field) (scope : List String) (offset value : Expr) :
    CompiledHeadLegacyCompatible fields scope (.mstore offset value) := by
  intro compiledIR hcompile
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    bind, Except.bind] at hcompile
  split at hcompile <;> try contradiction
  split at hcompile <;> cases hcompile
  exact .exprStmt _ _ .nil

private theorem compiledHeadLegacyCompatible_tstore
    (fields : List Field) (scope : List String) (offset value : Expr) :
    CompiledHeadLegacyCompatible fields scope (.tstore offset value) := by
  intro compiledIR hcompile
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    bind, Except.bind] at hcompile
  split at hcompile <;> try contradiction
  split at hcompile <;> cases hcompile
  exact .exprStmt _ _ .nil

/-- The `ite` head: both branch lists already carry the per-head interface, so
their compiled bodies are legacy-compatible and so is either emitted `if` shape. -/
private theorem compiledHeadLegacyCompatible_ite
    {fields : List Field} {scope : List String} {cond : Expr} {thenBranch elseBranch : List Stmt}
    (hthen : StmtListCompiledLegacyCompatible fields scope thenBranch)
    (helse : StmtListCompiledLegacyCompatible fields scope elseBranch) :
    CompiledHeadLegacyCompatible fields scope (.ite cond thenBranch elseBranch) := by
  intro compiledIR hcompile
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    bind, Except.bind] at hcompile
  split at hcompile <;> try contradiction
  split at hcompile <;> try contradiction
  rename_i thenIR hthenIR
  split at hcompile <;> try contradiction
  rename_i elseIR helseIR
  have hthenLegacy := compileStmtList_legacyCompatible_of_interface hthen hthenIR
  have helseLegacy := compileStmtList_legacyCompatible_of_interface helse helseIR
  by_cases hempty : elseBranch.isEmpty
  · simp only [hempty, ↓reduceIte] at hcompile
    cases hcompile
    exact .if_ _ thenIR [] hthenLegacy .nil
  · simp only [hempty, Bool.false_eq_true, ↓reduceIte] at hcompile
    cases hcompile
    exact .block _ [] (.let_ _ _ _ (.if_ _ _ _ hthenLegacy (.if_ _ _ _ helseLegacy .nil))) .nil

/-- Generic compile-core statement lists discharge the per-head legacy-compatible
compiled-output interface consumed by the helper-aware whole-contract bridge.

The compiler scope is deliberately independent of the proof scope: core
statement heads do not use the scope to choose their emitted Yul constructors,
and the tail is threaded through the compiler's `stmtNextScope`. -/
theorem stmtListCompileCore_compiledLegacyCompatible
    (fields : List Field) :
    ∀ {proofScope compilerScope : List String} {stmts : List Stmt},
      FunctionBody.StmtListCompileCore proofScope stmts →
        StmtListCompiledLegacyCompatible fields compilerScope stmts := by
  intro _ compilerScope _ h
  induction h generalizing compilerScope with
  | nil => exact .nil
  | letVar _ _ _ ih => exact .cons (compiledHeadLegacyCompatible_letVar fields _ _ _) ih
  | assignVar _ _ _ ih => exact .cons (compiledHeadLegacyCompatible_assignVar fields _ _ _) ih
  | require_ _ _ _ _ ih => exact .cons (compiledHeadLegacyCompatible_require fields _ _ _) ih
  | return_ _ _ _ ih => exact .cons (compiledHeadLegacyCompatible_return fields _ _) ih
  | stop _ ih => exact .cons (compiledHeadLegacyCompatible_stop fields _) ih
  | mstore _ _ _ _ _ ih => exact .cons (compiledHeadLegacyCompatible_mstore fields _ _ _) ih
  | tstore _ _ _ _ _ ih => exact .cons (compiledHeadLegacyCompatible_tstore fields _ _ _) ih

/-- Terminal-core statement lists also discharge the per-head legacy-compatible
compiled-output interface.  The `ite` case uses the existing list bridge on the
terminal branches and compile-core tail. -/
theorem stmtListTerminalCore_compiledLegacyCompatible
    (fields : List Field) :
    ∀ {proofScope compilerScope : List String} {stmts : List Stmt},
      FunctionBody.StmtListTerminalCore proofScope stmts →
        StmtListCompiledLegacyCompatible fields compilerScope stmts := by
  intro _ compilerScope _ h
  induction h generalizing compilerScope with
  | letVar _ _ _ ih => exact .cons (compiledHeadLegacyCompatible_letVar fields _ _ _) ih
  | assignVar _ _ _ ih => exact .cons (compiledHeadLegacyCompatible_assignVar fields _ _ _) ih
  | require_ _ _ _ _ ih => exact .cons (compiledHeadLegacyCompatible_require fields _ _ _) ih
  | return_ _ _ hrest =>
      exact .cons (compiledHeadLegacyCompatible_return fields _ _)
        (stmtListCompileCore_compiledLegacyCompatible fields hrest)
  | stop hrest =>
      exact .cons (compiledHeadLegacyCompatible_stop fields _)
        (stmtListCompileCore_compiledLegacyCompatible fields hrest)
  | mstore _ _ _ _ _ ih => exact .cons (compiledHeadLegacyCompatible_mstore fields _ _ _) ih
  | tstore _ _ _ _ _ ih => exact .cons (compiledHeadLegacyCompatible_tstore fields _ _ _) ih
  | ite _ _ _ _ hrest ihThen ihElse =>
      exact .cons (compiledHeadLegacyCompatible_ite ihThen ihElse)
        (stmtListCompileCore_compiledLegacyCompatible fields hrest)

/-- Singleton `setStorage` heads compile to ordinary legacy-compatible Yul when
the supported-fragment witness resolves the field to one concrete uint256
storage slot. -/
theorem stmtList_setStorageSingleSlot_compiledLegacyCompatible
    (fields : List Field)
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {slot : Nat}
    (_hvalue : FunctionBody.ExprCompileCore value)
    (_hscope : FunctionBody.exprBoundNamesInScope value scope)
    (hfield :
      findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    StmtListCompiledLegacyCompatible fields scope [Stmt.setStorage fieldName value] :=
  .cons
    (fun compiledIR hcompile => by
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hcompile
      simp [CompilationModel.compileSetStorage, hfield] at hcompile
      split at hcompile <;> try contradiction
      cases hvalueExpr : compileExprWithInternals fields .calldata [] value <;>
        simp [hvalueExpr] at hcompile
      cases hcompile
      exact .exprStmt _ _ .nil)
    .nil

/-- Singleton `setStorageAddr` heads compile to ordinary legacy-compatible Yul
when the supported-fragment witness resolves the field to one concrete address
storage slot. -/
theorem stmtList_setStorageAddrSingleSlot_compiledLegacyCompatible
    (fields : List Field)
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {slot : Nat}
    (_hvalue : FunctionBody.ExprCompileCore value)
    (_hscope : FunctionBody.exprBoundNamesInScope value scope)
    (hfield :
      findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.address }, slot)) :
    StmtListCompiledLegacyCompatible fields scope [Stmt.setStorageAddr fieldName value] :=
  .cons
    (fun compiledIR hcompile => by
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hcompile
      simp [CompilationModel.compileSetStorage, hfield] at hcompile
      split at hcompile <;> try contradiction
      cases hvalueExpr : compileExprWithInternals fields .calldata [] value <;>
        simp [hvalueExpr] at hcompile
      cases hcompile
      exact .exprStmt _ _ .nil)
    .nil

private theorem compileMappingSlotWrite_legacyCompatible
    {fields : List Field}
    {fieldName label : String}
    {keyExpr valueExpr : YulExpr}
    {wordOffset : Nat}
    {compiledIR : List YulStmt}
    (hcompile :
      CompilationModel.compileMappingSlotWrite fields fieldName keyExpr valueExpr
          label wordOffset true =
        Except.ok compiledIR) :
    LegacyCompatibleExternalStmtList compiledIR := by
  unfold CompilationModel.compileMappingSlotWrite at hcompile
  repeat' split at hcompile <;> try contradiction
  all_goals
    first
    | cases hcompile
      exact .exprStmt _ _ .nil
    | cases hcompile
      exact legacyCompatibleExternalStmtList_block_key_value_writes (α := Nat) (f := _) _ _ _ _

private theorem compileSetMapping2_legacyCompatible
    {fields : List Field}
    {fieldName : String}
    {dynamicSource : DynamicDataSource}
    {key1 key2 value : Expr}
    {compiledIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetMapping2 fields dynamicSource fieldName key1 key2 value [] =
        Except.ok compiledIR) :
    LegacyCompatibleExternalStmtList compiledIR := by
  unfold CompilationModel.compileSetMapping2 at hcompile
  cases hMapping2 : isMapping2 fields fieldName <;> simp [hMapping2] at hcompile
  cases hSlots : findFieldWriteSlots fields fieldName <;> simp [hSlots] at hcompile
  rename_i slots
  cases hkey1Expr : compileExprWithInternals fields dynamicSource [] key1 with
  | error err => simp [hkey1Expr, bind, Except.bind] at hcompile
  | ok key1Expr =>
      cases hkey2Expr : compileExprWithInternals fields dynamicSource [] key2 with
      | error err => simp [hkey1Expr, hkey2Expr, bind, Except.bind] at hcompile
      | ok key2Expr =>
          cases hvalueExpr : compileExprWithInternals fields dynamicSource [] value with
          | error err => simp [hkey1Expr, hkey2Expr, hvalueExpr, bind, Except.bind] at hcompile
          | ok valueExpr =>
              cases slots with
              | nil => simp [hkey1Expr, hkey2Expr, hvalueExpr, bind, Except.bind] at hcompile
              | cons slot rest =>
                  cases rest with
                  | nil =>
                      simp [hkey1Expr, hkey2Expr, hvalueExpr, bind, Except.bind] at hcompile
                      cases hcompile
                      exact .exprStmt _ _ .nil
                  | cons slot' rest =>
                      simp [hkey1Expr, hkey2Expr, hvalueExpr, bind, Except.bind] at hcompile
                      cases hcompile
                      exact legacyCompatibleExternalStmtList_block_key1_key2_value_writes
                        (α := Nat)
                        (f := fun slot =>
                          YulExpr.call "mappingSlot"
                            [YulExpr.call "mappingSlot"
                              [YulExpr.lit slot, YulExpr.ident "__compat_key1"],
                              YulExpr.ident "__compat_key2"])
                        (match findFieldWithResolvedSlot fields fieldName with
                          | some (f, _) => if f.isTransient then "tstore" else "sstore"
                          | none => "sstore")
                        key1Expr key2Expr valueExpr (slot :: slot' :: rest)

private theorem compileSetMapping2Word_legacyCompatible
    {fields : List Field} {fieldName : String} {dynamicSource : DynamicDataSource}
    {key1 key2 value : Expr} {wordOffset : Nat} {compiledIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetMapping2Word fields dynamicSource fieldName key1 key2
          wordOffset value [] =
        Except.ok compiledIR) :
    LegacyCompatibleExternalStmtList compiledIR := by
  unfold CompilationModel.compileSetMapping2Word at hcompile
  cases hMapping2 : isMapping2 fields fieldName <;> simp [hMapping2] at hcompile
  cases hSlots : findFieldWriteSlots fields fieldName <;> simp [hSlots] at hcompile
  rename_i slots
  cases hkey1Expr : compileExprWithInternals fields dynamicSource [] key1 with
  | error err => simp [hkey1Expr, bind, Except.bind] at hcompile
  | ok key1Expr =>
      cases hkey2Expr : compileExprWithInternals fields dynamicSource [] key2 with
      | error err => simp [hkey1Expr, hkey2Expr, bind, Except.bind] at hcompile
      | ok key2Expr =>
          cases hvalueExpr : compileExprWithInternals fields dynamicSource [] value with
          | error err => simp [hkey1Expr, hkey2Expr, hvalueExpr, bind, Except.bind] at hcompile
          | ok valueExpr =>
              cases slots with
              | nil => simp [hkey1Expr, hkey2Expr, hvalueExpr, bind, Except.bind] at hcompile
              | cons slot rest =>
                  cases rest with
                  | nil =>
                      simp [hkey1Expr, hkey2Expr, hvalueExpr, bind, Except.bind] at hcompile
                      cases hcompile
                      exact .exprStmt _ _ .nil
                  | cons slot' rest =>
                      simp [hkey1Expr, hkey2Expr, hvalueExpr, bind, Except.bind] at hcompile
                      cases hcompile
                      exact legacyCompatibleExternalStmtList_block_key1_key2_value_writes
                        (α := Nat)
                        (f := fun slot =>
                          let innerSlot :=
                            YulExpr.call "mappingSlot" [YulExpr.lit slot, YulExpr.ident "__compat_key1"]
                          let outerSlot :=
                            YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"]
                          if wordOffset = 0 then outerSlot else
                            YulExpr.call "add" [outerSlot, YulExpr.lit wordOffset])
                        (match findFieldWithResolvedSlot fields fieldName with
                          | some (f, _) => if f.isTransient then "tstore" else "sstore"
                          | none => "sstore")
                        key1Expr key2Expr valueExpr (slot :: slot' :: rest)

private theorem compileSetStructMember2_legacyCompatible
    {fields : List Field} {fieldName memberName : String} {dynamicSource : DynamicDataSource}
    {key1 key2 value : Expr} {wordOffset : Nat} {members : List StructMember}
    {compiledIR : List YulStmt}
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember : findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none })
    (hcompile : CompilationModel.compileSetStructMember2 fields dynamicSource fieldName key1 key2
          memberName value [] = Except.ok compiledIR) :
    LegacyCompatibleExternalStmtList compiledIR := by
  unfold CompilationModel.compileSetStructMember2 at hcompile
  cases hMapping2 : isMapping2 fields fieldName <;> simp [hMapping2] at hcompile
  simp [hmembers, hmember] at hcompile
  cases hSlots : findFieldWriteSlots fields fieldName <;> simp [hSlots] at hcompile
  rename_i slots
  cases hkey1Expr : compileExprWithInternals fields dynamicSource [] key1 with
  | error err => simp [hkey1Expr, bind, Except.bind] at hcompile
  | ok key1Expr =>
      cases hkey2Expr : compileExprWithInternals fields dynamicSource [] key2 with
      | error err => simp [hkey1Expr, hkey2Expr, bind, Except.bind] at hcompile
      | ok key2Expr =>
          cases hvalueExpr : compileExprWithInternals fields dynamicSource [] value with
          | error err => simp [hkey1Expr, hkey2Expr, hvalueExpr, bind, Except.bind] at hcompile
          | ok valueExpr =>
              cases slots with
              | nil => simp [hkey1Expr, hkey2Expr, hvalueExpr, bind, Except.bind] at hcompile
              | cons slot rest =>
                  cases rest with
                  | nil =>
                      simp [hkey1Expr, hkey2Expr, hvalueExpr, bind, Except.bind] at hcompile
                      cases hcompile
                      exact .exprStmt _ _ .nil
                  | cons slot' rest =>
                      simp [hkey1Expr, hkey2Expr, hvalueExpr, bind, Except.bind] at hcompile
                      cases hcompile
                      let finalSlot := fun slot =>
                        let innerSlot :=
                          YulExpr.call "mappingSlot" [YulExpr.lit slot, YulExpr.ident "__compat_key1"]
                        let outerSlot :=
                          YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"]
                        if wordOffset = 0 then outerSlot else
                          YulExpr.call "add" [outerSlot, YulExpr.lit wordOffset]
                      exact legacyCompatibleExternalStmtList_block_key1_key2_value_writes
                        (α := Nat)
                        (f := finalSlot)
                        (match findFieldWithResolvedSlot fields fieldName with
                          | some (f, _) => if f.isTransient then "tstore" else "sstore"
                          | none => "sstore")
                        key1Expr key2Expr valueExpr (slot :: slot' :: rest)

private theorem compileSetMappingChain_legacyCompatible
    {fields : List Field}
    {fieldName : String}
    {dynamicSource : DynamicDataSource}
    {keys : List Expr}
    {value : Expr}
    {compiledIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetMappingChain fields dynamicSource fieldName keys value [] =
        Except.ok compiledIR) :
    LegacyCompatibleExternalStmtList compiledIR := by
  unfold CompilationModel.compileSetMappingChain at hcompile
  cases hMapping : isMapping fields fieldName <;> simp [hMapping] at hcompile
  cases hSlots : findFieldWriteSlots fields fieldName <;> simp [hSlots] at hcompile
  rename_i slots
  cases hkeyExprs : compileExprListWithInternals fields dynamicSource [] keys with
  | error err => simp [hkeyExprs, bind, Except.bind] at hcompile
  | ok keyExprs =>
      cases hvalueExpr : compileExprWithInternals fields dynamicSource [] value with
      | error err => simp [hkeyExprs, hvalueExpr, bind, Except.bind] at hcompile
      | ok valueExpr =>
          cases slots with
          | nil => simp [hkeyExprs, hvalueExpr, bind, Except.bind] at hcompile
          | cons slot rest =>
              cases rest with
              | nil =>
                  simp [hkeyExprs, hvalueExpr, bind, Except.bind] at hcompile
                  cases hcompile
                  exact .exprStmt _ _ .nil
              | cons slot' rest =>
                  simp [hkeyExprs, hvalueExpr, bind, Except.bind] at hcompile
                  cases hcompile
                  convert legacyCompatibleExternalStmtList_block_value_lets_writes
                      (α := YulExpr × Nat) (β := Nat)
                      (letName := fun x => toString "__compat_key" ++ x.2.repr)
                      (letValue := fun x => x.1)
                      (f := fun slot =>
                        (List.range keyExprs.length).map
                          (fun idx => YulExpr.ident (toString "__compat_key" ++ idx.repr))
                        |>.foldl
                          (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
                          (YulExpr.lit slot))
                      (match findFieldWithResolvedSlot fields fieldName with
                        | some (f, _) => if f.isTransient then "tstore" else "sstore"
                        | none => "sstore")
                      valueExpr keyExprs.zipIdx (slot :: slot' :: rest) using 1 <;>
                    simp only [List.map, List.cons_append, List.append_assoc,
                      List.nil_append, Nat.toString_eq_repr] <;> rfl

/-- Singleton `setMapping` heads compile to ordinary legacy-compatible Yul. -/
theorem stmtList_setMappingSingle_compiledLegacyCompatible
    (fields : List Field)
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {slot : Nat}
    (_hkey : FunctionBody.ExprCompileCore key)
    (_hscopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (_hvalue : FunctionBody.ExprCompileCore value)
    (_hscopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (_hslot : findFieldSlot fields fieldName = some slot) :
    StmtListCompiledLegacyCompatible fields scope [Stmt.setMapping fieldName key value] :=
  .cons
    (fun compiledIR hcompile => by
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        bind, Except.bind] at hcompile
      split at hcompile <;> try contradiction
      rename_i keyExpr hkeyExpr
      split at hcompile <;> try contradiction
      rename_i valueExpr hvalueExpr
      exact compileMappingSlotWrite_legacyCompatible hcompile)
    .nil

/-- Singleton `setMappingChain` heads compile to ordinary legacy-compatible Yul. -/
theorem stmtList_setMappingChainSingle_compiledLegacyCompatible
    (fields : List Field)
    {scope : List String}
    {fieldName : String}
    {keys : List Expr}
    {value : Expr}
    {slot : Nat}
    (_hkeys : ∀ key ∈ keys, FunctionBody.ExprCompileCore key)
    (_hscopeKeys : ∀ key ∈ keys, FunctionBody.exprBoundNamesInScope key scope)
    (_hvalue : FunctionBody.ExprCompileCore value)
    (_hscopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (_hslot : findFieldSlot fields fieldName = some slot) :
    StmtListCompiledLegacyCompatible fields scope [Stmt.setMappingChain fieldName keys value] :=
  .cons
    (fun compiledIR hcompile => by
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hcompile
      exact compileSetMappingChain_legacyCompatible hcompile)
    .nil

/-- Singleton `setMapping2` heads compile to ordinary legacy-compatible Yul. -/
theorem stmtList_setMapping2Single_compiledLegacyCompatible
    (fields : List Field)
    {scope : List String}
    {fieldName : String}
    {key1 key2 value : Expr}
    {slot : Nat}
    (_hkey1 : FunctionBody.ExprCompileCore key1)
    (_hscopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (_hkey2 : FunctionBody.ExprCompileCore key2)
    (_hscopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (_hvalue : FunctionBody.ExprCompileCore value)
    (_hscopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (_hslot : findFieldSlot fields fieldName = some slot) :
    StmtListCompiledLegacyCompatible fields scope [Stmt.setMapping2 fieldName key1 key2 value] :=
  .cons
    (fun compiledIR hcompile => by
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hcompile
      exact compileSetMapping2_legacyCompatible hcompile)
    .nil

/-- Singleton `setMapping2Word` heads compile to ordinary legacy-compatible Yul. -/
theorem stmtList_setMapping2WordSingle_compiledLegacyCompatible
    (fields : List Field)
    {scope : List String}
    {fieldName : String}
    {key1 key2 value : Expr}
    {wordOffset slot : Nat}
    (_hkey1 : FunctionBody.ExprCompileCore key1)
    (_hscopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (_hkey2 : FunctionBody.ExprCompileCore key2)
    (_hscopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (_hvalue : FunctionBody.ExprCompileCore value)
    (_hscopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (_hslot : findFieldSlot fields fieldName = some slot) :
    StmtListCompiledLegacyCompatible fields scope
      [Stmt.setMapping2Word fieldName key1 key2 wordOffset value] :=
  .cons
    (fun compiledIR hcompile => by
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hcompile
      exact compileSetMapping2Word_legacyCompatible hcompile)
    .nil

/-- Singleton `setStructMember2` heads for unpacked members compile to ordinary
legacy-compatible Yul. -/
theorem stmtList_setStructMember2Single_compiledLegacyCompatible
    (fields : List Field)
    {scope : List String}
    {fieldName memberName : String}
    {key1 key2 value : Expr}
    {slot wordOffset : Nat}
    {members : List StructMember}
    (_hkey1 : FunctionBody.ExprCompileCore key1)
    (_hscopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (_hkey2 : FunctionBody.ExprCompileCore key2)
    (_hscopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (_hvalue : FunctionBody.ExprCompileCore value)
    (_hscopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (_hslot : findFieldSlot fields fieldName = some slot)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember :
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none }) :
    StmtListCompiledLegacyCompatible fields scope
      [Stmt.setStructMember2 fieldName key1 key2 memberName value] :=
  .cons
    (fun compiledIR hcompile => by
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hcompile
      exact compileSetStructMember2_legacyCompatible hmembers hmember hcompile)
    .nil

/-- Singleton `setMappingUint` heads compile to ordinary legacy-compatible Yul. -/
theorem stmtList_setMappingUintSingle_compiledLegacyCompatible
    (fields : List Field)
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {slot : Nat}
    (_hkey : FunctionBody.ExprCompileCore key)
    (_hscopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (_hvalue : FunctionBody.ExprCompileCore value)
    (_hscopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (_hslot : findFieldSlot fields fieldName = some slot) :
    StmtListCompiledLegacyCompatible fields scope [Stmt.setMappingUint fieldName key value] :=
  .cons
    (fun compiledIR hcompile => by
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        bind, Except.bind] at hcompile
      split at hcompile <;> try contradiction
      rename_i keyExpr hkeyExpr
      split at hcompile <;> try contradiction
      rename_i valueExpr hvalueExpr
      exact compileMappingSlotWrite_legacyCompatible hcompile)
    .nil

/-- Singleton `setMappingWord` heads compile to ordinary legacy-compatible Yul. -/
theorem stmtList_setMappingWordSingle_compiledLegacyCompatible
    (fields : List Field)
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {wordOffset slot : Nat}
    (_hkey : FunctionBody.ExprCompileCore key)
    (_hscopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (_hvalue : FunctionBody.ExprCompileCore value)
    (_hscopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (_hslot : findFieldSlot fields fieldName = some slot) :
    StmtListCompiledLegacyCompatible fields scope [Stmt.setMappingWord fieldName key wordOffset value] :=
  .cons
    (fun compiledIR hcompile => by
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        bind, Except.bind] at hcompile
      split at hcompile <;> try contradiction
      rename_i keyExpr hkeyExpr
      split at hcompile <;> try contradiction
      rename_i valueExpr hvalueExpr
      exact compileMappingSlotWrite_legacyCompatible hcompile)
    .nil

/-- Per-function legacy-compatibility bridge. A supported external function whose
scalar params are supported and whose compiled body satisfies the per-statement
legacy interface compiles to a function whose IR body stays inside the
legacy-compatible external Yul subset (`LegacyCompatibleExternalStmtList`).
Composes `genParamLoads_scalar_legacy` with the body composition lemma. -/
theorem compileFunctionSpec_body_legacyCompatible_of_interface
    (fields : List Field) (selector : Nat) (spec : FunctionSpec)
    {habi : spec.abiDecoding = .standard} (irFn : IRFunction)
    (hparams : ∀ param ∈ spec.params, SupportedExternalScalarParamType param.ty)
    (hbodyInterface :
      StmtListCompiledLegacyCompatible fields (spec.params.map (·.name)) spec.body)
    (hcompile : compileFunctionSpec fields [] [] [] selector spec = Except.ok irFn) :
    LegacyCompatibleExternalStmtList irFn.body := by
  obtain ⟨returns, bodyStmts, _hvalidate, _hreturns, hbodyCompile, hirFn⟩ :=
    compileFunctionSpec_ok_components (habi := habi) fields [] [] selector spec irFn hcompile
  subst hirFn
  simp only [compiledFunctionIR]
  exact legacyCompatibleExternalStmtList_append
    (genParamLoads_scalar_legacy spec.params hparams)
    (compileStmtList_legacyCompatible_of_interface hbodyInterface hbodyCompile)

/-- Function-level legacy-compatibility package for the generic compile-core
body fragment. This discharges #2080's per-statement legacy interface for
external functions whose source body is already in `StmtListCompileCore`. -/
theorem compileFunctionSpec_body_legacyCompatible_of_compileCore
    (fields : List Field) (selector : Nat) (spec : FunctionSpec)
    {habi : spec.abiDecoding = .standard} (irFn : IRFunction)
    (hparams : ∀ param ∈ spec.params, SupportedExternalScalarParamType param.ty)
    (hbodyCore :
      FunctionBody.StmtListCompileCore (spec.params.map (·.name)) spec.body)
    (hcompile : compileFunctionSpec fields [] [] [] selector spec = Except.ok irFn) :
    LegacyCompatibleExternalStmtList irFn.body :=
  compileFunctionSpec_body_legacyCompatible_of_interface (habi := habi)
    fields selector spec irFn hparams
    (stmtListCompileCore_compiledLegacyCompatible fields
      (compilerScope := spec.params.map (·.name)) hbodyCore)
    hcompile

/-- Function-level legacy-compatibility package for the terminal-core body
fragment, including terminal `ite` bodies. -/
theorem compileFunctionSpec_body_legacyCompatible_of_terminalCore
    (fields : List Field) (selector : Nat) (spec : FunctionSpec)
    {habi : spec.abiDecoding = .standard} (irFn : IRFunction)
    (hparams : ∀ param ∈ spec.params, SupportedExternalScalarParamType param.ty)
    (hbodyTerminal :
      FunctionBody.StmtListTerminalCore (spec.params.map (·.name)) spec.body)
    (hcompile : compileFunctionSpec fields [] [] [] selector spec = Except.ok irFn) :
    LegacyCompatibleExternalStmtList irFn.body :=
  compileFunctionSpec_body_legacyCompatible_of_interface (habi := habi)
    fields selector spec irFn hparams
    (stmtListTerminalCore_compiledLegacyCompatible fields
      (compilerScope := spec.params.map (·.name)) hbodyTerminal)
    hcompile

/-- Disjointness of the scalar validator guard
`if iszero(eq(name, calldataload(lit offset))) { revert(0, 0) }` from a runtime
contract's internal-function table. -/
private theorem scalarValidationGuard_calldataload_callsDisjoint
    (runtimeContract : IRContract) (name : String) (offset : Nat)
    (hload : yulExprCallsDisjointFromInternalTable runtimeContract
      (YulExpr.call "calldataload" [YulExpr.lit offset]))
    (heq : findInternalFunction? runtimeContract "eq" = none)
    (hrevert : findInternalFunction? runtimeContract "revert" = none)
    (hiszero : findInternalFunction? runtimeContract "iszero" = none) :
    YulStmtListCallsDisjointFromInternalTable runtimeContract
      [scalarValidationGuard name (YulExpr.call "calldataload" [YulExpr.lit offset])] := by
  refine .if_ _ _ _ ?_ (.exprStmt _ _ ?_ .nil) .nil
  · simp only [yulExprCallsDisjointFromInternalTable]
    refine ⟨hiszero, ?_⟩
    intro arg harg; simp only [List.mem_singleton] at harg
    subst harg
    simp only [yulExprCallsDisjointFromInternalTable]
    refine ⟨heq, ?_⟩
    intro arg harg; simp only [List.mem_cons, List.not_mem_nil, or_false] at harg
    rcases harg with h1 | h2
    · subst h1; simp only [yulExprCallsDisjointFromInternalTable]
    · subst h2; exact hload
  · simp only [yulExprCallsDisjointFromInternalTable]
    refine ⟨hrevert, ?_⟩
    intro arg harg; simp only [List.mem_cons, List.not_mem_nil, or_false] at harg
    rcases harg with h1 | h2 <;> (subst_vars; simp only [yulExprCallsDisjointFromInternalTable])

private theorem calldataload_lit_callsDisjoint
    (runtimeContract : IRContract) (offset : Nat)
    (hcd : findInternalFunction? runtimeContract "calldataload" = none) :
    yulExprCallsDisjointFromInternalTable runtimeContract
      (YulExpr.call "calldataload" [YulExpr.lit offset]) := by
  simp only [yulExprCallsDisjointFromInternalTable]
  refine ⟨hcd, ?_⟩
  intro arg harg; simp only [List.mem_singleton] at harg
  subst harg
  simp only [yulExprCallsDisjointFromInternalTable]

/-- Disjointness of a scalar cleanup load (`genScalarCleanLoad` with the
`calldataload` word loader) from a runtime contract's internal-function table:
its builtins (`calldataload`, `and`, `signextend`, `iszero`) are assumed absent
from the table. -/
private theorem genScalarCleanLoad_calldataload_callsDisjoint
    (runtimeContract : IRContract) (name : String) (ty : ParamType) (offset : Nat)
    (hsupported : SupportedExternalScalarParamType ty)
    (hcd : findInternalFunction? runtimeContract "calldataload" = none)
    (hand : findInternalFunction? runtimeContract "and" = none)
    (hsignextend : findInternalFunction? runtimeContract "signextend" = none)
    (hiszero : findInternalFunction? runtimeContract "iszero" = none) :
    YulStmtListCallsDisjointFromInternalTable runtimeContract
      (genScalarCleanLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty offset) := by
  have hload := calldataload_lit_callsDisjoint runtimeContract offset hcd
  cases ty <;> simp only [SupportedExternalScalarParamType] at hsupported ⊢
  all_goals
    first
    | exact .let_ _ _ [] hload .nil
    | (refine .let_ _ _ [] ?_ .nil
       simp only [yulExprCallsDisjointFromInternalTable]
       refine ⟨hand, ?_⟩
       intro arg harg; simp only [List.mem_cons, List.not_mem_nil, or_false] at harg
       rcases harg with h1 | h2
       · subst h1; exact hload
       · subst h2; simp only [yulExprCallsDisjointFromInternalTable])
    | (refine .let_ _ _ [] ?_ .nil
       simp only [yulExprCallsDisjointFromInternalTable]
       refine ⟨hsignextend, ?_⟩
       intro arg harg; simp only [List.mem_cons, List.not_mem_nil, or_false] at harg
       rcases harg with h1 | h2
       · subst h1; simp only [yulExprCallsDisjointFromInternalTable]
       · subst h2; exact hload)
    | (refine .let_ _ _ [] ?_ .nil
       simp only [yulExprCallsDisjointFromInternalTable]
       refine ⟨hiszero, ?_⟩
       intro arg harg; simp only [List.mem_singleton] at harg
       subst harg
       simp only [yulExprCallsDisjointFromInternalTable]
       refine ⟨hiszero, ?_⟩
       intro arg2 harg2; simp only [List.mem_singleton] at harg2
       subst harg2
       exact hload)

/-- Disjointness of a single scalar param-load (with the `calldataload` word
loader used by `genParamLoads`) from a runtime contract's internal-function
table: the cleanup load, then for narrow types the validator guard (`eq`,
`iszero`, `revert`). -/
private theorem genScalarLoad_calldataload_callsDisjoint
    (runtimeContract : IRContract) (name : String) (ty : ParamType) (offset : Nat)
    (hsupported : SupportedExternalScalarParamType ty)
    (hcd : findInternalFunction? runtimeContract "calldataload" = none)
    (hand : findInternalFunction? runtimeContract "and" = none)
    (hsignextend : findInternalFunction? runtimeContract "signextend" = none)
    (hiszero : findInternalFunction? runtimeContract "iszero" = none)
    (heq : findInternalFunction? runtimeContract "eq" = none)
    (hrevert : findInternalFunction? runtimeContract "revert" = none) :
    YulStmtListCallsDisjointFromInternalTable runtimeContract
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty offset) := by
  have hclean := genScalarCleanLoad_calldataload_callsDisjoint runtimeContract name ty offset
    hsupported hcd hand hsignextend hiszero
  have hguard := scalarValidationGuard_calldataload_callsDisjoint runtimeContract name offset
    (calldataload_lit_callsDisjoint runtimeContract offset hcd) heq hrevert hiszero
  cases ty <;> simp only [SupportedExternalScalarParamType] at hsupported
  all_goals first
    | exact hclean
    | exact yulStmtListCallsDisjoint_append hclean hguard

/-- Disjointness of the whole param-load body (the recursive `genSingleParamLoad`
sequence used by `genParamLoads`) from a runtime contract's internal-function
table, given the scalar-load and validator builtins are absent. Recurses over the
supported scalar params, appending per-param disjointness. -/
private theorem genParamLoadBodyFrom_calldataload_callsDisjoint
    (runtimeContract : IRContract)
    (hcd : findInternalFunction? runtimeContract "calldataload" = none)
    (hand : findInternalFunction? runtimeContract "and" = none)
    (hsignextend : findInternalFunction? runtimeContract "signextend" = none)
    (hiszero : findInternalFunction? runtimeContract "iszero" = none)
    (heq : findInternalFunction? runtimeContract "eq" = none)
    (hrevert : findInternalFunction? runtimeContract "revert" = none)
    (sizeExpr : YulExpr) (headSize baseOffset : Nat) :
    ∀ (params : List Param) (headOffset : Nat),
      (∀ param ∈ params, SupportedExternalScalarParamType param.ty) →
        YulStmtListCallsDisjointFromInternalTable runtimeContract
          (genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
            sizeExpr headSize baseOffset params headOffset)
  | [], _, _ => .nil
  | param :: rest, headOffset, hsupported => by
      have htail := genParamLoadBodyFrom_calldataload_callsDisjoint runtimeContract
        hcd hand hsignextend hiszero heq hrevert sizeExpr headSize baseOffset rest
        (headOffset + paramHeadSize param.ty)
        (by intro p hp; exact hsupported p (by simp [hp]))
      have hhead_sup : SupportedExternalScalarParamType param.ty := hsupported param (by simp)
      have hhead := genScalarLoad_calldataload_callsDisjoint runtimeContract
        param.name param.ty headOffset hhead_sup hcd hand hsignextend hiszero heq hrevert
      cases hty : param.ty <;>
        simp only [SupportedExternalScalarParamType, hty] at hhead_sup <;>
        simpa only [genParamLoadBodyFrom, genSingleParamLoad, hty]
          using yulStmtListCallsDisjoint_append hhead htail

/-- Disjointness of the full `genParamLoads` output (min-input-size guard plus
the param-load body) from a runtime contract's internal-function table, given
that none of the eight EVM/Yul builtins it emits (`calldataload`, `calldatasize`,
`lt`, `revert`, `and`, `signextend`, `iszero`, `eq`) collide with an internal helper. -/
private theorem genParamLoads_callsDisjoint_of_builtins
    (runtimeContract : IRContract) (params : List Param)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hcd : findInternalFunction? runtimeContract "calldataload" = none)
    (hcdsize : findInternalFunction? runtimeContract "calldatasize" = none)
    (hlt : findInternalFunction? runtimeContract "lt" = none)
    (hrevert : findInternalFunction? runtimeContract "revert" = none)
    (hand : findInternalFunction? runtimeContract "and" = none)
    (hsignextend : findInternalFunction? runtimeContract "signextend" = none)
    (hiszero : findInternalFunction? runtimeContract "iszero" = none)
    (heq : findInternalFunction? runtimeContract "eq" = none) :
    YulStmtListCallsDisjointFromInternalTable runtimeContract (genParamLoads params) := by
  have hbody := genParamLoadBodyFrom_calldataload_callsDisjoint runtimeContract
    hcd hand hsignextend hiszero heq hrevert (YulExpr.call "calldatasize" [])
    ((params.map (fun p => paramHeadSize p.ty)).foldl (· + ·) 0) 4 params 4 hsupported
  simp only [genParamLoads, genParamLoadsFrom]
  refine .if_ _ _ _ ?_ ?_ hbody
  · simp only [yulExprCallsDisjointFromInternalTable]
    refine ⟨hlt, ?_⟩
    intro arg harg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at harg
    rcases harg with h1 | h2
    · subst h1
      simp only [yulExprCallsDisjointFromInternalTable]
      exact ⟨hcdsize, by intro a ha; simp at ha⟩
    · subst h2; simp only [yulExprCallsDisjointFromInternalTable]
  · refine .exprStmt _ _ ?_ .nil
    simp only [yulExprCallsDisjointFromInternalTable]
    refine ⟨hrevert, ?_⟩
    intro arg harg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at harg
    rcases harg with h1 | h2
    · subst h1; simp only [yulExprCallsDisjointFromInternalTable]
    · subst h2; simp only [yulExprCallsDisjointFromInternalTable]

/-- Package `genParamLoads` disjointness directly from the runtime contract's
reserved-name invariant. Every helper name is reserved (`internal_`-, `__verity_`-,
`checked_`-, or `panic_error_`-prefixed), while the eight builtins emitted by the
param-load prologue (`calldataload`, `calldatasize`, `lt`, `revert`, `and`,
`signextend`, `iszero`, `eq`) are provably *not* reserved, so none of them can resolve to a helper.
This is the true seam that replaces the false "every helper is `internal_`-prefixed"
premise: real compiler helpers are not `internal_`-prefixed, but they *are*
reserved, so the invariant is dischargeable from actual compilation output. -/
theorem genParamLoads_callsDisjoint_of_reserved
    (runtimeContract : IRContract) (params : List Param)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hinv : InternalTableNamesReserved runtimeContract) :
    YulStmtListCallsDisjointFromInternalTable runtimeContract (genParamLoads params) :=
  genParamLoads_callsDisjoint_of_builtins runtimeContract params hsupported
    (findInternalFunction?_eq_none_of_not_reserved runtimeContract "calldataload" hinv (by decide))
    (findInternalFunction?_eq_none_of_not_reserved runtimeContract "calldatasize" hinv (by decide))
    (findInternalFunction?_eq_none_of_not_reserved runtimeContract "lt" hinv (by decide))
    (findInternalFunction?_eq_none_of_not_reserved runtimeContract "revert" hinv (by decide))
    (findInternalFunction?_eq_none_of_not_reserved runtimeContract "and" hinv (by decide))
    (findInternalFunction?_eq_none_of_not_reserved runtimeContract "signextend" hinv (by decide))
    (findInternalFunction?_eq_none_of_not_reserved runtimeContract "iszero" hinv (by decide))
    (findInternalFunction?_eq_none_of_not_reserved runtimeContract "eq" hinv (by decide))

/-- Package `genParamLoads` disjointness from the `internal_`-prefix naming
invariant, routed through the reserved-name seam
(`genParamLoads_callsDisjoint_of_reserved` +
`InternalTableNamesReserved_of_internalPrefixed`). Retained as the compiled-only
entry point; the populated-table path uses the reserved variant directly. -/
theorem genParamLoads_callsDisjoint_of_internalNamesPrefixed
    (runtimeContract : IRContract) (params : List Param)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hinv : InternalTableNamesInternalPrefixed runtimeContract) :
    YulStmtListCallsDisjointFromInternalTable runtimeContract (genParamLoads params) :=
  genParamLoads_callsDisjoint_of_reserved runtimeContract params hsupported
    (InternalTableNamesReserved_of_internalPrefixed runtimeContract hinv)

/-- The Yul name emitted for a compiled internal helper begins with
`internalFunctionPrefix` (`"internal_"`). This is the structural fact that lets
the whole-contract dispatch proof discharge `InternalTableNamesInternalPrefixed`
directly from the compilation pipeline rather than assuming an empty internal
table. -/
theorem internalFunctionYulName_take_prefix (name : String) :
    (internalFunctionYulName name).toList.take internalFunctionPrefix.toList.length =
      internalFunctionPrefix.toList := by
  have hdata : (internalFunctionYulName name).toList =
      internalFunctionPrefix.toList ++ name.toList := by
    have ts : ∀ s : String, toString s = s := fun _ => rfl
    simpa only [internalFunctionYulName, ts] using
      (String.toList_append :
        (internalFunctionPrefix ++ name).toList =
          internalFunctionPrefix.toList ++ name.toList)
  rw [hdata]
  simp

/-- Every successful `compileInternalFunction` output is a `funcDef` whose Yul
name is exactly `internalFunctionYulName spec.name`. Mirrors the case analysis of
`compileInternalFunction_ok_components`, extracting only the emitted name. -/
theorem compileInternalFunction_isFuncDef_internalNamed
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (adtTypes : List AdtTypeDef) (spec : FunctionSpec)
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (internalFunctions : List FunctionSpec) (stmt : YulStmt)
    (hcompile : compileInternalFunction fields events errors adtTypes spec targetFork
        internalFunctions = Except.ok stmt) :
    ∃ params rets body,
      stmt = YulStmt.funcDef (internalFunctionYulName spec.name) params rets body := by
  unfold compileInternalFunction at hcompile
  cases hvalidate : validateFunctionSpec spec
  · rw [hvalidate] at hcompile
    cases hcompile
  case ok _ =>
    cases hreturns : functionReturns spec
    · rw [hvalidate, hreturns] at hcompile
      cases hcompile
    case ok returns =>
      rw [hvalidate, hreturns] at hcompile
      simp only [bind, Except.bind] at hcompile
      cases hbody :
          compileStmtListWithFork fields events errors .calldata
            (freshInternalRetNames returns
              (internalFunctionYulParamNames spec.params ++ collectStmtListBindNames spec.body))
            true
            (internalFunctionYulParamNames spec.params ++
              freshInternalRetNames returns
                (internalFunctionYulParamNames spec.params ++ collectStmtListBindNames spec.body))
            adtTypes targetFork spec.body internalFunctions
      · rw [hbody] at hcompile
        cases hcompile
      case ok bodyStmts =>
        rw [hbody] at hcompile
        simp only [pure, Except.pure, Except.ok.injEq] at hcompile
        exact ⟨_, _, _, hcompile.symm⟩

/-- If every statement in a runtime contract's internal table is the output of
`compileInternalFunction`, then the contract satisfies
`InternalTableNamesInternalPrefixed`. This packages the compiled-internal naming
invariant for consumption by the whole-contract dispatch seam. -/
theorem InternalTableNamesInternalPrefixed_of_all_compiledInternal
    (runtimeContract : IRContract)
    (hcompiled : ∀ stmt ∈ runtimeContract.internalFunctions,
        ∃ (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
          (adtTypes : List AdtTypeDef) (spec : FunctionSpec)
          (targetFork : Verity.Core.Intrinsics.HardFork)
          (internalFunctions : List FunctionSpec),
          compileInternalFunction fields events errors adtTypes spec targetFork internalFunctions
            = Except.ok stmt) :
    InternalTableNamesInternalPrefixed runtimeContract := by
  intro d hd
  rw [List.mem_filterMap] at hd
  obtain ⟨stmt, hstmt, hdecode⟩ := hd
  obtain ⟨fields, events, errors, adtTypes, spec, tf, ifs, hc⟩ := hcompiled stmt hstmt
  obtain ⟨params, rets, body, hstmteq⟩ :=
    compileInternalFunction_isFuncDef_internalNamed fields events errors adtTypes spec tf ifs stmt hc
  subst hstmteq
  simp only [irInternalFunctionDefOfStmt?_funcDef, Option.some.injEq] at hdecode
  subst hdecode
  exact internalFunctionYulName_take_prefix spec.name

private theorem compiledStmt_scalar_events_callsDisjoint
    (runtimeContract : IRContract) (hinternal : runtimeContract.internalFunctions = [])
    {fields : List Field} {spec : CompilationModel} {scope : List String}
    {stmt : Stmt} {compiledIR : List YulStmt}
    (hstmtSurface :
      stmtTouchesUnsupportedContractSurfaceWithEvents spec.events stmt = false)
    (hhead :
      stmtTouchesEventSurface stmt = true ∨
        stmtTouchesUnsupportedContractSurface stmt = false)
    (hplainDisjoint :
      stmtTouchesUnsupportedHelperSurface stmt = false →
        ∀ compiledIR,
          CompilationModel.compileStmt fields [] [] .calldata [] false scope [] stmt =
            Except.ok compiledIR →
          YulStmtListCallsDisjointFromInternalTable runtimeContract compiledIR)
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope [] stmt =
        Except.ok compiledIR) :
    YulStmtListCallsDisjointFromInternalTable runtimeContract compiledIR := by
  rcases hhead with hevent | hplain
  · cases stmt with
    | emit eventName args =>
        rcases eventCompileStmt_emit_scalar_shape
            (eventEmissionProofSupported_eq_true_of_emit_contractSurfaceWithEventsClosed
              hstmtSurface)
            (exprListTouchesUnsupportedContractSurface_eq_false_of_emit_contractSurfaceWithEventsClosed
              hstmtSurface)
            hcompile with ⟨eventDef, argExprs, _, _, hshape⟩
        rw [hshape]
        exact YulStmtListCallsDisjointFromInternalTable_of_internalFunctions_nil
          runtimeContract hinternal _
          (eventCompiledScalarEmit_legacy eventDef args argExprs)
    | _ => simp [stmtTouchesEventSurface] at hevent
  · have hhelper := stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hplain
    have hcompilePlain :
        CompilationModel.compileStmt fields [] [] .calldata [] false scope [] stmt =
          Except.ok compiledIR := by
      rw [← compileStmt_eventsErrorsAgnostic_of_contractSurfaceClosed
        (events := spec.events) (errors := spec.errors) hplain]
      exact hcompile
    exact hplainDisjoint hhelper compiledIR hcompilePlain

private theorem compileStmtList_scalar_events_callsDisjoint
    (runtimeContract : IRContract) (hinternal : runtimeContract.internalFunctions = [])
    {fields : List Field} {spec : CompilationModel} :
    ∀ {scope : List String} {stmts : List Stmt} {compiledIR : List YulStmt},
      stmtListTouchesUnsupportedContractSurfaceWithEvents spec.events stmts = false →
      (∀ s ∈ stmts,
        stmtTouchesEventSurface s = true ∨
          stmtTouchesUnsupportedContractSurface s = false) →
      StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts →
      CompilationModel.compileStmtList fields spec.events spec.errors .calldata [] false
        scope [] stmts = Except.ok compiledIR →
      YulStmtListCallsDisjointFromInternalTable runtimeContract compiledIR
  | _, [], _, _, _, _, hcompile => by
      try unfold CompilationModel.compileStmtList at hcompile
      unfold CompilationModel.compileStmtListWithFork at hcompile
      cases hcompile
      exact .nil
  | scope, stmt :: rest, compiledIR, hsurface, hheads, hdisjoint, hcompile => by
      obtain ⟨hstmtSurface, hrestSurface⟩ := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedContractSurfaceWithEvents] using hsurface
      rcases FunctionBody.compileStmtList_cons_ok_inv hcompile with
        ⟨headIR, tailIR, hheadCompile, htailCompile, hbody⟩
      cases hdisjoint with
      | cons hheadDisjoint htailDisjoint =>
          rw [hbody]
          exact yulStmtListCallsDisjoint_append
            (compiledStmt_scalar_events_callsDisjoint runtimeContract hinternal
              hstmtSurface (hheads stmt List.mem_cons_self) hheadDisjoint hheadCompile)
            (compileStmtList_scalar_events_callsDisjoint runtimeContract hinternal
              hrestSurface
              (fun s hmem => hheads s (List.mem_cons_of_mem stmt hmem))
              htailDisjoint htailCompile)

private theorem supported_function_correct_with_scalar_events_state_runtime
    (model : CompilationModel) (fn : FunctionSpec) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (initialState state : IRState) (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hstate : state = ParamLoading.applyBindingsToIRState (prebindRawArgs initialState fn.params) bindings)
    (hinitialState : initialState = FunctionBody.initialIRStateForTx model tx initialWorld) :
    FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector, errors := model.errors }
      state := by
  subst hstate
  subst hinitialState
  have hpreboundRuntime :
      FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector, errors := model.errors }
        (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params) := by
    exact runtimeStateMatchesIR_prebindRawArgs
      (state := FunctionBody.initialIRStateForTx model tx initialWorld)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector, errors := model.errors })
      (fields := SourceSemantics.effectiveFields model) (params := fn.params)
      (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized hcalldataSizeFits)
  exact runtimeStateMatchesIR_applyBindingsToIRState
    (state := prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
    (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector, errors := model.errors })
    (fields := SourceSemantics.effectiveFields model) (bindings := bindings) hpreboundRuntime

private theorem supported_function_correct_with_scalar_events_body_extraFuelLower
    (model : CompilationModel) (fn : FunctionSpec)
    {habi : fn.abiDecoding = .standard} (selector : Nat) (returns : List ParamType)
    (bodyStmts : List YulStmt) (irFn : IRFunction)
    (hvalidate : validateFunctionSpec fn = Except.ok ()) (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (extraFuel : Nat) (hextraFuel : extraFuel = sizeOf irFn.body - irFn.body.length) :
    sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
  have hcompiled := compileFunctionSpec_ok_of_components (habi := habi) model.fields model.events model.errors selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled
  subst hirFn
  subst hextraFuel
  simpa [compiledFunctionIR] using yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts

private theorem supported_function_correct_with_scalar_events_body_fuel
    (selector : Nat) (fn : FunctionSpec) (returns : List ParamType) (bodyStmts : List YulStmt)
    (irFn : IRFunction) (extraFuel : Nat)
    (hcompileOk : irFn = compiledFunctionIR selector fn returns bodyStmts)
    (hextraFuel : extraFuel = sizeOf irFn.body - irFn.body.length) :
    (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
      sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
  subst hcompileOk
  subst hextraFuel
  have hlenle := Nat.le_of_add_le_add_right
    (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
  simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle

private theorem supported_function_correct_with_scalar_events_body_correct
    (runtimeContract : IRContract) (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors)
    (fn : FunctionSpec) (bodyStmts : List YulStmt) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (state : IRState) (bindings : List (String × Nat)) (extraFuel : Nat)
    (hfn : fn ∈ selectorDispatchedFunctions model) (hbodyExtraFuelLower : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < hSupported.helperFuel)
    (hhelperFree : StmtListHelperFreeNonEventStepInterface (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hstmtDisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hinternal : runtimeContract.internalFunctions = [])
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hscope : FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector, errors := model.errors } state)
    (hstateBindings : FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal runtimeContract model fn bodyStmts hSupported.helperFuel tx initialWorld state bindings extraFuel := by
  have hsupportedFn := hSupported.supportedFunctionOfSelectorDispatched hfn
  exact supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir_callsDisjoint_with_scalar_events
    runtimeContract model fn bodyStmts hSupported.helperFuel tx initialWorld state bindings extraFuel
    hbodyExtraFuelLower hfuelPos (by simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
    hSupported.noErrors hSupported.noAdtTypes hsupportedFn.body.contractSurfaceWithEvents
    hsupportedFn.body.topLevelEventHeads hhelperFree hsupportedFn.body.eventScratchFreshInitial
    hsupportedFn.body.eventScratchFreshStmts hsupportedFn.body.emitArgsInScope hinternal
    (hSupported.noAdtTypes ▸ hbodyCompile) hscope hbounded hstateRuntime hstateBindings hstmtDisjoint

theorem supported_function_correct_with_scalar_events
    (runtimeContract : IRContract) (model : CompilationModel) (selectors : List Nat) (hSupported : SupportedSpecWithScalarEvents model selectors)
    (fn : FunctionSpec) (selector : Nat) (returns : List ParamType) (bodyStmts : List YulStmt) (irFn : IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat)) (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ()) (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hfuelPos : 0 < hSupported.helperFuel)
    (hhelperFree : StmtListHelperFreeNonEventStepInterface (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hstmtDisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hbodyDisjoint : YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts) (hinternal : runtimeContract.internalFunctions = [])
    (hhelperIR : execIRFunctionWithInternals runtimeContract 0 irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld) = execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) :
    FunctionBody.sourceResultMatchesIRResult (supportedSourceFunctionSemanticsWithScalarEvents model selectors hSupported fn tx initialWorld) (execIRFunctionWithInternals runtimeContract 0 irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have habi : fn.abiDecoding = .standard :=
    (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  let state := ParamLoading.applyBindingsToIRState (prebindRawArgs initialState fn.params) bindings
  let extraFuel := sizeOf irFn.body - irFn.body.length
  have hcompiled := compileFunctionSpec_ok_of_components (habi := habi) model.fields model.events model.errors selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled; injection hcompiled
  have hbodyExtraFuelLower : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel :=
    supported_function_correct_with_scalar_events_body_extraFuelLower (habi := habi)
      model fn selector returns bodyStmts irFn hvalidate hreturns hbodyCompile hcompile extraFuel rfl
  have hinit : FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
    simpa [initialState] using FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
  have hstateRuntime : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model) { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector, errors := model.errors } state :=
    supported_function_correct_with_scalar_events_state_runtime
      model fn tx initialWorld bindings initialState state htxNormalized hcalldataSizeFits rfl rfl
  have hstateBindings : FunctionBody.bindingsExactlyMatchIRVars bindings state :=
    supported_function_param_state_exact initialState fn.params bindings hinit
      (hSupported.selectorFunctionParamNamesNodup hfn) hbind
  have hscope : FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
    intro name hmem; exact lookupBinding?_some_of_mem bindings name (by rw [ParamLoading.bindSupportedParams_names hbind]; simpa using hmem)
  have hbounded : FunctionBody.bindingsBounded bindings := FunctionBody.bindingsBounded_of_bindSupportedParams hbind
  have hbodyCorrect := supported_function_correct_with_scalar_events_body_correct
    runtimeContract model selectors hSupported fn bodyStmts tx initialWorld state bindings extraFuel hfn
    hbodyExtraFuelLower hfuelPos hhelperFree hstmtDisjoint hinternal hbodyCompile
    hscope hbounded hstateRuntime hstateBindings
  have hbodyFuel : (genParamLoads fn.params ++ bodyStmts).length + extraFuel = sizeOf (compiledFunctionIR selector fn returns bodyStmts).body :=
    supported_function_correct_with_scalar_events_body_fuel selector fn returns bodyStmts irFn extraFuel hirFn rfl
  exact supported_function_correct_with_scalar_events_body_goal_and_helper_ir
    model selectors hSupported runtimeContract fn selector returns bodyStmts irFn tx initialWorld
    bindings hfn hvalidate hreturns hbodyCompile hcompile hbind htxNormalized extraFuel hbodyFuel
    hbodyCorrect hbodyDisjoint hhelperIR hcalldataSizeFits

theorem supported_function_correct_with_scalar_events_of_bodyCallsDisjoint
    (runtimeContract : IRContract) (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors)
    (fn : FunctionSpec) (selector : Nat) (returns : List ParamType)
    (bodyStmts : List YulStmt) (irFn : IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hfuelPos : 0 < hSupported.helperFuel)
    (hhelperFree : StmtListHelperFreeNonEventStepInterface
      (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hstmtDisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract
      (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hbodyDisjoint : YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts)
    (hfnBodyDisjoint : YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
    (hinternal : runtimeContract.internalFunctions = []) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemanticsWithScalarEvents model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact supported_function_correct_with_scalar_events
    runtimeContract model selectors hSupported fn selector returns bodyStmts irFn tx
    initialWorld bindings hfn hvalidate hreturns hbodyCompile hcompile hbind htxNormalized
    hcalldataSizeFits hfuelPos hhelperFree hstmtDisjoint hbodyDisjoint hinternal
    (execIRFunctionWithInternals_eq_execIRFunction_of_bodyCallsDisjoint
      runtimeContract irFn tx.args
      (FunctionBody.initialIRStateForTx model tx initialWorld) hfnBodyDisjoint)

private theorem compiledFunctionIR_scalar_events_callsDisjoint
    (runtimeContract : IRContract) (hinternal : runtimeContract.internalFunctions = [])
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors)
    (fn : FunctionSpec) (selector : Nat) (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hstmtDisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract
      (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body) :
    YulStmtListCallsDisjointFromInternalTable runtimeContract
      (compiledFunctionIR selector fn returns bodyStmts).body := by
  have hsupportedFn := hSupported.supportedFunctionOfSelectorDispatched hfn
  have hbodyDisjoint := compileStmtList_scalar_events_callsDisjoint
    runtimeContract hinternal hsupportedFn.body.contractSurfaceWithEvents
    hsupportedFn.body.topLevelEventHeads hstmtDisjoint
    (by simpa [SourceSemantics.effectiveFields, hSupported.normalizedFields] using hbodyCompile)
  have hparamLegacy := genParamLoads_scalar_legacy fn.params
    (hSupported.selectorFunctionParamsSupported hfn)
  have hparamDisjoint :=
    YulStmtListCallsDisjointFromInternalTable_of_internalFunctions_nil
      runtimeContract hinternal (genParamLoads fn.params) hparamLegacy
  simpa [compiledFunctionIR] using
    yulStmtListCallsDisjoint_append hparamDisjoint hbodyDisjoint

theorem compileFunctionSpec_correct_with_scalar_events
    (runtimeContract : IRContract) (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors)
    (fn : FunctionSpec) (sel : Nat) (irFn : IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (htxNormalized : TxContextNormalized tx)
    (bindings : List (String × Nat)) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn : compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hfuelPos : 0 < hSupported.helperFuel)
    (hhelperFree : StmtListHelperFreeNonEventStepInterface
      (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hstmtDisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract
      (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hinternal : runtimeContract.internalFunctions = []) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemanticsWithScalarEvents model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have habi : fn.abiDecoding = .standard :=
    (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi
  rcases compileFunctionSpec_ok_components (habi := habi) model.fields model.events model.errors sel fn irFn
      hcompileFn with ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
  subst hirFn
  have hbodyDisjoint := compileStmtList_scalar_events_callsDisjoint
    runtimeContract hinternal
    (hSupported.supportedFunctionOfSelectorDispatched hfn).body.contractSurfaceWithEvents
    (hSupported.supportedFunctionOfSelectorDispatched hfn).body.topLevelEventHeads
    hstmtDisjoint
    (by simpa [SourceSemantics.effectiveFields, hSupported.normalizedFields] using hbodyCompile)
  have hfnDisjoint := compiledFunctionIR_scalar_events_callsDisjoint
    runtimeContract hinternal model selectors hSupported fn sel returns bodyStmts hfn
    hbodyCompile hstmtDisjoint
  have hcorrect := supported_function_correct_with_scalar_events_of_bodyCallsDisjoint
    runtimeContract model selectors hSupported fn sel returns bodyStmts
    (compiledFunctionIR sel fn returns bodyStmts) tx initialWorld bindings hfn
    hvalidate hreturns hbodyCompile (by simpa using hcompileFn) hbind htxNormalized
    hcalldataSizeFits hfuelPos hhelperFree hstmtDisjoint hbodyDisjoint hfnDisjoint hinternal
  simpa [execIRFunctionWithInternals_eq_execIRFunction_of_bodyCallsDisjoint
    runtimeContract (compiledFunctionIR sel fn returns bodyStmts) tx.args
    (FunctionBody.initialIRStateForTx model tx initialWorld) hfnDisjoint] using hcorrect

/-- Constructor-mode compilation agreement for a single surface-closed expression. -/
private abbrev ConstructorModeEq (fields : List Field) (expr : Expr) : Prop :=
  exprTouchesUnsupportedCoreSurface expr = false →
    exprTouchesUnsupportedCallSurface expr = false →
    exprTouchesUnsupportedConstructorRawCalldataSurface expr = false →
    compileExprWithInternals fields .memory [] expr =
      compileExprWithInternals fields .calldata [] expr

/-- The `externalCall` arm: only the binary builtin `exp` call is surface-closed. -/
private theorem constructorModeEq_externalCall {fields : List Field}
    {name : String} {args : List Expr}
    (ih : ∀ e : Expr, sizeOf e < sizeOf (Expr.externalCall name args) →
      ConstructorModeEq fields e) :
    ConstructorModeEq fields (.externalCall name args) := by
  intro hcore hcall hraw
  match args, ih, hcore, hcall, hraw with
  | [base, exponent], ih, hcore, hcall, hraw =>
      by_cases hname : name = builtinExpName
      · subst hname
        simp only [exprTouchesUnsupportedCoreSurface, beq_self_eq_true, if_true,
          Bool.or_eq_false_iff] at hcore
        simp only [exprTouchesUnsupportedCallSurface, beq_self_eq_true, if_true,
          Bool.or_eq_false_iff] at hcall
        simp only [exprTouchesUnsupportedConstructorRawCalldataSurface,
          exprListTouchesUnsupportedConstructorRawCalldataSurface, Bool.or_false,
          Bool.or_eq_false_iff] at hraw
        simp [compileExprWithInternals, compileExprListWithInternals,
          ih base (by simp +arith) hcore.1 hcall.1 hraw.1,
          ih exponent (by simp +arith) hcore.2 hcall.2 hraw.2]
      · simp [exprTouchesUnsupportedCoreSurface, hname] at hcore
  | [], _, hcore, _, _ => simp [exprTouchesUnsupportedCoreSurface] at hcore
  | [_], _, hcore, _, _ => simp [exprTouchesUnsupportedCoreSurface] at hcore
  | _ :: _ :: _ :: _, _, hcore, _, _ => simp [exprTouchesUnsupportedCoreSurface] at hcore

/-- One constructor step of `compileExpr_constructor_mode_eq`, given the agreement
for every strictly smaller expression. Each arm is either excluded by one of the
three surfaces, independent of the data source, or a congruence over its operands. -/
private theorem constructorModeEq_of_lt {fields : List Field} {expr : Expr}
    (ih : ∀ e : Expr, sizeOf e < sizeOf expr → ConstructorModeEq fields e) :
    ConstructorModeEq fields expr := by
  cases expr
  case externalCall => exact constructorModeEq_externalCall ih
  all_goals intro hcore hcall hraw
  all_goals first
    | (simp [exprTouchesUnsupportedCoreSurface] at hcore; done)
    | (simp [exprTouchesUnsupportedCallSurface] at hcall; done)
    | (simp [exprTouchesUnsupportedConstructorRawCalldataSurface] at hraw; done)
    | (simp [compileExprWithInternals]; done)
    | (simp only [exprTouchesUnsupportedCoreSurface, exprTouchesUnsupportedCallSurface,
          exprTouchesUnsupportedConstructorRawCalldataSurface, Bool.or_eq_false_iff,
          Bool.or_assoc] at hcore hcall hraw
       first
        | (rename_i a; simp [compileExprWithInternals,
            ih a (by simp +arith) hcore hcall hraw])
        | (rename_i a b; simp [compileExprWithInternals,
            ih a (by simp +arith) hcore.1 hcall.1 hraw.1,
            ih b (by simp +arith) hcore.2 hcall.2 hraw.2])
        | (rename_i a b c; simp [compileExprWithInternals,
            ih a (by simp +arith) hcore.1 hcall.1 hraw.1,
            ih b (by simp +arith) hcore.2.1 hcall.2.1 hraw.2.1,
            ih c (by simp +arith) hcore.2.2 hcall.2.2 hraw.2.2]))

/-- On the constructor body surface, expression compilation does not depend on
the dynamic-data source. The only expression forms whose generated Yul differs
between memory and calldata are excluded by the core/raw-calldata surfaces. -/
private theorem compileExpr_constructor_mode_eq
    {fields : List Field} :
    ∀ {expr : Expr},
      exprTouchesUnsupportedCoreSurface expr = false →
      exprTouchesUnsupportedCallSurface expr = false →
      exprTouchesUnsupportedConstructorRawCalldataSurface expr = false →
      compileExprWithInternals fields .memory [] expr =
        compileExprWithInternals fields .calldata [] expr
  | expr, hcore, hcall, hraw =>
      constructorModeEq_of_lt
        (fun e _ => compileExpr_constructor_mode_eq (expr := e)) hcore hcall hraw
termination_by expr => sizeOf expr

private theorem compileExprList_constructor_mode_eq
    {fields : List Field} :
    ∀ {exprs : List Expr},
      exprs.all (fun expr => exprTouchesUnsupportedCoreSurface expr == false) = true →
      exprs.all (fun expr => exprTouchesUnsupportedCallSurface expr == false) = true →
      exprListTouchesUnsupportedConstructorRawCalldataSurface exprs = false →
      compileExprListWithInternals fields .memory [] exprs =
        compileExprListWithInternals fields .calldata [] exprs
  | [], _, _, _ => by simp [compileExprListWithInternals, pure, Except.pure]
  | expr :: rest, hcore, hcall, hraw => by
      simp only [List.all_cons, Bool.and_eq_true, Bool.beq_eq_decide_eq,
        decide_eq_true_eq] at hcore
      simp only [exprListTouchesUnsupportedConstructorRawCalldataSurface,
        Bool.or_eq_false_iff] at hraw
      simp only [List.all_cons, Bool.and_eq_true, Bool.beq_eq_decide_eq,
        decide_eq_true_eq] at hcall
      rcases hcore with ⟨hcoreHead, hcoreTail⟩
      rcases hcall with ⟨hcallHead, hcallTail⟩
      rcases hraw with ⟨hrawHead, hrawTail⟩
      simp [compileExprListWithInternals,
        compileExpr_constructor_mode_eq hcoreHead hcallHead hrawHead,
        compileExprList_constructor_mode_eq hcoreTail hcallTail hrawTail,
        Bind.bind, Except.bind, Functor.map, Except.map]

private theorem compileRequireFailCond_constructor_mode_eq
    {fields : List Field}
    {cond : Expr}
    (hcoreClosed : exprTouchesUnsupportedCoreSurface cond = false)
    (hcallClosed : exprTouchesUnsupportedCallSurface cond = false)
    (hrawClosed : exprTouchesUnsupportedConstructorRawCalldataSurface cond = false) :
    compileRequireFailCondWithInternals fields .memory [] cond =
      compileRequireFailCondWithInternals fields .calldata [] cond := by
  cases cond <;>
    try simp_all [compileRequireFailCondWithInternals,
      compileExpr_constructor_mode_eq]
  · simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff] at hcoreClosed
    simp only [exprTouchesUnsupportedCallSurface, Bool.or_eq_false_iff] at hcallClosed
    simp only [exprTouchesUnsupportedConstructorRawCalldataSurface,
      Bool.or_eq_false_iff] at hrawClosed
    simp [
      compileRequireFailCondWithInternals,
      compileExpr_constructor_mode_eq hcoreClosed.1 hcallClosed.1 hrawClosed.1,
      compileExpr_constructor_mode_eq hcoreClosed.2 hcallClosed.2 hrawClosed.2]
  · simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff] at hcoreClosed
    simp only [exprTouchesUnsupportedCallSurface, Bool.or_eq_false_iff] at hcallClosed
    simp only [exprTouchesUnsupportedConstructorRawCalldataSurface,
      Bool.or_eq_false_iff] at hrawClosed
    simp [
      compileRequireFailCondWithInternals,
      compileExpr_constructor_mode_eq hcoreClosed.1 hcallClosed.1 hrawClosed.1,
      compileExpr_constructor_mode_eq hcoreClosed.2 hcallClosed.2 hrawClosed.2]

mutual
private theorem compileStmt_constructor_mode_eq
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {scope : List String}
    {stmt : Stmt}
    (heffectsClosed : stmtTouchesUnsupportedEffectSurface stmt = false)
    (hcoreClosed : stmtTouchesUnsupportedCoreSurface stmt = false)
    (hcallClosed : stmtTouchesUnsupportedCallSurface stmt = false)
    (hrawClosed : stmtTouchesUnsupportedConstructorRawCalldataSurface stmt = false) :
        compileStmt fields events errors .memory [] false scope [] stmt =
          compileStmt fields [] [] .calldata [] false scope [] stmt := by
    rw [← FunctionBody.compileStmtWithFork_cancun_eq_compileStmt
      fields events errors .memory [] false scope [] stmt]
    rw [← FunctionBody.compileStmtWithFork_cancun_eq_compileStmt
      fields [] [] .calldata [] false scope [] stmt]
    cases stmt with
    | forEach varName count body =>
        cases count <;>
          simp_all [stmtTouchesUnsupportedEffectSurface, stmtTouchesUnsupportedCoreSurface,
            stmtTouchesUnsupportedCallSurface, stmtTouchesUnsupportedConstructorRawCalldataSurface,
            exprTouchesUnsupportedCoreSurface, exprTouchesUnsupportedCallSurface,
            exprTouchesUnsupportedConstructorRawCalldataSurface,
            compileStmtWithFork, FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
            compileExpr_constructor_mode_eq, compileStmtList_constructor_mode_eq',
            compileExprWithInternals]
    | _ =>
        try simp [stmtTouchesUnsupportedEffectSurface] at heffectsClosed
        try simp [stmtTouchesUnsupportedCoreSurface] at hcoreClosed
        try simp [stmtTouchesUnsupportedCallSurface] at hcallClosed
        try simp [stmtTouchesUnsupportedConstructorRawCalldataSurface] at hrawClosed
        try simp_all [compileStmtWithFork,
          FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
          compileSetStorage, compileStorageArrayPush,
          compileSetStorageArrayElement, compileSetMapping2, compileSetMapping2Word,
          compileSetMappingChain, compileSetStructMember, compileSetStructMember2,
          compileRequireFailCond_constructor_mode_eq, compileExpr_constructor_mode_eq,
          compileExprList_constructor_mode_eq, compileStmtList_constructor_mode_eq',
          compileExprWithInternals, compileExprListWithInternals]

private theorem compileStmtList_constructor_mode_eq'
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {scope : List String} :
    ∀ {body : List Stmt},
      stmtListTouchesUnsupportedEffectSurface body = false →
      stmtListTouchesUnsupportedCoreSurface body = false →
      stmtListTouchesUnsupportedCallSurface body = false →
      stmtListTouchesUnsupportedConstructorRawCalldataSurface body = false →
        compileStmtList fields events errors .memory [] false scope [] body =
          compileStmtList fields [] [] .calldata [] false scope [] body
    | [], _, _, _, _ => by
        unfold compileStmtList
        unfold compileStmtListWithFork
        rfl
    | stmt :: rest, heffectsClosed, hcoreClosed, hcallClosed, hrawClosed => by
      simp only [stmtListTouchesUnsupportedEffectSurface,
        stmtListTouchesUnsupportedCoreSurface,
        stmtListTouchesUnsupportedCallSurface,
        stmtListTouchesUnsupportedConstructorRawCalldataSurface,
        Bool.or_eq_false_iff] at heffectsClosed hcoreClosed hcallClosed hrawClosed
      rcases heffectsClosed with ⟨heffectsStmt, heffectsRest⟩
      rcases hcoreClosed with ⟨hcoreStmt, hcoreRest⟩
      rcases hcallClosed with ⟨hcallStmt, hcallRest⟩
      rcases hrawClosed with ⟨hrawStmt, hrawRest⟩
      unfold compileStmtList
      unfold compileStmtListWithFork
      simp only [FunctionBody.compileStmtWithFork_cancun_eq_compileStmt,
        FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList]
      rw [
        compileStmt_constructor_mode_eq (events := events) (errors := errors)
          (scope := scope) heffectsStmt hcoreStmt hcallStmt hrawStmt,
        compileStmtList_constructor_mode_eq' (events := events) (errors := errors)
          (scope := collectStmtBindNames stmt ++ scope)
          heffectsRest hcoreRest hcallRest hrawRest]
end

/-- For effect-surface-closed + core-surface-closed + raw-calldata-surface-closed
bodies (which is guaranteed by SupportedConstructor), compilation is independent
of the events/errors lists and the dynamic source mode.

This holds because:
- `.emit` is blocked by effect surface → events never consulted
- `.requireError`/`.revertError` blocked by effect surface → errors never consulted
- `arrayElement`/`dynamicBytesEq` blocked by core surface → dynamic source never branched on
- `.calldataload` blocked by raw calldata surface → calldataload compilation path is dead -/
private theorem compileStmtList_constructor_mode_eq
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {body : List Stmt}
    (heffectsClosed : stmtListTouchesUnsupportedEffectSurface body = false)
    (hcoreClosed : stmtListTouchesUnsupportedCoreSurface body = false)
    (hcallClosed : stmtListTouchesUnsupportedCallSurface body = false)
    (hrawClosed : stmtListTouchesUnsupportedConstructorRawCalldataSurface body = false) :
      compileStmtList fields events errors .memory [] false [] [] body =
        compileStmtList fields [] [] .calldata [] false [] [] body := by
  exact compileStmtList_constructor_mode_eq' (events := events) (errors := errors)
    (scope := []) heffectsClosed hcoreClosed hcallClosed hrawClosed

/-- Erase only the transaction calldata-size word from a source runtime state.
Constructor execution uses deploy-time calldata (`args.length * 32`), while the
generic function interpreter uses selector-prefixed calldata (`4 + args.length *
32`). The two states are not judgmentally equal, even for an empty body, so
constructor bridging must use this observational relation rather than direct
`StmtResult` equality. -/
private def eraseRuntimeCalldataSize
    (state : SourceSemantics.RuntimeState) : SourceSemantics.RuntimeState :=
  { state with world := { state.world with calldataSize := 0 } }

/-- The constructor/function transaction contexts differ only in calldata size.
This is the base fact for the calldata-size bridge; a full execution bridge must
show raw-calldata-surface-closed bodies preserve this erased-state relation. -/
private theorem constructor_function_contexts_erase_calldataSize_eq
    {bindings : List (String × Nat)}
    {selector : Nat}
    {initialWorld : Verity.ContractState}
    {tx : IRTransaction} :
    eraseRuntimeCalldataSize
        { world := SourceSemantics.withConstructorTransactionContext initialWorld tx
          bindings := bindings
          selector := selector } =
      eraseRuntimeCalldataSize
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := selector } := by
  simp [eraseRuntimeCalldataSize, SourceSemantics.withConstructorTransactionContext,
    SourceSemantics.withTransactionContext]

private theorem execStmtListWithHelpers_constructor_calldataSize_eq
    {bindings : List (String × Nat)}
    {selector : Nat}
    {initialWorld : Verity.ContractState}
    {tx : IRTransaction} :
    eraseRuntimeCalldataSize
        { world := SourceSemantics.withConstructorTransactionContext initialWorld tx
          bindings := bindings
          selector := selector } =
      eraseRuntimeCalldataSize
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := selector } :=
  constructor_function_contexts_erase_calldataSize_eq

/-- Constructor calldataSize bound implies the stronger runtime calldataSize
bound because tx.args.length * 32 is a multiple of 32, so adding 4 cannot
cause overflow given the size of evmModulus (2^256). -/
private theorem txCalldataSizeFitsEvm_of_constructorCalldataSizeFitsEvm
    {tx : IRTransaction}
    (h : TxConstructorCalldataSizeFitsEvm tx) :
    TxCalldataSizeFitsEvm tx := by
  -- evmModulus = 2^256 = 2^251 * 32, so strict inequality `n*32 < evmModulus`
  -- forces `n+1 ≤ 2^251`, hence `4 + n*32 < evmModulus`.
  simp only [TxCalldataSizeFitsEvm, TxConstructorCalldataSizeFitsEvm,
    Compiler.Constants.evmModulus] at *
  have hk : (2 : Nat) ^ 256 = 2 ^ 251 * 32 := by norm_num
  rw [hk] at h ⊢
  have hlt : tx.args.length * 32 < 2 ^ 251 * 32 := h
  have hle : tx.args.length < 2 ^ 251 :=
    Nat.lt_of_mul_lt_mul_right hlt
  have : (tx.args.length + 1) * 32 ≤ 2 ^ 251 * 32 :=
    Nat.mul_le_mul_right 32 hle
  have hstep : 4 + tx.args.length * 32 < (tx.args.length + 1) * 32 := by
    omega
  exact lt_of_lt_of_le hstep this

private theorem bindingsExactlyMatchIRVars_applyBindingsToIRState_self
    {state : IRState}
    {bindings : List (String × Nat)}
    (hinit : FunctionBody.bindingsExactlyMatchIRVars [] state)
    (hnodup : (bindings.map Prod.fst).Nodup) :
    FunctionBody.bindingsExactlyMatchIRVars bindings
      (ParamLoading.applyBindingsToIRState state bindings) := by
  have hfold :
      FunctionBody.bindingsExactlyMatchIRVars
        (bindings.foldl (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) [])
        (ParamLoading.applyBindingsToIRState state bindings) :=
    FunctionBody.bindingsExactlyMatchIRVars_applyBindingsToIRState hinit
  intro queryName
  rw [hfold queryName]
  by_cases hmem : queryName ∈ bindings.map Prod.fst
  · exact lookupBinding?_foldl_bindValue_mem bindings [] queryName hmem hnodup
  · rw [lookupBinding?_foldl_bindValue_not_mem bindings [] queryName hmem]
    symm
    exact lookupBinding?_eq_none_of_not_mem bindings queryName hmem

private theorem constructorTouchesUnsupportedRawCalldataSurface_eq_false
    {model : CompilationModel}
    {ctor : ConstructorSpec}
    (hSupported : SupportedConstructor model ctor) :
    SourceSemantics.constructorTouchesUnsupportedRawCalldataSurface model ctor = false := by
  have hhelpers :
      SourceSemantics.helperClosureTouchesUnsupportedConstructorRawCalldataSurface model
        (model.functions.length + 1) (constructorAsFunctionSpec ctor) = false :=
    SourceSemantics.helperClosureTouchesUnsupportedConstructorRawCalldataSurface_eq_false_of_no_helper_calls
      (model.functions.length + 1)
      hSupported.body.helperCallNames_nil
  simp [SourceSemantics.constructorTouchesUnsupportedRawCalldataSurface,
    hSupported.rawCalldataSurfaceClosed, hhelpers]

private theorem wordNormalize_lt_evmModulus
    (n : Nat) :
    SourceSemantics.wordNormalize n < Compiler.Constants.evmModulus := by
  rw [SourceSemantics.wordNormalize_eq_mod]
  exact Nat.mod_lt n (by norm_num [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS])

private theorem constructorArgAliasRawValue_lt_evmModulus
    {rawArgs : List Nat}
    {headWord value : Nat}
    (hvalue :
      Option.map SourceSemantics.wordNormalize rawArgs[headWord]? =
        some value) :
    value < Compiler.Constants.evmModulus := by
  cases harg : rawArgs[headWord]? with
  | none =>
      simp [harg] at hvalue
  | some raw =>
      simp [harg] at hvalue
      cases hvalue
      exact wordNormalize_lt_evmModulus raw

private theorem constructorArgAliasLookupValue_lt_evmModulus
    {bindings : List (String × Nat)}
    {name : String}
    {value : Nat}
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hvalue : SourceSemantics.lookupBinding? bindings name = some value) :
    value < Compiler.Constants.evmModulus := by
  have hlookup' :
      FunctionBody.lookupBinding? bindings name = some value := by
    simpa [FunctionBody.lookupBinding?, SourceSemantics.lookupBinding?] using hvalue
  have hlookupValue :=
    FunctionBody.lookupValue_eq_of_lookupBinding?_some hlookup'
  rw [← hlookupValue]
  exact hbounded name

private theorem constructorArgAliasValue?_lt_evmModulus
    {param : Param}
    {rawArgs : List Nat}
    {headWord : Nat}
    {bindings : List (String × Nat)}
    {value : Nat}
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hvalue :
      SourceSemantics.constructorArgAliasValue? param rawArgs headWord bindings =
        some value) :
    value < Compiler.Constants.evmModulus := by
  rcases param with ⟨paramName, paramTy⟩
  unfold SourceSemantics.constructorArgAliasValue? at hvalue
  by_cases hdyn : isDynamicParamType paramTy = true
  · have hraw :
        Option.map SourceSemantics.wordNormalize rawArgs[headWord]? = some value := by
      rw [hdyn] at hvalue
      simp only [if_true] at hvalue
      exact hvalue
    exact constructorArgAliasRawValue_lt_evmModulus hraw
  · have hdynFalse : isDynamicParamType paramTy = false := by
      cases h : isDynamicParamType paramTy <;> simp [h] at hdyn ⊢
    rw [hdynFalse] at hvalue
    simp only [Bool.false_eq_true, if_false] at hvalue
    cases paramTy <;>
      first
      | exact constructorArgAliasLookupValue_lt_evmModulus hbounded hvalue
      | exact constructorArgAliasRawValue_lt_evmModulus hvalue

private theorem bindConstructorArgAliasesFrom_bounded
    {remaining : List Param}
    {rawArgs : List Nat}
    {idx headWord : Nat}
    {bindings out : List (String × Nat)}
    (hbind :
      SourceSemantics.bindConstructorArgAliasesFrom
        remaining rawArgs idx headWord bindings = some out)
    (hbounded : FunctionBody.bindingsBounded bindings) :
    FunctionBody.bindingsBounded out := by
  induction remaining generalizing idx headWord bindings out with
  | nil =>
      simp [SourceSemantics.bindConstructorArgAliasesFrom] at hbind
      cases hbind
      exact hbounded
  | cons param rest ih =>
      simp [SourceSemantics.bindConstructorArgAliasesFrom] at hbind
      cases hvalue :
          SourceSemantics.constructorArgAliasValue? param rawArgs headWord bindings <;>
        simp [hvalue] at hbind
      case some value =>
        exact ih hbind.2
          (FunctionBody.bindingsBounded_bindValue hbounded s!"arg{idx}" value
            (constructorArgAliasValue?_lt_evmModulus hbounded hvalue))

private theorem bindConstructorArgAliases_bounded
    {params : List Param}
    {rawArgs : List Nat}
    {bindings out : List (String × Nat)}
    (hbind :
      SourceSemantics.bindConstructorArgAliases params rawArgs bindings = some out)
    (hbounded : FunctionBody.bindingsBounded bindings) :
    FunctionBody.bindingsBounded out :=
  bindConstructorArgAliasesFrom_bounded
    (by simpa [SourceSemantics.bindConstructorArgAliases] using hbind)
    hbounded

private theorem bindValue_names_nodup
    {bindings : List (String × Nat)}
    {name : String}
    {value : Nat}
    (hnodup : (bindings.map Prod.fst).Nodup) :
    ((SourceSemantics.bindValue bindings name value).map Prod.fst).Nodup := by
  have hmapFilter :
      (bindings.filter (fun entry => entry.1 != name)).map Prod.fst =
        (bindings.map Prod.fst).filter (fun entryName => entryName != name) := by
    clear hnodup value
    induction bindings with
    | nil => simp
    | cons entry rest ih =>
        by_cases hentry : entry.1 = name <;> simp [hentry, ih]
  have hnameNotMem :
      name ∉ (bindings.filter (fun entry => entry.1 != name)).map Prod.fst := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨entry, hentry, hname⟩
    have hfilter := List.mem_filter.mp hentry
    have hne : entry.1 ≠ name := by
      intro hEq
      simp [hEq] at hfilter
    exact hne hname
  simp [SourceSemantics.bindValue, hnameNotMem, hmapFilter, hnodup.filter]

private theorem bindConstructorArgAliasesFrom_names_nodup
    {remaining : List Param}
    {rawArgs : List Nat}
    {idx headWord : Nat}
    {bindings out : List (String × Nat)}
    (hbind :
      SourceSemantics.bindConstructorArgAliasesFrom
        remaining rawArgs idx headWord bindings = some out)
    (hnodup : (bindings.map Prod.fst).Nodup) :
    (out.map Prod.fst).Nodup := by
  induction remaining generalizing idx headWord bindings out with
  | nil =>
      simp [SourceSemantics.bindConstructorArgAliasesFrom] at hbind
      cases hbind
      exact hnodup
  | cons param rest ih =>
      simp [SourceSemantics.bindConstructorArgAliasesFrom] at hbind
      cases hvalue :
          SourceSemantics.constructorArgAliasValue? param rawArgs headWord bindings <;>
        simp [hvalue] at hbind
      case some value =>
        exact ih hbind.2 (bindValue_names_nodup hnodup)

private theorem bindConstructorArgAliases_names_nodup
    {params : List Param}
    {rawArgs : List Nat}
    {bindings out : List (String × Nat)}
    (hbind :
      SourceSemantics.bindConstructorArgAliases params rawArgs bindings = some out)
    (hnodup : (bindings.map Prod.fst).Nodup) :
    (out.map Prod.fst).Nodup :=
  bindConstructorArgAliasesFrom_names_nodup
    (by simpa [SourceSemantics.bindConstructorArgAliases] using hbind)
    hnodup

/-! ## Constructor-body bridge notes

Instead of generalizing the 179+ `.calldata`-hardcoded step lemmas to accept
`.memory` mode, the constructor path first rewrites the compiled body through
the proven `SupportedConstructor` surface closures:

1. **Compilation mode equivalence** (`compileStmtList_constructor_mode_eq`):
   For bodies where effect/core/raw-calldata surfaces are all closed,
   `compileStmtList fields events errors .memory [] false [] body =
    compileStmtList fields [] [] .calldata [] false [] body`.
   This holds because emit/requireError/revertError (which use events/errors)
   are blocked by effect surface, and arrayElement/dynamicBytesEq/calldataload
   (where .memory≠.calldata) are blocked by core/raw-calldata surfaces.

2. **CalldataSize observation** (`execStmtListWithHelpers_constructor_calldataSize_eq`):
   Constructor and function transaction contexts differ only in the
   `calldataSize` word. The supported constructor surface is raw-calldata-closed,
   so the body bridge reuses the runtime function context while retaining the
   named erased-calldata fact for the deploy-time context.

3. **Calldata bound lifting** (`txCalldataSizeFitsEvm_of_constructorCalldataSizeFitsEvm`):
   TxConstructorCalldataSizeFitsEvm ⊂ TxCalldataSizeFitsEvm by simple arithmetic.

These bridges set up reuse of the existing `.calldata` +
`runtimeStateMatchesIR` + `withTransactionContext` step infrastructure once the
scope/fuel alignment below is completed. -/

/-- Source runtime state in which a constructor body runs. -/
private abbrev constructorBodySourceState (model : CompilationModel)
    (initialWorld : Verity.ContractState)
    (tx : IRTransaction) (ctorBindings : List (String × Nat)) : SourceSemantics.RuntimeState :=
  { world := SourceSemantics.withTransactionContext initialWorld tx
    bindings := ctorBindings
    selector := tx.functionSelector
    errors := model.errors }

/-- IR state in which the compiled constructor body runs. -/
private abbrev constructorBodyIRState (model : CompilationModel) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (ctorBindings : List (String × Nat)) : IRState :=
  ParamLoading.applyBindingsToIRState (FunctionBody.initialIRStateForTx model tx initialWorld)
    ctorBindings

private theorem constructor_body_aliases_of_executionBindings
    {ctor : ConstructorSpec} {tx : IRTransaction} {bindings ctorBindings : List (String × Nat)}
    (hbind :
      SourceSemantics.bindSupportedParams ctor.params (tx.args.take ctor.params.length) =
        some bindings)
    (hconstructorBindings :
      SourceSemantics.constructorExecutionBindings ctor tx.args = some ctorBindings) :
    SourceSemantics.bindConstructorArgAliases ctor.params tx.args bindings =
      some ctorBindings := by
  unfold SourceSemantics.constructorExecutionBindings at hconstructorBindings
  simpa [hbind] using hconstructorBindings

/-- The memory-mode constructor body compiles exactly like the calldata-mode body over
the effective fields, by the constructor-surface mode equivalence. -/
private theorem constructor_body_compile_effective_of_memory
    {model : CompilationModel} {ctor : ConstructorSpec} {bodyStmts : List YulStmt}
    (hnormalized : applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hSupported : SupportedConstructor model ctor)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .memory [] false
        (constructorBodyScope ctor.params) [] ctor.body = Except.ok bodyStmts) :
    compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
      (constructorBodyScope ctor.params) [] ctor.body = Except.ok bodyStmts := by
  have hmode :=
    compileStmtList_constructor_mode_eq' (fields := model.fields)
      (events := model.events) (errors := model.errors)
      (scope := constructorBodyScope ctor.params) (body := ctor.body)
      hSupported.body.effects.surfaceClosed hSupported.body.core.surfaceClosed
      (SupportedBodyCallInterface.surfaceClosed_exceptMappingWrites hSupported.body)
      hSupported.rawCalldataSurfaceClosed
  rw [hbodyCompile] at hmode
  simpa [SourceSemantics.effectiveFields, hnormalized] using hmode.symm

private theorem constructor_body_bindings_exact
    {model : CompilationModel} {ctor : ConstructorSpec} {tx : IRTransaction}
    {initialWorld : Verity.ContractState} {bindings ctorBindings : List (String × Nat)}
    (hSupported : SupportedConstructor model ctor)
    (hbind :
      SourceSemantics.bindSupportedParams ctor.params (tx.args.take ctor.params.length) =
        some bindings)
    (haliases :
      SourceSemantics.bindConstructorArgAliases ctor.params tx.args bindings =
        some ctorBindings) :
    FunctionBody.bindingsExactlyMatchIRVars ctorBindings
      (constructorBodyIRState model tx initialWorld ctorBindings) :=
  bindingsExactlyMatchIRVars_applyBindingsToIRState_self
    (FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld)
    (bindConstructorArgAliases_names_nodup haliases
      (ParamLoading.bindSupportedParams_names_nodup hSupported.params.namesNodup hbind))

/-- Every constructor-body scope name (argument aliases and decoded parameters) is bound. -/
private theorem constructor_body_scope_present
    {ctor : ConstructorSpec} {tx : IRTransaction} {bindings ctorBindings : List (String × Nat)}
    (hbind :
      SourceSemantics.bindSupportedParams ctor.params (tx.args.take ctor.params.length) =
        some bindings)
    (hconstructorBindings :
      SourceSemantics.constructorExecutionBindings ctor tx.args = some ctorBindings) :
    FunctionBody.scopeNamesPresent (constructorBodyScope ctor.params) ctorBindings := by
  intro name hmem
  simp [constructorBodyScope, constructorArgAliasNames] at hmem
  rcases hmem with ⟨idx, hidx, rfl⟩ | hmemParam
  · exact SourceSemantics.constructorExecutionBindings_argAlias_present
      hconstructorBindings hidx
  · have hmemBindings : name ∈ bindings.map Prod.fst := by
      rw [ParamLoading.bindSupportedParams_names hbind]
      simpa using hmemParam
    rcases lookupBinding?_some_of_mem bindings name hmemBindings with ⟨value, hvalue⟩
    exact SourceSemantics.bindConstructorArgAliasesFrom_preserves_lookup
      (by simpa [SourceSemantics.bindConstructorArgAliases] using
        constructor_body_aliases_of_executionBindings hbind hconstructorBindings)
      ⟨value, by simpa [FunctionBody.lookupBinding?, SourceSemantics.lookupBinding?] using hvalue⟩

private theorem constructor_body_generic
    {model : CompilationModel} {ctor : ConstructorSpec}
    (hnormalized : applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hSupported : SupportedConstructor model ctor)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : ∀ stmt ∈ ctor.body, StmtMappingWriteSlotSafe model.fields stmt)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = []) :
    StmtListGenericWithHelpers model (SourceSemantics.effectiveFields model)
      (constructorBodyScope ctor.params) ctor.body := by
  have hscopeEq :
      (constructorAsFunctionSpec ctor).params.map (·.name) =
        constructorBodyScope ctor.params := by
    simp [constructorAsFunctionSpec, constructorBodyScope, constructorArgAliasNames,
      Function.comp_apply, List.map_map, Param.toIRParam]
  have hhelperFree :
      StmtListHelperFreeStepInterface (SourceSemantics.effectiveFields model)
        (constructorBodyScope ctor.params) ctor.body := by
    rw [show SourceSemantics.effectiveFields model = model.fields by
      simp [SourceSemantics.effectiveFields, hnormalized], ← hscopeEq]
    exact hSupported.body.helperFreeStepInterface_stmtSafety hnoConflict hsafety
  exact stmtListGenericWithHelpers_of_helperFreeStepInterface_and_helperSurfaceClosed
    (spec := model) (hhelperFree := hhelperFree) (hnoEvents := hnoEvents)
    (hnoErrors := hnoErrors)
    (hsurface := by simpa [constructorAsFunctionSpec] using hSupported.body.helperSurfaceClosed)

private theorem constructor_body_stmtResult_matches
    {model : CompilationModel} {ctor : ConstructorSpec} {helperFuel : Nat}
    {tx : IRTransaction} {initialWorld : Verity.ContractState}
    {ctorBindings : List (String × Nat)} {bodyStmts : List YulStmt}
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (hgeneric : StmtListGenericWithHelpers model (SourceSemantics.effectiveFields model)
      (constructorBodyScope ctor.params) ctor.body)
    (hscope : FunctionBody.scopeNamesPresent (constructorBodyScope ctor.params) ctorBindings)
    (hstateBindings : FunctionBody.bindingsExactlyMatchIRVars ctorBindings
      (constructorBodyIRState model tx initialWorld ctorBindings))
    (hbounded : FunctionBody.bindingsBounded ctorBindings)
    (hstateRuntime : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
      (constructorBodySourceState model initialWorld tx ctorBindings)
      (constructorBodyIRState model tx initialWorld ctorBindings))
    (hcompile : compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
      (constructorBodyScope ctor.params) [] ctor.body = Except.ok bodyStmts) :
    FunctionBody.stmtResultMatchesIRExec (SourceSemantics.effectiveFields model)
      (SourceSemantics.execStmtListWithHelpers model (SourceSemantics.effectiveFields model)
        helperFuel (constructorBodySourceState model initialWorld tx ctorBindings) ctor.body)
      (execIRStmts (sizeOf bodyStmts + 1)
        (constructorBodyIRState model tx initialWorld ctorBindings) bodyStmts) := by
  rcases exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel helperFuel 0 hgeneric hscope
      (FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings) hbounded
      hnoEvents hnoErrors hstateRuntime with ⟨bodyIR, hcompileIR, hmatch⟩
  rw [hcompile] at hcompileIR
  cases hcompileIR
  exact hmatch

/-- Package the constructor body match into the constructor result relation. -/
private theorem constructor_body_result_of_matches
    {model : CompilationModel} {ctor : ConstructorSpec} {helperFuel : Nat}
    {tx : IRTransaction} {initialWorld : Verity.ContractState}
    {ctorBindings : List (String × Nat)} {bodyStmts : List YulStmt}
    (hrawUnsupported :
      SourceSemantics.constructorTouchesUnsupportedRawCalldataSurface model ctor = false)
    (hconstructorBindings :
      SourceSemantics.constructorExecutionBindings ctor tx.args = some ctorBindings)
    (hmatch : FunctionBody.stmtResultMatchesIRExec (SourceSemantics.effectiveFields model)
      (SourceSemantics.execStmtListWithHelpers model (SourceSemantics.effectiveFields model)
        helperFuel (constructorBodySourceState model initialWorld tx ctorBindings) ctor.body)
      (execIRStmts (sizeOf bodyStmts + 1)
        (constructorBodyIRState model tx initialWorld ctorBindings) bodyStmts)) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretConstructorWithHelpers model helperFuel ctor tx initialWorld)
      (execResultToIRResult (FunctionBody.initialIRStateForTx model tx initialWorld)
        (execIRStmts (sizeOf bodyStmts + 1)
          (constructorBodyIRState model tx initialWorld ctorBindings) bodyStmts)) := by
  have hpack := FunctionBody.stmtResultToSourceResult_matches_irExecResult model
    (SourceSemantics.effectiveFields model) (SourceSemantics.withTransactionContext initialWorld tx)
    (FunctionBody.initialIRStateForTx model tx initialWorld) _ _
    (by funext s; simp [FunctionBody.initialIRStateForTx,
      FunctionBody.encodeStorage_withTransactionContext])
    (by simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext])
    rfl hmatch
  rw [SourceSemantics.interpretConstructorWithHelpers, hrawUnsupported, hconstructorBindings]
  exact hpack

private theorem constructor_body_runtime_matches
    {model : CompilationModel} {tx : IRTransaction} {initialWorld : Verity.ContractState}
    (ctorBindings : List (String × Nat))
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxConstructorCalldataSizeFitsEvm tx) :
    FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
      (constructorBodySourceState model initialWorld tx ctorBindings)
      (constructorBodyIRState model tx initialWorld ctorBindings) := by
  have hinit := initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized
    (txCalldataSizeFitsEvm_of_constructorCalldataSizeFitsEvm hcalldataSizeFits)
  simpa [FunctionBody.runtimeStateMatchesIR] using
    runtimeStateMatchesIR_applyBindingsToIRState
      (fields := SourceSemantics.effectiveFields model) hinit ctorBindings

/-- Constructor-body bridge for the currently proved statement fragment.
This proves the user-written constructor body after constructor arguments have
already been decoded into IR locals. The initcode wrapper that materializes
those locals from deploy-time bytecode is still outside the current proof
interpreter surface.

The bridge shape is described in the constructor-body bridge notes above. -/
theorem supported_constructor_body_correct_with_body_interface
    (model : CompilationModel) (ctor : ConstructorSpec) (helperFuel : Nat)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hfunctionNamesNodup : (model.functions.map (·.name)).Nodup)
    (hSupported : SupportedConstructor model ctor)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : ∀ stmt ∈ ctor.body, StmtMappingWriteSlotSafe model.fields stmt)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat)) (ctorBindings : List (String × Nat))
    (bodyStmts : List YulStmt)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .memory [] false
        (constructorBodyScope ctor.params) [] ctor.body = Except.ok bodyStmts)
    (hbind :
      SourceSemantics.bindSupportedParams ctor.params (tx.args.take ctor.params.length) =
        some bindings)
    (hconstructorBindings :
      SourceSemantics.constructorExecutionBindings ctor tx.args = some ctorBindings)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxConstructorCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretConstructorWithHelpers model helperFuel ctor tx initialWorld)
      (execResultToIRResult
        (FunctionBody.initialIRStateForTx model tx initialWorld)
        (execIRStmts
            (sizeOf bodyStmts + 1)
            (ParamLoading.applyBindingsToIRState
              (FunctionBody.initialIRStateForTx model tx initialWorld)
              ctorBindings)
            bodyStmts)) := by
  let _ := hfunctionNamesNodup
  have haliases := constructor_body_aliases_of_executionBindings hbind hconstructorBindings
  exact constructor_body_result_of_matches
    (constructorTouchesUnsupportedRawCalldataSurface_eq_false hSupported) hconstructorBindings
    (constructor_body_stmtResult_matches hnoEvents hnoErrors
      (constructor_body_generic hnormalized hSupported hnoConflict hsafety hnoEvents hnoErrors)
      (constructor_body_scope_present hbind hconstructorBindings)
      (constructor_body_bindings_exact hSupported hbind haliases)
      (bindConstructorArgAliases_bounded haliases
        (FunctionBody.bindingsBounded_of_bindSupportedParams hbind))
      (constructor_body_runtime_matches ctorBindings htxNormalized hcalldataSizeFits)
      (constructor_body_compile_effective_of_memory hnormalized hSupported hbodyCompile))

/-- IR state after prebinding raw arguments and loading the bound parameters. -/
private abbrev bodyInterfaceParamState (model : CompilationModel) (fn : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat)) : IRState :=
  ParamLoading.applyBindingsToIRState
    (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params) bindings

/-- Source runtime of the transaction under the given parameter bindings. -/
private abbrev bodyInterfaceRuntime (model : CompilationModel)
    (initialWorld : Verity.ContractState) (tx : IRTransaction)
    (bindings : List (String × Nat)) : SourceSemantics.RuntimeState :=
  { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := bindings,
    selector := tx.functionSelector, errors := model.errors }

/-- Spare fuel of the canonical compiled function beyond its statement count. -/
private noncomputable abbrev bodyInterfaceExtraFuel (selector : Nat) (fn : FunctionSpec)
    (returns : List ParamType) (bodyStmts : List YulStmt) : Nat :=
  sizeOf (compiledFunctionIR selector fn returns bodyStmts).body -
    (compiledFunctionIR selector fn returns bodyStmts).body.length

/-- The component compilation facts of a function: validation, return types, and body. -/
private abbrev BodyInterfaceCompiled (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (fn : FunctionSpec) (returns : List ParamType)
    (bodyStmts : List YulStmt) : Prop :=
  validateFunctionSpec fn = Except.ok () ∧ functionReturns fn = Except.ok returns ∧
    compileStmtList fields events errors .calldata [] false (fn.params.map (·.name)) []
      fn.body = Except.ok bodyStmts

/-- Global model normalization facts shared by the body-interface bridges. -/
private abbrev BodyInterfaceModelNormal (model : CompilationModel) : Prop :=
  SourceSemantics.effectiveFields model = model.fields ∧ model.events = [] ∧
    model.errors = [] ∧ model.adtTypes = []

/-- The parameter-loaded IR state still matches the initial source runtime. -/
private theorem body_interface_param_state_runtime
    {model : CompilationModel} {fn : FunctionSpec} {tx : IRTransaction}
    {initialWorld : Verity.ContractState} {bindings : List (String × Nat)}
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
      (bodyInterfaceRuntime model initialWorld tx [])
      (bodyInterfaceParamState model fn tx initialWorld bindings) :=
  runtimeStateMatchesIR_applyBindingsToIRState
    (runtimeStateMatchesIR_prebindRawArgs
      (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized
        hcalldataSizeFits) fn.params) bindings

/-- The parameter-loaded IR state binds exactly the parameter bindings. -/
private theorem body_interface_param_state_bindings
    {model : CompilationModel} {fn : FunctionSpec} {tx : IRTransaction}
    {initialWorld : Verity.ContractState} {bindings : List (String × Nat)}
    (hparamNamesNodup : (fn.params.map (·.name)).Nodup)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings) :
    FunctionBody.bindingsExactlyMatchIRVars bindings
      (bodyInterfaceParamState model fn tx initialWorld bindings) :=
  supported_function_param_state_exact _ fn.params bindings
    (FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld)
    hparamNamesNodup hbind

/-- A successful `compileFunctionSpec` is the canonical `compiledFunctionIR`. -/
private theorem body_interface_irFn_eq
    {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    {selector : Nat} {fn : FunctionSpec} {habi : fn.abiDecoding = .standard}
    {returns : List ParamType} {bodyStmts : List YulStmt} {irFn : IRFunction}
    (hparts : BodyInterfaceCompiled fields events errors fn returns bodyStmts)
    (hcompile : compileFunctionSpec fields events errors [] selector fn = Except.ok irFn) :
    irFn = compiledFunctionIR selector fn returns bodyStmts := by
  have hcompiled := compileFunctionSpec_ok_of_components (habi := habi) fields events errors
    selector fn returns bodyStmts hparts.1 hparts.2.1 hparts.2.2
  rw [hcompile] at hcompiled
  injection hcompiled

/-- Parameter-load prefix plus body plus spare fuel is the compiled body's size. -/
private theorem body_interface_body_fuel_eq
    (selector : Nat) (fn : FunctionSpec) (returns : List ParamType)
    (bodyStmts : List YulStmt) :
    (genParamLoads fn.params ++ bodyStmts).length +
        bodyInterfaceExtraFuel selector fn returns bodyStmts =
      sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
  have hlenle := Nat.le_of_add_le_add_right
    (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
  simpa [bodyInterfaceExtraFuel, compiledFunctionIR] using Nat.add_sub_of_le hlenle

/-- Fuel adequacy tail: once the fuel is exactly `sizeOf body + 1`, the
fuel-indexed function result is the total `execIRFunction` result. -/
private theorem body_interface_execIRFunction_of_fuel
    {source : SourceSemantics.SourceContractResult} {fn : IRFunction} {args : List Nat}
    {state : IRState} {prefixLen extraFuel : Nat}
    (hfuel : prefixLen + extraFuel = sizeOf fn.body)
    (hmatch : FunctionBody.sourceResultMatchesIRResult source
      (Compiler.Proofs.YulGeneration.execIRFunctionFuel (prefixLen + extraFuel + 1)
        fn args state)) :
    FunctionBody.sourceResultMatchesIRResult source (execIRFunction fn args state) := by
  have hadequate : Compiler.Proofs.YulGeneration.execIRFunctionFuel (sizeOf fn.body + 1)
      fn args state = execIRFunction fn args state :=
    Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate fn args state
  rwa [hfuel, hadequate] at hmatch

/-- Every parameter name is bound after a successful parameter binding. -/
private theorem body_interface_scopeNamesPresent
    {params : List Param} {args : List Nat} {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings) :
    FunctionBody.scopeNamesPresent (params.map (·.name)) bindings := by
  intro name hmem
  have hmemBindings : name ∈ bindings.map Prod.fst := by
    rw [ParamLoading.bindSupportedParams_names hbind]
    simpa using hmem
  exact lookupBinding?_some_of_mem bindings name hmemBindings

/-- Helper-surface-closed bodies run identically with or without helper semantics. -/
private theorem body_interface_execStmtList_of_withHelpers
    {model : CompilationModel} {helperFuel : Nat} {state : SourceSemantics.RuntimeState}
    {stmts : List Stmt} {result : SourceSemantics.StmtResult}
    (hnoEvents : model.events = [])
    (hclosed : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (hsource : SourceSemantics.execStmtListWithHelpers model
      (SourceSemantics.effectiveFields model) helperFuel state stmts = result) :
    SourceSemantics.execStmtList (SourceSemantics.effectiveFields model) state stmts =
      result := by
  simpa [hnoEvents] using
    (SourceSemantics.execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed model
      _ helperFuel state stmts hclosed).symm.trans hsource

/-- Terminal-core branch of the body-interface body goal. -/
private theorem body_interface_body_goal_of_terminal
    (model : CompilationModel) (fn : FunctionSpec) (bodyStmts : List YulStmt)
    (helperFuel : Nat) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (state : IRState) (bindings : List (String × Nat)) (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (hhelperGoal : SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal model
      (SourceSemantics.effectiveFields model) helperFuel
      (bodyInterfaceRuntime model initialWorld tx bindings) fn.body)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hstateRuntime : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
      (bodyInterfaceRuntime model initialWorld tx []) state)
    (hstateBindings : FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersIRPreservationGoal model fn bodyStmts helperFuel tx
      initialWorld state bindings extraFuel := by
  rcases supported_function_body_correct_from_exact_state_terminal_core_extraFuel model fn
      bodyStmts tx initialWorld state bindings extraFuel hextraFuel hnormalized hnoEvents
      hnoErrors hbind hterminal hbodyCompile hstateRuntime hstateBindings with
    ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  exact ⟨sourceResult, irExec, hhelperGoal.trans (by simpa [hnoEvents] using hsource),
    hbodyExec, hmatch⟩

/-- Generic helper-free branch of the body-interface body goal. -/
private theorem body_interface_body_goal_of_generic
    (model : CompilationModel) (fn : FunctionSpec) (bodyStmts : List YulStmt)
    (helperFuel : Nat) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (state : IRState) (bindings : List (String × Nat)) (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hclosed : stmtListTouchesUnsupportedHelperSurface fn.body = false)
    (hhelperFree : StmtListHelperFreeStepInterface (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hstateRuntime : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
      (bodyInterfaceRuntime model initialWorld tx []) state)
    (hstateBindings : FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersIRPreservationGoal model fn bodyStmts helperFuel tx
      initialWorld state bindings extraFuel :=
  supported_function_body_correct_from_exact_state_generic_with_helpers model fn bodyStmts
    helperFuel tx initialWorld state bindings extraFuel hextraFuel hnormalized hnoEvents
    hnoErrors hnoAdtTypes hclosed hhelperFree (by rw [hnoAdtTypes]; exact hbodyCompile)
    (body_interface_scopeNamesPresent hbind)
    (FunctionBody.bindingsBounded_of_bindSupportedParams hbind) hstateRuntime hstateBindings

/-- Function-level finish: the helper-aware body goal at the compiled function's
spare fuel yields the legacy function result match. -/
private theorem body_interface_interpretFunction_of_body_goal
    (model : CompilationModel) (fn : FunctionSpec) {habi : fn.abiDecoding = .standard}
    (helperFuel : Nat) (hnoEvents : model.events = [])
    (hnormalized : applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hparamsSupported : ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hclosed : stmtListTouchesUnsupportedHelperSurface fn.body = false)
    (selector : Nat) (returns : List ParamType) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (hparts : BodyInterfaceCompiled (applySlotAliasRanges model.fields model.slotAliasRanges)
      model.events model.errors fn returns bodyStmts)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hgoal : SupportedFunctionBodyWithHelpersIRPreservationGoal model fn bodyStmts helperFuel
      tx initialWorld (bodyInterfaceParamState model fn tx initialWorld bindings) bindings
      (bodyInterfaceExtraFuel selector fn returns bodyStmts)) :
    FunctionBody.sourceResultMatchesIRResult (SourceSemantics.interpretFunction model fn tx
      initialWorld) (execIRFunction (compiledFunctionIR selector fn returns bodyStmts) tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rcases hgoal with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  exact body_interface_execIRFunction_of_fuel (body_interface_body_fuel_eq selector fn returns
    bodyStmts) (compileFunctionSpec_correct_of_body_normalized_extraFuel (habi := habi) model
      hnormalized selector fn _ returns bodyStmts tx initialWorld sourceResult irExec bindings _
      hparts.1 hparts.2.1 hparts.2.2 (compileFunctionSpec_ok_of_components (habi := habi) _ _ _
        selector fn returns bodyStmts hparts.1 hparts.2.1 hparts.2.2) hparamsSupported
      hcalldataSizeFits hbind hnoEvents (body_interface_execStmtList_of_withHelpers hnoEvents
        hclosed hsource) hbodyExec hmatch)

/-- Helper-aware body goal from the parameter-loaded initial IR state. -/
private theorem body_interface_body_goal
    (model : CompilationModel) (fn : FunctionSpec) (bodyStmts : List YulStmt)
    (helperFuel : Nat) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat)) (extraFuel : Nat) (hmodel : BodyInterfaceModelNormal model)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hhelperGoal : SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal model
      (SourceSemantics.effectiveFields model) helperFuel
      (bodyInterfaceRuntime model initialWorld tx bindings) fn.body)
    (hclosed : stmtListTouchesUnsupportedHelperSurface fn.body = false)
    (hhelperFree : StmtListHelperFreeStepInterface model.fields (fn.params.map (·.name)) fn.body)
    (hparamNamesNodup : (fn.params.map (·.name)).Nodup)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts) :
    SupportedFunctionBodyWithHelpersIRPreservationGoal model fn bodyStmts helperFuel tx
      initialWorld (bodyInterfaceParamState model fn tx initialWorld bindings) bindings
      extraFuel := by
  by_cases hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body
  · exact body_interface_body_goal_of_terminal model fn bodyStmts helperFuel tx initialWorld _
      bindings extraFuel hextraFuel hmodel.1 hmodel.2.1 hmodel.2.2.1 hhelperGoal hbind hterminal
      hbodyCompile (body_interface_param_state_runtime htxNormalized hcalldataSizeFits)
      (body_interface_param_state_bindings hparamNamesNodup hbind)
  · exact body_interface_body_goal_of_generic model fn bodyStmts helperFuel tx initialWorld _
      bindings extraFuel hextraFuel hmodel.1 hmodel.2.1 hmodel.2.2.1 hmodel.2.2.2 hclosed (hmodel.1
      ▸ hhelperFree) hbind hbodyCompile (body_interface_param_state_runtime htxNormalized
      hcalldataSizeFits) (body_interface_param_state_bindings hparamNamesNodup hbind)

/-- The compiled function's spare fuel covers the body's own spare fuel. -/
private theorem body_interface_extraFuel_lower
    (selector : Nat) (fn : FunctionSpec) (returns : List ParamType)
    (bodyStmts : List YulStmt) :
    sizeOf bodyStmts - bodyStmts.length ≤ bodyInterfaceExtraFuel selector fn returns bodyStmts := by
  simpa [bodyInterfaceExtraFuel, compiledFunctionIR] using
    yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts

/-- Function-level Tier 2 bridge for bodies admitted by the alternate
singleton storage-write state interface. This keeps the theorem local to one
function: global normalization and no-event/no-error assumptions remain
explicit, while the body proof can now use the non-vacuous singleton
mapping-write step interfaces instead of contradiction. -/
theorem supported_function_correct_with_body_interface_except_mapping_writes
    (model : CompilationModel) (fn : FunctionSpec) {habi : fn.abiDecoding = .standard}
    (helperFuel : Nat)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = []) (hparams : SupportedParamProfile fn.params)
    (hBody : SupportedBodyInterfaceExceptMappingWrites model fn)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (selector : Nat) (returns : List ParamType) (bodyStmts : List YulStmt) (irFn : IRFunction)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunctionWithHelpers model helperFuel fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hirFn := body_interface_irFn_eq (habi := habi) ⟨hvalidate, hreturns, hbodyCompile⟩
    hcompile
  subst hirFn
  rw [SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
    model helperFuel fn tx initialWorld hBody.helperSurfaceClosed]
  exact body_interface_interpretFunction_of_body_goal model fn (habi := habi) helperFuel
    hnoEvents hnormalized hparams.supported hBody.helperSurfaceClosed selector returns bodyStmts
    tx initialWorld bindings ⟨hvalidate, hreturns, hnormalized.symm ▸ hbodyCompile⟩ hbind
    hcalldataSizeFits
    (body_interface_body_goal model fn bodyStmts helperFuel tx initialWorld bindings _
      ⟨hnormalized, hnoEvents, hnoErrors, hnoAdtTypes⟩
      (body_interface_extraFuel_lower selector fn returns bodyStmts)
      (SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
        model _ helperFuel _ fn.body hBody.helperSurfaceClosed)
      hBody.helperSurfaceClosed (hBody.helperFreeStepInterface hnoConflict hsafety)
      hparams.namesNodup hbind htxNormalized hcalldataSizeFits hbodyCompile)

/-- Body-local variant of
`supported_function_correct_with_body_interface_except_mapping_writes (habi := habi)`.
This keeps the alternate Tier 2 theorem usable for concrete contracts whose
mapping-write safety argument is only available for the statements that
actually occur in the current body. -/
theorem supported_function_correct_with_body_interface_except_mapping_writes_stmtSafety
    (model : CompilationModel) (fn : FunctionSpec) {habi : fn.abiDecoding = .standard}
    (helperFuel : Nat)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = []) (hparams : SupportedParamProfile fn.params)
    (hBody : SupportedBodyInterfaceExceptMappingWrites model fn)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : ∀ stmt ∈ fn.body, StmtMappingWriteSlotSafe model.fields stmt)
    (selector : Nat) (returns : List ParamType) (bodyStmts : List YulStmt) (irFn : IRFunction)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunctionWithHelpers model helperFuel fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hirFn := body_interface_irFn_eq (habi := habi) ⟨hvalidate, hreturns, hbodyCompile⟩
    hcompile
  subst hirFn
  rw [SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
    model helperFuel fn tx initialWorld hBody.helperSurfaceClosed]
  exact body_interface_interpretFunction_of_body_goal model fn (habi := habi) helperFuel
    hnoEvents hnormalized hparams.supported hBody.helperSurfaceClosed selector returns bodyStmts
    tx initialWorld bindings ⟨hvalidate, hreturns, hnormalized.symm ▸ hbodyCompile⟩ hbind
    hcalldataSizeFits
    (body_interface_body_goal model fn bodyStmts helperFuel tx initialWorld bindings _
      ⟨hnormalized, hnoEvents, hnoErrors, hnoAdtTypes⟩
      (body_interface_extraFuel_lower selector fn returns bodyStmts)
      (SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
        model _ helperFuel _ fn.body hBody.helperSurfaceClosed)
      hBody.helperSurfaceClosed (hBody.helperFreeStepInterface_stmtSafety hnoConflict hsafety)
      hparams.namesNodup hbind htxNormalized hcalldataSizeFits hbodyCompile)

/-- Function-level Tier 2 bridge from the alternate contract support witness.
This is the selector-dispatched analogue of `supported_function_correct`,
reusing the weakened body interface instead of the default fail-closed state
surface. -/
theorem supported_function_correct_except_mapping_writes
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (fn : FunctionSpec) (selector : Nat) (irFn : IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hfn' := hSupported.supportedFunctionOfSelectorDispatched hfn
  obtain ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, rfl⟩ :=
    compileFunctionSpec_ok_components (habi := hfn'.standardAbi) _ _ _ selector fn irFn hcompileFn
  exact SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
    model hSupported.helperFuel fn tx initialWorld hfn'.body.helperSurfaceClosed ▸
    supported_function_correct_with_body_interface_except_mapping_writes model fn
    (habi := hfn'.standardAbi) hSupported.helperFuel hSupported.normalizedFields hSupported.noEvents
    hSupported.noErrors hSupported.noAdtTypes hfn'.params hfn'.body hnoConflict hsafety selector
    returns bodyStmts _ tx initialWorld bindings hvalidate hreturns hbodyCompile hcompileFn hbind
    htxNormalized hcalldataSizeFits

theorem supported_function_correct_except_mapping_writes_stmtSafety
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (fn : FunctionSpec) (selector : Nat) (irFn : IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : ∀ stmt ∈ fn.body, StmtMappingWriteSlotSafe model.fields stmt)
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hfn' := hSupported.supportedFunctionOfSelectorDispatched hfn
  obtain ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, rfl⟩ :=
    compileFunctionSpec_ok_components (habi := hfn'.standardAbi) _ _ _ selector fn irFn hcompileFn
  exact SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
    model hSupported.helperFuel fn tx initialWorld hfn'.body.helperSurfaceClosed ▸
    supported_function_correct_with_body_interface_except_mapping_writes_stmtSafety model fn
    (habi := hfn'.standardAbi) hSupported.helperFuel hSupported.normalizedFields hSupported.noEvents
    hSupported.noErrors hSupported.noAdtTypes hfn'.params hfn'.body hnoConflict hsafety selector
    returns bodyStmts _ tx initialWorld bindings hvalidate hreturns hbodyCompile hcompileFn hbind
    htxNormalized hcalldataSizeFits

/-- Validated compile inputs leave no conflicting field write slots. -/
private theorem helper_proofs_goal_firstFieldWriteSlotConflict_eq_none
    {model : CompilationModel} {selectors : List Nat} (hSupported : SupportedSpec model selectors)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ()) :
    firstFieldWriteSlotConflict model.fields = none := by
  simpa [hSupported.normalizedFields] using
    firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs (spec := model)
      (selectors := selectors) hvalidateInputs

/-- Goal-based helper-proof-carrying variant of `supported_function_correct`.
This keeps the current helper-free source-side conservative-extension premise
available as a wrapper, but the exact future helper seam is now the direct
helper-aware body/IR goal exposed by
`supported_function_correct_with_helper_proofs_body_goal`. -/
theorem supported_function_correct_with_helper_proofs_goal
    (model : CompilationModel) (selectors : List Nat) (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec) (selector : Nat) (returns : List ParamType) (bodyStmts : List YulStmt)
    (irFn : IRFunction) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat)) (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx)
    (hbodyHelperGoal : SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal model
      (SourceSemantics.effectiveFields model) hSupported.helperFuel
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := bindings
        selector := tx.functionSelector, errors := model.errors } fn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hfn' := hSupported.supportedFunctionOfSelectorDispatched hfn
  have hirFn := body_interface_irFn_eq (habi := hfn'.standardAbi)
    ⟨hvalidate, hreturns, hbodyCompile⟩ hcompile
  subst hirFn
  have hnoConflict :=
    helper_proofs_goal_firstFieldWriteSlotConflict_eq_none hSupported hvalidateInputs
  exact supported_function_correct_with_helper_proofs_body_goal model selectors hSupported
    hHelperProofs hvalidateInputs fn selector returns bodyStmts _ tx initialWorld bindings hfn
    hvalidate hreturns hbodyCompile hcompile hbind htxNormalized _
    (body_interface_body_fuel_eq selector fn returns bodyStmts)
    (body_interface_body_goal model fn bodyStmts hSupported.helperFuel tx initialWorld bindings _
      ⟨hSupported.normalizedFields, hSupported.noEvents, hSupported.noErrors,
        hSupported.noAdtTypes⟩
      (body_interface_extraFuel_lower selector fn returns bodyStmts) hbodyHelperGoal
      hfn'.body.helperSurfaceClosed (hfn'.body.helperFreeStepInterface hnoConflict)
      (hSupported.selectorFunctionParamNamesNodup hfn) hbind htxNormalized hcalldataSizeFits
      hbodyCompile)
    hcalldataSizeFits

theorem supported_function_correct_with_helper_proofs
    (model : CompilationModel) (selectors : List Nat) (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec) (selector : Nat) (returns : List ParamType) (bodyStmts : List YulStmt)
    (irFn : IRFunction) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat)) (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hclosed := (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed
  exact supported_function_correct_with_helper_proofs_goal model selectors hSupported
    hHelperProofs hvalidateInputs fn selector returns bodyStmts irFn tx initialWorld bindings hfn
    hvalidate hreturns hbodyCompile hcompile hbind htxNormalized
    (SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
      model _ hSupported.helperFuel _ fn.body hclosed)
    hcalldataSizeFits

/-- Support witness for a `fallback` or `receive` special entrypoint.
Special entrypoints take no ABI parameters, declare no returns, do not use the
`nonreentrant` transient-storage guard, use standard ABI decoding, and satisfy
the weakened body interface (`SupportedBodyInterfaceExceptMappingWrites`). -/
structure SupportedSpecialEntrypoint (spec : CompilationModel) (ep : FunctionSpec) where
  noParams : ep.params = []
  noReturnType : ep.returnType = none
  noReturns : ep.returns = []
  noNonReentrant : ep.nonReentrantLock = none
  standardAbi : ep.abiDecoding = .standard
  body : SupportedBodyInterfaceExceptMappingWrites spec ep

/-- Execute a compiled `IREntrypoint` (`fallback` or `receive`) on `initialState`,
mirroring the runtime Yul dispatcher's `callvalue()` check before running the
entrypoint body. -/
noncomputable def execIREntrypoint (ep : IREntrypoint) (tx : IRTransaction)
    (initialState : IRState) : IRResult :=
  if !ep.payable && tx.msgValue % Compiler.Constants.evmModulus != 0 then
    { success := false
      returnValue := none
      finalStorage := initialState.storage
      finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
      events := initialState.events }
  else
    execResultToIRResult initialState
      (execIRStmts (sizeOf ep.body + 1) initialState ep.body)

/-- Source-level execution of a `fallback` or `receive` special entrypoint,
including the `isPayable` guard on `tx.msgValue`. -/
def interpretSpecialEntrypointWithHelpers
    (model : CompilationModel) (helperFuel : Nat) (ep : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  if !ep.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0 then
    SourceSemantics.revertedResult model
      (SourceSemantics.withTransactionContext initialWorld tx)
  else
    SourceSemantics.interpretFunctionWithHelpers model helperFuel ep tx initialWorld

/-- Component inversion for `compileSpecialEntrypoint` when `nonReentrantLock = none`. -/
theorem compileSpecialEntrypoint_ok_body
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (ep : FunctionSpec) (irEp : IREntrypoint)
    (hnoLock : ep.nonReentrantLock = none)
    (hcompile :
      compileSpecialEntrypoint fields events errors [] .cancun [] ep = Except.ok irEp) :
    compileStmtList fields events errors .calldata [] false [] [] ep.body =
      Except.ok irEp.body ∧
    irEp.payable = ep.isPayable := by
  unfold compileSpecialEntrypoint at hcompile
  rw [hnoLock] at hcompile
  cases hbody : compileStmtList fields events errors .calldata [] false [] [] ep.body with
  | error err =>
      simp [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
        hbody, bind, Except.bind] at hcompile
  | ok bodyStmts =>
      simp only [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
        hbody, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hcompile
      subst hcompile
      exact ⟨rfl, rfl⟩

private theorem supported_special_entrypoint_body_correct_of_helperFree
    (model : CompilationModel) (ep : FunctionSpec) (helperFuel : Nat)
    (hnormalized : applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = []) (hnoAdtTypes : model.adtTypes = [])
    (hSupported : SupportedSpecialEntrypoint model ep)
    (hhelperFree : StmtListHelperFreeStepInterface model.fields (ep.params.map (·.name)) ep.body)
    (irEp : IREntrypoint) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hcompile : compileSpecialEntrypoint model.fields model.events model.errors [] .cancun [] ep = Except.ok irEp)
    (htxNormalized : TxContextNormalized tx) (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunctionWithHelpers model helperFuel ep tx initialWorld)
      (execResultToIRResult (FunctionBody.initialIRStateForTx model tx initialWorld)
        (execIRStmts (sizeOf irEp.body + 1)
          (FunctionBody.initialIRStateForTx model tx initialWorld) irEp.body)) := by
  obtain ⟨hbody, _⟩ := compileSpecialEntrypoint_ok_body
    model.fields model.events model.errors ep irEp hSupported.noNonReentrant hcompile
  have hbind : SourceSemantics.bindSupportedParams ep.params tx.args = some [] := by
    simp [hSupported.noParams, SourceSemantics.bindSupportedParams]
  have hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false
      (ep.params.map (·.name)) [] ep.body = Except.ok irEp.body := by
    simpa [hSupported.noParams] using hbody
  rcases body_interface_body_goal model ep irEp.body helperFuel tx initialWorld []
      (sizeOf irEp.body - irEp.body.length)
      ⟨hnormalized, hnoEvents, hnoErrors, hnoAdtTypes⟩ (Nat.le_refl _)
      (SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
        model _ helperFuel _ ep.body hSupported.body.helperSurfaceClosed)
      hSupported.body.helperSurfaceClosed hhelperFree
      (by simp [hSupported.noParams]) hbind htxNormalized hcalldataSizeFits hbodyCompile with
    ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hfuel : irEp.body.length + (sizeOf irEp.body - irEp.body.length) + 1 = sizeOf irEp.body + 1 := by
    have hle := yulStmtList_length_le_sizeOf irEp.body; omega
  have hstate : bodyInterfaceParamState model ep tx initialWorld [] =
      FunctionBody.initialIRStateForTx model tx initialWorld := by
    simp [bodyInterfaceParamState, prebindRawArgs, ParamLoading.applyBindingsToIRState, hSupported.noParams]
  rw [hfuel, hstate] at hbodyExec; rw [hbodyExec]
  exact bodyGoal_source_match model ep (habi := hSupported.standardAbi) helperFuel tx
    initialWorld [] sourceResult irExec hbind hsource hmatch

/-- Body-level semantic preservation for a `SupportedSpecialEntrypoint`:
the compiled entrypoint body `irEp.body` executed from `initialIRStateForTx`
matches `SourceSemantics.interpretFunctionWithHelpers`. -/
theorem supported_special_entrypoint_body_correct_stmtSafety
    (model : CompilationModel) (ep : FunctionSpec) (helperFuel : Nat)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hSupported : SupportedSpecialEntrypoint model ep)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : ∀ stmt ∈ ep.body, StmtMappingWriteSlotSafe model.fields stmt)
    (irEp : IREntrypoint) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hcompile :
      compileSpecialEntrypoint model.fields model.events model.errors [] .cancun [] ep =
        Except.ok irEp)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunctionWithHelpers model helperFuel ep tx initialWorld)
      (execResultToIRResult
        (FunctionBody.initialIRStateForTx model tx initialWorld)
        (execIRStmts (sizeOf irEp.body + 1)
          (FunctionBody.initialIRStateForTx model tx initialWorld) irEp.body)) :=
  supported_special_entrypoint_body_correct_of_helperFree model ep helperFuel hnormalized
    hnoEvents hnoErrors hnoAdtTypes hSupported
    (hSupported.body.helperFreeStepInterface_stmtSafety hnoConflict hsafety)
    irEp tx initialWorld hcompile htxNormalized hcalldataSizeFits

/-- Body-level semantic preservation for a `SupportedSpecialEntrypoint` under
contract-wide `SupportedStmtListMappingWriteSlotSafety`. -/
theorem supported_special_entrypoint_body_correct
    (model : CompilationModel) (ep : FunctionSpec) (helperFuel : Nat)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hSupported : SupportedSpecialEntrypoint model ep)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (irEp : IREntrypoint) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hcompile :
      compileSpecialEntrypoint model.fields model.events model.errors [] .cancun [] ep =
        Except.ok irEp)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunctionWithHelpers model helperFuel ep tx initialWorld)
      (execResultToIRResult
        (FunctionBody.initialIRStateForTx model tx initialWorld)
        (execIRStmts (sizeOf irEp.body + 1)
          (FunctionBody.initialIRStateForTx model tx initialWorld) irEp.body)) :=
  supported_special_entrypoint_body_correct_of_helperFree model ep helperFuel hnormalized
    hnoEvents hnoErrors hnoAdtTypes hSupported
    (hSupported.body.helperFreeStepInterface hnoConflict hsafety)
    irEp tx initialWorld hcompile htxNormalized hcalldataSizeFits

/-- Full entrypoint-level semantic preservation for a `SupportedSpecialEntrypoint`
(with statement-local mapping-write slot safety): `execIREntrypoint` matches
`interpretSpecialEntrypointWithHelpers`. -/
theorem supported_special_entrypoint_correct_stmtSafety
    (model : CompilationModel) (ep : FunctionSpec) (helperFuel : Nat)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hSupported : SupportedSpecialEntrypoint model ep)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : ∀ stmt ∈ ep.body, StmtMappingWriteSlotSafe model.fields stmt)
    (irEp : IREntrypoint) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hcompile :
      compileSpecialEntrypoint model.fields model.events model.errors [] .cancun [] ep =
        Except.ok irEp)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretSpecialEntrypointWithHelpers model helperFuel ep tx initialWorld)
      (execIREntrypoint irEp tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  obtain ⟨_, hpayable⟩ :=
    compileSpecialEntrypoint_ok_body model.fields model.events model.errors ep irEp
      hSupported.noNonReentrant hcompile
  unfold interpretSpecialEntrypointWithHelpers execIREntrypoint
  rw [hpayable]
  by_cases hguard : (!ep.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = true
  · rw [if_pos hguard, if_pos hguard]
    simp [FunctionBody.sourceResultMatchesIRResult, SourceSemantics.revertedResult,
      FunctionBody.initialIRStateForTx, FunctionBody.encodeStorage_withTransactionContext,
      FunctionBody.encodeEvents_withTransactionContext]
  · rw [if_neg hguard, if_neg hguard]
    exact supported_special_entrypoint_body_correct_stmtSafety model ep helperFuel hnormalized
      hnoEvents hnoErrors hnoAdtTypes hSupported hnoConflict hsafety irEp tx initialWorld
      hcompile htxNormalized hcalldataSizeFits

/-- Full entrypoint-level semantic preservation for a `SupportedSpecialEntrypoint`
under contract-wide `SupportedStmtListMappingWriteSlotSafety`. -/
theorem supported_special_entrypoint_correct
    (model : CompilationModel) (ep : FunctionSpec) (helperFuel : Nat)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hSupported : SupportedSpecialEntrypoint model ep)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (irEp : IREntrypoint) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hcompile :
      compileSpecialEntrypoint model.fields model.events model.errors [] .cancun [] ep =
        Except.ok irEp)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretSpecialEntrypointWithHelpers model helperFuel ep tx initialWorld)
      (execIREntrypoint irEp tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  obtain ⟨_, hpayable⟩ :=
    compileSpecialEntrypoint_ok_body model.fields model.events model.errors ep irEp
      hSupported.noNonReentrant hcompile
  unfold interpretSpecialEntrypointWithHelpers execIREntrypoint
  rw [hpayable]
  by_cases hguard : (!ep.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = true
  · rw [if_pos hguard, if_pos hguard]
    simp [FunctionBody.sourceResultMatchesIRResult, SourceSemantics.revertedResult,
      FunctionBody.initialIRStateForTx, FunctionBody.encodeStorage_withTransactionContext,
      FunctionBody.encodeEvents_withTransactionContext]
  · rw [if_neg hguard, if_neg hguard]
    exact supported_special_entrypoint_body_correct model ep helperFuel hnormalized
      hnoEvents hnoErrors hnoAdtTypes hSupported hnoConflict hsafety irEp tx initialWorld
      hcompile htxNormalized hcalldataSizeFits

private theorem constructor_body_generic_of_helperFree
    {model : CompilationModel} {ctor : ConstructorSpec}
    (hnormalized : applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hSupported : SupportedConstructor model ctor)
    (hhelperFree :
      StmtListHelperFreeStepInterface model.fields
        ((constructorAsFunctionSpec ctor).params.map (·.name)) ctor.body)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = []) :
    StmtListGenericWithHelpers model (SourceSemantics.effectiveFields model)
      (constructorBodyScope ctor.params) ctor.body := by
  have hscopeEq :
      (constructorAsFunctionSpec ctor).params.map (·.name) =
        constructorBodyScope ctor.params := by
    simp [constructorAsFunctionSpec, constructorBodyScope, constructorArgAliasNames,
      Function.comp_apply, List.map_map, Param.toIRParam]
  have hhelperFree' :
      StmtListHelperFreeStepInterface (SourceSemantics.effectiveFields model)
        (constructorBodyScope ctor.params) ctor.body := by
    rw [show SourceSemantics.effectiveFields model = model.fields by
      simp [SourceSemantics.effectiveFields, hnormalized], ← hscopeEq]
    exact hhelperFree
  exact stmtListGenericWithHelpers_of_helperFreeStepInterface_and_helperSurfaceClosed
    (spec := model) (hhelperFree := hhelperFree') (hnoEvents := hnoEvents)
    (hnoErrors := hnoErrors)
    (hsurface := by simpa [constructorAsFunctionSpec] using hSupported.body.helperSurfaceClosed)

/-- Constructor-body semantic preservation without the unused
`hfunctionNamesNodup` premise (statement-local mapping-write slot safety). -/
theorem supported_constructor_body_correct_stmtSafety
    (model : CompilationModel) (ctor : ConstructorSpec) (helperFuel : Nat)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hSupported : SupportedConstructor model ctor)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : ∀ stmt ∈ ctor.body, StmtMappingWriteSlotSafe model.fields stmt)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat)) (ctorBindings : List (String × Nat))
    (bodyStmts : List YulStmt)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .memory [] false
        (constructorBodyScope ctor.params) [] ctor.body = Except.ok bodyStmts)
    (hbind :
      SourceSemantics.bindSupportedParams ctor.params (tx.args.take ctor.params.length) =
        some bindings)
    (hconstructorBindings :
      SourceSemantics.constructorExecutionBindings ctor tx.args = some ctorBindings)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxConstructorCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretConstructorWithHelpers model helperFuel ctor tx initialWorld)
      (execResultToIRResult
        (FunctionBody.initialIRStateForTx model tx initialWorld)
        (execIRStmts
          (sizeOf bodyStmts + 1)
          (ParamLoading.applyBindingsToIRState
            (FunctionBody.initialIRStateForTx model tx initialWorld)
            ctorBindings)
          bodyStmts)) := by
  have haliases := constructor_body_aliases_of_executionBindings hbind hconstructorBindings
  exact constructor_body_result_of_matches
    (constructorTouchesUnsupportedRawCalldataSurface_eq_false hSupported) hconstructorBindings
    (constructor_body_stmtResult_matches hnoEvents hnoErrors
      (constructor_body_generic hnormalized hSupported hnoConflict hsafety hnoEvents hnoErrors)
      (constructor_body_scope_present hbind hconstructorBindings)
      (constructor_body_bindings_exact hSupported hbind haliases)
      (bindConstructorArgAliases_bounded haliases
        (FunctionBody.bindingsBounded_of_bindSupportedParams hbind))
      (constructor_body_runtime_matches ctorBindings htxNormalized hcalldataSizeFits)
      (constructor_body_compile_effective_of_memory hnormalized hSupported hbodyCompile))

/-- Constructor-body semantic preservation under contract-wide
`SupportedStmtListMappingWriteSlotSafety`. -/
theorem supported_constructor_body_correct
    (model : CompilationModel) (ctor : ConstructorSpec) (helperFuel : Nat)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hSupported : SupportedConstructor model ctor)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (hnoEvents : model.events = []) (hnoErrors : model.errors = [])
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat)) (ctorBindings : List (String × Nat))
    (bodyStmts : List YulStmt)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .memory [] false
        (constructorBodyScope ctor.params) [] ctor.body = Except.ok bodyStmts)
    (hbind :
      SourceSemantics.bindSupportedParams ctor.params (tx.args.take ctor.params.length) =
        some bindings)
    (hconstructorBindings :
      SourceSemantics.constructorExecutionBindings ctor tx.args = some ctorBindings)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxConstructorCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretConstructorWithHelpers model helperFuel ctor tx initialWorld)
      (execResultToIRResult
        (FunctionBody.initialIRStateForTx model tx initialWorld)
        (execIRStmts
          (sizeOf bodyStmts + 1)
          (ParamLoading.applyBindingsToIRState
            (FunctionBody.initialIRStateForTx model tx initialWorld)
            ctorBindings)
          bodyStmts)) := by
  have haliases := constructor_body_aliases_of_executionBindings hbind hconstructorBindings
  exact constructor_body_result_of_matches
    (constructorTouchesUnsupportedRawCalldataSurface_eq_false hSupported) hconstructorBindings
    (constructor_body_stmtResult_matches hnoEvents hnoErrors
      (constructor_body_generic_of_helperFree hnormalized hSupported
        (hSupported.body.helperFreeStepInterface hnoConflict hsafety) hnoEvents hnoErrors)
      (constructor_body_scope_present hbind hconstructorBindings)
      (constructor_body_bindings_exact hSupported hbind haliases)
      (bindConstructorArgAliases_bounded haliases
        (FunctionBody.bindingsBounded_of_bindSupportedParams hbind))
      (constructor_body_runtime_matches ctorBindings htxNormalized hcalldataSizeFits)
      (constructor_body_compile_effective_of_memory hnormalized hSupported hbodyCompile))
