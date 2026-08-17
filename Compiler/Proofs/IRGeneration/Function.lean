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
  | .revert _ =>
      { success := false
        returnValue := none
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events }

theorem compileFunctionSpec_ok_of_components
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (hvalidate : validateFunctionSpec spec = Except.ok ())
    (hreturns : functionReturns spec = Except.ok returns)
    (hbody :
      compileStmtList fields events errors .calldata [] false
        (spec.params.map (·.name)) [] spec.body = Except.ok bodyStmts) :
    compileFunctionSpec fields events errors [] selector spec =
      Except.ok (compiledFunctionIR selector spec returns bodyStmts) := by
  unfold CompilationModel.compileFunctionSpec
  rw [hvalidate, hreturns, FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hbody]
  rfl

/-- Populated-internal-table variant of `compileFunctionSpec_ok_of_components`.
The body equation and the enclosing function compilation must use the same
caller-supplied internal function table. -/
theorem compileFunctionSpec_ok_of_components_with_internals
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (internalFunctions : List FunctionSpec)
    (selector : Nat) (spec : FunctionSpec)
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
            (spec.params.map (·.name)) [] spec.body
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
            (spec.params.map (·.name)) [] spec.body
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
            (spec.params.map (·.name)) [] spec.body
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
            (spec.params.map (·.name)) [] spec.body internalFunctions
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
    (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (hcompile : compileFunctionSpec fields events errors [] selector spec = Except.ok irFn) :
    ∃ returns bodyStmts,
      validateFunctionSpec spec = Except.ok () ∧
      functionReturns spec = Except.ok returns ∧
      compileStmtList fields events errors .calldata [] false
        (spec.params.map (·.name)) [] spec.body = Except.ok bodyStmts ∧
      irFn = compiledFunctionIR selector spec returns bodyStmts := by
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

theorem exec_compiledFunctionIR_of_body
    (state : IRState) (selector : Nat) (spec : FunctionSpec)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (bindings : List (String × Nat)) (tailResult : IRExecResult)
    (hsupported : ∀ param ∈ spec.params, SupportedExternalParamType param.ty)
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
      execResultToIRResult state tailResult := by
  let preboundState := prebindRawArgs state spec.params
  have hbind' :
      SourceSemantics.bindSupportedParams spec.params preboundState.calldata = some bindings := by
    simpa [preboundState] using hbind
  have hcalldataSizeFits' :
      4 + preboundState.calldata.length * 32 < Compiler.Constants.evmModulus := by
    simpa [preboundState] using hcalldataSizeFits
  have hprefix :
      execIRStmts ((genParamLoads spec.params ++ bodyStmts).length + 1) preboundState
          (genParamLoads spec.params ++ bodyStmts) =
        execIRStmts (bodyStmts.length + 1)
          (ParamLoading.applyBindingsToIRState preboundState bindings)
          bodyStmts := by
    simpa [preboundState, List.length_append, Nat.add_assoc] using
      ParamLoading.exec_genParamLoads_supported_then
        (state := preboundState)
        (params := spec.params)
        (bindings := bindings)
        (rest := bodyStmts)
        hsupported hcalldataSizeFits' hbind'
  have hprefix' :
      execIRStmts ((genParamLoads spec.params).length + bodyStmts.length + 1) preboundState
          (genParamLoads spec.params ++ bodyStmts) =
        execIRStmts (bodyStmts.length + 1)
          (ParamLoading.applyBindingsToIRState preboundState bindings)
          bodyStmts := by
    simpa [List.length_append, Nat.add_assoc] using hprefix
  have hprebound :
      List.foldl (fun s x => s.setVar x.1.name x.2) state
        ((List.map Param.toIRParam spec.params).zip state.calldata) = preboundState := by
    rfl
  unfold Compiler.Proofs.YulGeneration.execIRFunctionFuel
  unfold Compiler.Proofs.YulGeneration.execIRStmtsFuel
  simp [compiledFunctionIR, execResultToIRResult]
  rw [hprebound]
  rw [hprefix', hbody]
  rfl

theorem exec_compiledFunctionIR_of_body_extraFuel
    (state : IRState) (selector : Nat) (spec : FunctionSpec)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (bindings : List (String × Nat)) (tailResult : IRExecResult)
    (extraFuel : Nat)
    (hsupported : ∀ param ∈ spec.params, SupportedExternalParamType param.ty)
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
  let preboundState := prebindRawArgs state spec.params
  have hbind' :
      SourceSemantics.bindSupportedParams spec.params preboundState.calldata = some bindings := by
    simpa [preboundState] using hbind
  have hcalldataSizeFits' :
      4 + preboundState.calldata.length * 32 < Compiler.Constants.evmModulus := by
    simpa [preboundState] using hcalldataSizeFits
  have hprefix :
      execIRStmts ((genParamLoads spec.params ++ bodyStmts).length + extraFuel + 1) preboundState
          (genParamLoads spec.params ++ bodyStmts) =
        execIRStmts (bodyStmts.length + extraFuel + 1)
          (ParamLoading.applyBindingsToIRState preboundState bindings)
          bodyStmts := by
    simpa [preboundState, List.length_append, Nat.add_assoc] using
      ParamLoading.exec_genParamLoads_supported_then_extraFuel
        (state := preboundState)
        (params := spec.params)
        (bindings := bindings)
        (rest := bodyStmts)
        (extraFuel := extraFuel)
        hsupported hcalldataSizeFits' hbind'
  have hprefix' :
      execIRStmts ((genParamLoads spec.params).length + bodyStmts.length + extraFuel + 1) preboundState
          (genParamLoads spec.params ++ bodyStmts) =
        execIRStmts (bodyStmts.length + extraFuel + 1)
          (ParamLoading.applyBindingsToIRState preboundState bindings)
          bodyStmts := by
    simpa [List.length_append, Nat.add_assoc] using hprefix
  have hprebound :
      List.foldl (fun s x => s.setVar x.1.name x.2) state
        ((List.map Param.toIRParam spec.params).zip state.calldata) = preboundState := by
    rfl
  unfold Compiler.Proofs.YulGeneration.execIRFunctionFuel
  unfold Compiler.Proofs.YulGeneration.execIRStmtsFuel
  simp [compiledFunctionIR, execResultToIRResult]
  rw [hprebound]
  rw [hprefix', hbody]
  rfl

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
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty)
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
    (hsupported : ∀ param ∈ spec.params, SupportedExternalParamType param.ty)
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
  let preboundState := prebindRawArgs state spec.params
  have hbind' :
      SourceSemantics.bindSupportedParams spec.params preboundState.calldata = some bindings := by
    simpa [preboundState] using hbind
  have hcalldataSizeFits' :
      4 + preboundState.calldata.length * 32 < Compiler.Constants.evmModulus := by
    simpa [preboundState] using hcalldataSizeFits
  have hprefix :
      execIRStmtsWithInternals runtimeContract
          ((genParamLoads spec.params).length + bodyStmts.length + extraFuel + 1)
          preboundState (genParamLoads spec.params ++ bodyStmts) =
        execIRStmtsWithInternals runtimeContract
          (bodyStmts.length + extraFuel + 1)
          (ParamLoading.applyBindingsToIRState preboundState bindings)
          bodyStmts := by
    simpa [preboundState, Nat.add_assoc] using
      exec_genParamLoads_supported_then_extraFuel_withInternals
        (runtimeContract := runtimeContract)
        (state := preboundState)
        (params := spec.params)
        (bindings := bindings)
        (rest := bodyStmts)
        (extraFuel := extraFuel)
        hsupported hcalldataSizeFits' hbind' hparamDisjoint
  calc
    execIRStmtsWithInternals runtimeContract
        ((genParamLoads spec.params ++ bodyStmts).length + extraFuel + 1)
        (prebindRawArgs state spec.params)
        (compiledFunctionIR selector spec returns bodyStmts).body
        =
      execIRStmtsWithInternals runtimeContract
        (bodyStmts.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState preboundState bindings)
        bodyStmts := by
          simpa [preboundState, compiledFunctionIR, List.length_append, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using hprefix
    _ = tailResult := hbody

theorem interpretFunction_eq_execResultToIRResult_of_body
    (model : CompilationModel) (fn : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult)
    (rollback : IRState) (irResult : IRExecResult)
    (bindings : List (String × Nat))
    (hbind :
      SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hnoEvents : model.events = [])
    (hsource :
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
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
          selector := tx.functionSelector }
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
  simp only [SourceSemantics.interpretFunction,
    SourceSemantics.bindExternalParams_eq_some_of_bindSupportedParams _ hbind]
  rw [hsourceWithEvents]; exact hpack

theorem interpretFunctionWithHelpers_eq_execResultToIRResultWithInternals_of_body
    (model : CompilationModel) (fn : FunctionSpec)
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
          selector := tx.functionSelector }
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
  cases sourceResult <;> cases irResult <;>
    simp [stmtResultMatchesIRExecWithInternals, FunctionBody.stmtResultMatchesIRExec] at hmatch
  · rcases hmatch with
      ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hblob, _, _, hcds, _, hret, hevents⟩
    simp [SourceSemantics.interpretFunctionWithHelpers, hbind, hsource,
      FunctionBody.sourceResultMatchesIRResult, FunctionBody.irResultOfExecResultWithInternals,
      SourceSemantics.successResult, SourceSemantics.encodeStorage,
      hstorage, hevents, hret]
  · rcases hmatch with
      ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hblob, _, _, hcds, _, hret, hevents⟩
    simp [SourceSemantics.interpretFunctionWithHelpers, hbind, hsource,
      FunctionBody.sourceResultMatchesIRResult, FunctionBody.irResultOfExecResultWithInternals,
      SourceSemantics.successResult, SourceSemantics.encodeStorage,
      hstorage, hevents]
  · rcases hmatch with
      ⟨hvalue, hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hblob, _, _, hcds, _, hret,
        hevents⟩
    simp [SourceSemantics.interpretFunctionWithHelpers, hbind, hsource,
      FunctionBody.sourceResultMatchesIRResult, FunctionBody.irResultOfExecResultWithInternals,
      SourceSemantics.successResult, SourceSemantics.encodeStorage,
      hvalue, hstorage, hevents]
  · simp [SourceSemantics.interpretFunctionWithHelpers, hbind, hsource,
      FunctionBody.sourceResultMatchesIRResult, FunctionBody.irResultOfExecResultWithInternals,
      SourceSemantics.revertedResult, hrollbackStorage, hrollbackEvents]

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
        selector := tx.functionSelector }
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
  have htxOriginEvm : tx.txOrigin < Compiler.Constants.evmModulus := by
    dsimp [Compiler.Constants.addressModulus, Compiler.Constants.evmModulus] at htxOrigin ⊢
    omega
  have htxOriginAddr : tx.txOrigin < Verity.Core.Address.modulus := by
    simpa [Verity.Core.Address.modulus, Compiler.Constants.addressModulus,
      Verity.Core.ADDRESS_MODULUS] using htxOrigin
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [FunctionBody.initialIRStateForTx, SourceSemantics.effectiveFields,
      SourceSemantics.encodeStorage] using
      (FunctionBody.encodeStorage_withTransactionContext model initialWorld tx).symm
  · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext,
      Verity.wordToAddress]
    symm
    calc
      tx.sender % Compiler.Constants.evmModulus % Verity.Core.Address.modulus
          = tx.sender % Verity.Core.Address.modulus := by
              rw [Nat.mod_eq_of_lt hsenderEvm]
      _ = tx.sender := Nat.mod_eq_of_lt hsenderAddr
  · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
    symm
    exact Nat.mod_eq_of_lt hmsgValue
  · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext,
      Verity.wordToAddress]
    symm
    calc
      tx.thisAddress % Compiler.Constants.evmModulus % Verity.Core.Address.modulus
          = tx.thisAddress % Verity.Core.Address.modulus := by
              rw [Nat.mod_eq_of_lt hthisEvm]
      _ = tx.thisAddress := Nat.mod_eq_of_lt hthisAddr
  · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
    symm
    exact Nat.mod_eq_of_lt htimestamp
  · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
    symm
    exact Nat.mod_eq_of_lt hnumber
  · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
    symm
    exact Nat.mod_eq_of_lt hchain
  · -- blobBaseFee
    simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
    symm
    exact Nat.mod_eq_of_lt hblob
  · -- txOrigin
    simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext, Verity.wordToAddress]
    symm
    calc
      tx.txOrigin % Compiler.Constants.evmModulus % Verity.Core.Address.modulus
          = tx.txOrigin % Verity.Core.Address.modulus := by
              rw [Nat.mod_eq_of_lt htxOriginEvm]
      _ = tx.txOrigin := Nat.mod_eq_of_lt htxOriginAddr
  · -- selector
    rfl
  · -- calldata
    rfl
  · -- calldataSize
    have : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
    simp only [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext,
      Verity.Core.Uint256.ofNat, this]
    exact Nat.mod_eq_of_lt hcalldataSizeFits
  · -- memory
    funext o
    simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
  · -- returnValue
    rfl
  · -- events
    change (FunctionBody.initialIRStateForTx model tx initialWorld).events =
      SourceSemantics.encodeEvents
        (SourceSemantics.withTransactionContext initialWorld tx).events
    have : (SourceSemantics.withTransactionContext initialWorld tx).events = initialWorld.events :=
      rfl
    rw [this]
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
        selector := tx.functionSelector }
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
      SourceSemantics.withConstructorTransactionContext, Verity.wordToAddress, hsenderWord, hthisWord,
      htxOriginWord, Nat.mod_eq_of_lt hmsgValue, Nat.mod_eq_of_lt htimestamp, Nat.mod_eq_of_lt hnumber,
      Nat.mod_eq_of_lt hchain, Nat.mod_eq_of_lt hblob]
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
        selector := tx.functionSelector }
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

theorem supported_function_body_correct_from_exact_state_core
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcore : FunctionBody.StmtListCompileCore (fn.params.map (·.name)) fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
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
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body = sourceResult ∧
      execIRStmts (bodyStmts.length + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
  have hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
    intro name hmem
    have hmemBindings : name ∈ bindings.map Prod.fst := by
      rw [ParamLoading.bindSupportedParams_names hbind]
      simpa using hmem
    exact lookupBinding?_some_of_mem bindings name hmemBindings
  have hbounded : FunctionBody.bindingsBounded bindings :=
    FunctionBody.bindingsBounded_of_bindSupportedParams hbind
  have hstateRuntime' :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] []
        .calldata [] false (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
  rcases FunctionBody.exec_compileStmtList_core
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings
                    selector := tx.functionSelector })
      (state := state)
      (scope := fn.params.map (·.name))
      (inScopeNames := fn.params.map (·.name))
      (stmts := fn.body)
      hcore hscope hstateBindings hbounded hstateRuntime' with
    ⟨bodyIR, hbodyCoreCompile, hcoreSem, _⟩
  have hbodyEq : bodyIR = bodyStmts := by
    rw [hbodyCompile'] at hbodyCoreCompile
    injection hbodyCoreCompile with hEq
    exact hEq.symm
  subst bodyIR
  refine ⟨_, _, rfl, rfl, hcoreSem⟩

theorem supported_function_body_correct_from_exact_state_core_extraFuel
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcore : FunctionBody.StmtListCompileCore (fn.params.map (·.name)) fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
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
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body = sourceResult ∧
      execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
  have hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
    intro name hmem
    have hmemBindings : name ∈ bindings.map Prod.fst := by
      rw [ParamLoading.bindSupportedParams_names hbind]
      simpa using hmem
    exact lookupBinding?_some_of_mem bindings name hmemBindings
  have hbounded : FunctionBody.bindingsBounded bindings :=
    FunctionBody.bindingsBounded_of_bindSupportedParams hbind
  have hstateRuntime' :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] []
        .calldata [] false (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
  rcases FunctionBody.exec_compileStmtList_core_extraFuel
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings
                    selector := tx.functionSelector })
      (state := state)
      (scope := fn.params.map (·.name))
      (inScopeNames := fn.params.map (·.name))
      (stmts := fn.body)
      extraFuel hcore hscope hstateBindings hbounded hstateRuntime' with
    ⟨bodyIR, hbodyCoreCompile, hcoreSem, _⟩
  have hbodyEq : bodyIR = bodyStmts := by
    rw [hbodyCompile'] at hbodyCoreCompile
    injection hbodyCoreCompile with hEq
    exact hEq.symm
  subst bodyIR
  refine ⟨_, _, rfl, rfl, hcoreSem⟩

theorem supported_function_body_correct_from_exact_state_terminal_core_extraFuel
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
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
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
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body = sourceResult ∧
      execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
  have hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
    intro name hmem
    have hmemBindings : name ∈ bindings.map Prod.fst := by
      rw [ParamLoading.bindSupportedParams_names hbind]
      simpa using hmem
    exact lookupBinding?_some_of_mem bindings name hmemBindings
  have hscopeExact :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (fn.params.map (·.name)) bindings state :=
    FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings
  have hbounded : FunctionBody.bindingsBounded bindings :=
    FunctionBody.bindingsBounded_of_bindSupportedParams hbind
  have hstateRuntime' :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] []
        .calldata [] false (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
  let sizeSlack := extraFuel - (sizeOf bodyStmts - bodyStmts.length)
  rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings
                    selector := tx.functionSelector })
      (state := state)
      (scope := fn.params.map (·.name))
      (inScopeNames := fn.params.map (·.name))
      (stmts := fn.body)
      (extraFuel := sizeSlack)
      hterminal
      FunctionBody.scopeNamesIncluded_refl
      hscope
      hscopeExact
      hbounded
      hstateRuntime' with
    ⟨bodyIR, hbodyTerminalCompile, hterminalSem⟩
  have hbodyEq : bodyIR = bodyStmts := by
    rw [hbodyCompile'] at hbodyTerminalCompile
    injection hbodyTerminalCompile with hEq
    exact hEq.symm
  subst bodyIR
  have hfuel :
      sizeOf bodyStmts + sizeSlack + 1 =
        bodyStmts.length + extraFuel + 1 := by
    dsimp [sizeSlack]
    have hlenle : bodyStmts.length ≤ sizeOf bodyStmts :=
      yulStmtList_length_le_sizeOf bodyStmts
    omega
  refine ⟨_, _, rfl, rfl, ?_⟩
  simpa [hfuel, sizeSlack] using hterminalSem

private theorem firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs
    {spec : CompilationModel}
    {selectors : List Nat}
    (hvalidate : validateCompileInputs spec selectors = Except.ok ()) :
    firstFieldWriteSlotConflict
        (applySlotAliasRanges spec.fields spec.slotAliasRanges) = none := by
  exact validateCompileInputs_firstFieldWriteSlotConflict_eq_none hvalidate

theorem compileFunctionSpec_correct_of_body
    (model : CompilationModel)
    (selector : Nat) (fn : FunctionSpec) (irFn : IRFunction)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult) (irExec : IRExecResult)
    (bindings : List (String × Nat))
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hparamsSupported : ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hnoEvents : model.events = [])
    (hsource :
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body = sourceResult)
    (hbodyExec :
      execIRStmts (bodyStmts.length + 1)
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bodyStmts = irExec)
    (hmatch :
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads fn.params ++ bodyStmts).length + 1)
        irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  have hcompiled :=
    compileFunctionSpec_ok_of_components model.fields model.events model.errors
      selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled with hirFn
  have hrollbackStorage :
        initialState.storage = fun s =>
          Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
            (SourceSemantics.encodeStorage model
              (SourceSemantics.withTransactionContext initialWorld tx) s.toNat) := by
    funext s
    simp [initialState, FunctionBody.initialIRStateForTx,
      FunctionBody.encodeStorage_withTransactionContext]
  have hrollbackEvents :
      initialState.events =
        SourceSemantics.encodeEvents
          (SourceSemantics.withTransactionContext initialWorld tx).events := by
    simp [initialState, FunctionBody.initialIRStateForTx]
  have hsourceMatch :=
    interpretFunction_eq_execResultToIRResult_of_body
      (model := model) (fn := fn) (tx := tx) (initialWorld := initialWorld)
      (sourceResult := sourceResult) (rollback := initialState) (irResult := irExec)
      (bindings := bindings) hbind hnoEvents hsource hrollbackStorage hrollbackEvents hmatch
  have hcompiledExec :
      Compiler.Proofs.YulGeneration.execIRFunctionFuel
          ((genParamLoads fn.params ++ bodyStmts).length + 1)
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
        execResultToIRResult initialState irExec := by
    exact exec_compiledFunctionIR_of_body
      (state := initialState) (selector := selector) (spec := fn)
      (returns := returns) (bodyStmts := bodyStmts) (bindings := bindings)
      (tailResult := irExec) hparamsSupported hcalldataSizeFits hbind hbodyExec
  subst hirFn
  rw [hcompiledExec]
  simpa [initialState] using hsourceMatch

theorem compileFunctionSpec_correct_of_body_normalized_extraFuel
    (model : CompilationModel)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (selector : Nat) (fn : FunctionSpec) (irFn : IRFunction)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult) (irExec : IRExecResult)
    (bindings : List (String × Nat)) (extraFuel : Nat)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList
        (applySlotAliasRanges model.fields model.slotAliasRanges)
        model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec
        (applySlotAliasRanges model.fields model.slotAliasRanges)
        model.events model.errors [] selector fn = Except.ok irFn)
    (hparamsSupported : ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hnoEvents : model.events = [])
    (hsource :
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body = sourceResult)
    (hbodyExec :
      execIRStmts (bodyStmts.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bodyStmts = irExec)
    (hmatch :
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1)
        irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  have hbodyCompile' :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts := by
    simpa [hnormalized] using hbodyCompile
  have hcompile' :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn := by
    simpa [hnormalized] using hcompile
  have hcompiled :=
    compileFunctionSpec_ok_of_components model.fields model.events model.errors
      selector fn returns bodyStmts hvalidate hreturns hbodyCompile'
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile'] at hcompiled
    injection hcompiled with hirFn
  have hrollbackStorage :
        initialState.storage = fun s =>
          Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
            (SourceSemantics.encodeStorage model
              (SourceSemantics.withTransactionContext initialWorld tx) s.toNat) := by
    funext s
    simp [initialState, FunctionBody.initialIRStateForTx,
      FunctionBody.encodeStorage_withTransactionContext]
  have hrollbackEvents :
      initialState.events =
        SourceSemantics.encodeEvents
          (SourceSemantics.withTransactionContext initialWorld tx).events := by
    simp [initialState, FunctionBody.initialIRStateForTx]
  have hsourceMatch :=
    interpretFunction_eq_execResultToIRResult_of_body
      (model := model) (fn := fn) (tx := tx) (initialWorld := initialWorld)
      (sourceResult := sourceResult) (rollback := initialState) (irResult := irExec)
      (bindings := bindings) hbind hnoEvents hsource hrollbackStorage hrollbackEvents hmatch
  have hcompiledExec :
      Compiler.Proofs.YulGeneration.execIRFunctionFuel
          ((genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1)
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
        execResultToIRResult initialState irExec := by
    exact exec_compiledFunctionIR_of_body_extraFuel
      (state := initialState) (selector := selector) (spec := fn)
      (returns := returns) (bodyStmts := bodyStmts) (bindings := bindings)
      (tailResult := irExec) (extraFuel := extraFuel)
      hparamsSupported hcalldataSizeFits hbind hbodyExec
  subst hirFn
  rw [hcompiledExec]
  simpa [initialState] using hsourceMatch

theorem compileFunctionSpec_correct_of_body_supported_extraFuel
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (selector : Nat) (fn : FunctionSpec) (irFn : IRFunction)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult) (irExec : IRExecResult)
    (bindings : List (String × Nat)) (extraFuel : Nat)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList
        (applySlotAliasRanges model.fields model.slotAliasRanges)
        model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec
        (applySlotAliasRanges model.fields model.slotAliasRanges)
        model.events model.errors [] selector fn = Except.ok irFn)
    (hparamsSupported : ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hsource :
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body = sourceResult)
    (hbodyExec :
      execIRStmts (bodyStmts.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bodyStmts = irExec)
    (hmatch :
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1)
        irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact compileFunctionSpec_correct_of_body_normalized_extraFuel
    model
    hSupported.normalizedFields
    selector fn irFn returns bodyStmts tx initialWorld sourceResult irExec
    bindings extraFuel hvalidate hreturns hbodyCompile hcompile hparamsSupported
    hcalldataSizeFits hbind hSupported.noEvents hsource hbodyExec hmatch

theorem supported_function_correct
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec)
    (selector : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
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
      (SourceSemantics.interpretFunction model fn tx initialWorld)
    (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  classical
  let _ := hvalidateInputs
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  have hinitBindings :
      FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
    simpa [initialState] using
      FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
  have hparamNamesNodup :
      (fn.params.map (·.name)).Nodup :=
    hSupported.selectorFunctionParamNamesNodup hfn
  have hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) :=
    supported_function_param_state_exact
      initialState fn.params bindings hinitBindings hparamNamesNodup hbind
  have hpreboundRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        (prebindRawArgs initialState fn.params) := by
    simpa [initialState] using
      runtimeStateMatchesIR_prebindRawArgs
        (state := initialState)
        (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
        (fields := SourceSemantics.effectiveFields model)
        (params := fn.params)
        (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized
          hcalldataSizeFits)
  have hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) :=
    runtimeStateMatchesIR_applyBindingsToIRState
      (state := prebindRawArgs initialState fn.params)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
      (fields := SourceSemantics.effectiveFields model)
      (bindings := bindings)
      hpreboundRuntime
  have hbodyStateBindings := hstateBindings
  have hbodyStateRuntime := hstateRuntime
  by_cases hcore : FunctionBody.StmtListCompileCore (fn.params.map (·.name)) fn.body
  · let extraFuel := sizeOf irFn.body - irFn.body.length
    have hbodyCorrect :
        ∃ sourceResult irExec,
          SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
            { world := SourceSemantics.withTransactionContext initialWorld tx
              bindings := bindings
              selector := tx.functionSelector }
            fn.body = sourceResult ∧
          execIRStmts (bodyStmts.length + extraFuel + 1)
            (ParamLoading.applyBindingsToIRState
              (prebindRawArgs initialState fn.params) bindings)
            bodyStmts = irExec ∧
          FunctionBody.stmtResultMatchesIRExec
            (SourceSemantics.effectiveFields model) sourceResult irExec := by
      exact supported_function_body_correct_from_exact_state_core_extraFuel
        (model := model)
        (fn := fn)
        (bodyStmts := bodyStmts)
        (tx := tx)
        (initialWorld := initialWorld)
        (state := ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings)
        (bindings := bindings)
        (extraFuel := extraFuel)
        (hnormalized := by
          simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
        (hnoEvents := hSupported.noEvents)
        (hnoErrors := hSupported.noErrors)
        hbind hcore hbodyCompile hbodyStateRuntime hbodyStateBindings
    rcases hbodyCorrect with
      ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
    have hfuel :=
      compileFunctionSpec_correct_of_body_supported_extraFuel
        (model := model)
        (selectors := selectors)
        (hSupported := hSupported)
        (selector := selector)
        (fn := fn)
        (irFn := irFn)
        (returns := returns)
        (bodyStmts := bodyStmts)
        (tx := tx)
        (initialWorld := initialWorld)
        (sourceResult := sourceResult)
        (irExec := irExec)
        (bindings := bindings)
        (extraFuel := extraFuel)
        hvalidate hreturns
        (by simpa [hSupported.normalizedFields] using hbodyCompile)
        (by simpa [hSupported.normalizedFields] using hcompile)
        (hSupported.selectorFunctionParamsSupported hfn)
        hcalldataSizeFits hbind hsource hbodyExec hmatch
    have hcompiled :=
      compileFunctionSpec_ok_of_components model.fields model.events model.errors
        selector fn returns bodyStmts hvalidate hreturns hbodyCompile
    have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
      rw [hcompile] at hcompiled
      injection hcompiled
    subst hirFn
    have hbodyFuel :
        (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
          sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
      have hlenle :
          (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
            sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
        exact Nat.le_of_add_le_add_right
          (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
      dsimp [extraFuel]
      simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
    have hfuelEq' :
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel)) =
          1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by
      have hbodyFuel' :
          (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
            sizeOf (genParamLoads fn.params ++ bodyStmts) := by
        simpa [compiledFunctionIR] using hbodyFuel
      calc
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel))
            = ((genParamLoads fn.params ++ bodyStmts).length + extraFuel) + 1 := by
                simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = sizeOf (genParamLoads fn.params ++ bodyStmts) + 1 := by rw [hbodyFuel']
        _ = 1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by omega
    have hadequacy :
        Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
          execIRFunction (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState := by
      simpa [Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal] using
        (Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState)
    have hfuel' :
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState) := by
      simpa [compiledFunctionIR, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        hfuelEq'] using hfuel
    simpa [hadequacy] using hfuel'
  · let extraFuel := sizeOf irFn.body - irFn.body.length
    have hbodyExtraFuelLower :
        sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
      have hcompiled :=
        compileFunctionSpec_ok_of_components model.fields model.events model.errors
          selector fn returns bodyStmts hvalidate hreturns hbodyCompile
      have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
        rw [hcompile] at hcompiled
        injection hcompiled
      subst hirFn
      dsimp [extraFuel]
      simpa [compiledFunctionIR] using
        yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts
    have hsupportedFn := hSupported.supportedFunctionOfSelectorDispatched hfn
    have hbodyHelperGoal :
        SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
          model
          (SourceSemantics.effectiveFields model)
          hSupported.helperFuel
          { world := SourceSemantics.withTransactionContext initialWorld tx
            bindings := bindings
            selector := tx.functionSelector }
          fn.body :=
      SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (fuel := hSupported.helperFuel)
        (state := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings
                    selector := tx.functionSelector })
        (stmts := fn.body)
        hsupportedFn.body.helperSurfaceClosed
    have hbodyCorrect :
        ∃ sourceResult irExec,
          SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
            { world := SourceSemantics.withTransactionContext initialWorld tx
              bindings := bindings
              selector := tx.functionSelector }
            fn.body = sourceResult ∧
          execIRStmts (bodyStmts.length + extraFuel + 1)
            (ParamLoading.applyBindingsToIRState
              (prebindRawArgs initialState fn.params) bindings)
            bodyStmts = irExec ∧
          FunctionBody.stmtResultMatchesIRExec
            (SourceSemantics.effectiveFields model) sourceResult irExec := by
      by_cases hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body
      · rcases supported_function_body_correct_from_exact_state_terminal_core_extraFuel
            (model := model)
            (fn := fn)
            (bodyStmts := bodyStmts)
            (tx := tx)
            (initialWorld := initialWorld)
            (state := ParamLoading.applyBindingsToIRState
              (prebindRawArgs initialState fn.params) bindings)
            (bindings := bindings)
            (extraFuel := extraFuel)
            (hextraFuel := hbodyExtraFuelLower)
            (hnormalized := by
              simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
            (hnoEvents := hSupported.noEvents)
            (hnoErrors := hSupported.noErrors)
            hbind hterminal hbodyCompile hbodyStateRuntime hbodyStateBindings with
          ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
        exact ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
      · have hscope :
            FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
          intro name hmem
          have hmemBindings : name ∈ bindings.map Prod.fst := by
            rw [ParamLoading.bindSupportedParams_names hbind]
            simpa using hmem
          exact lookupBinding?_some_of_mem bindings name hmemBindings
        have hbounded : FunctionBody.bindingsBounded bindings :=
          FunctionBody.bindingsBounded_of_bindSupportedParams hbind
        have hnoConflict :
            firstFieldWriteSlotConflict model.fields = none := by
          simpa [SourceSemantics.effectiveFields, hSupported.normalizedFields] using
            firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs
              (spec := model)
              (selectors := selectors)
              hvalidateInputs
        have hhelperFreeFields :
            StmtListHelperFreeStepInterface
              model.fields
              (fn.params.map (·.name))
              fn.body :=
          hsupportedFn.body.helperFreeStepInterface hnoConflict
        have hhelperFree :
            StmtListHelperFreeStepInterface
              (SourceSemantics.effectiveFields model)
              (fn.params.map (·.name))
              fn.body := by
          simpa [SourceSemantics.effectiveFields, hSupported.normalizedFields] using hhelperFreeFields
        rcases supported_function_body_correct_from_exact_state_generic_with_helpers
          model fn bodyStmts hSupported.helperFuel tx initialWorld
          (ParamLoading.applyBindingsToIRState
            (prebindRawArgs initialState fn.params) bindings)
          bindings extraFuel hbodyExtraFuelLower
          (by simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
          hSupported.noEvents
          hSupported.noErrors
          hSupported.noAdtTypes
          hsupportedFn.body.helperSurfaceClosed
          hhelperFree
          (by rw [hSupported.noAdtTypes]; exact hbodyCompile)
          hscope
          hbounded
          hbodyStateRuntime
          hbodyStateBindings with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
        refine ⟨sourceResult, irExec, ?_, hbodyExec, hmatch⟩
        have hsourceWithEvents :=
          hbodyHelperGoal.symm.trans hsource
        simpa [hSupported.noEvents] using hsourceWithEvents
    rcases hbodyCorrect with
      ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
    have hfuel :=
      compileFunctionSpec_correct_of_body_supported_extraFuel
        (model := model)
        (selectors := selectors)
        (hSupported := hSupported)
        (selector := selector)
        (fn := fn)
        (irFn := irFn)
        (returns := returns)
        (bodyStmts := bodyStmts)
        (tx := tx)
        (initialWorld := initialWorld)
        (sourceResult := sourceResult)
        (irExec := irExec)
        (bindings := bindings)
        (extraFuel := extraFuel)
        hvalidate hreturns
        (by simpa [hSupported.normalizedFields] using hbodyCompile)
        (by simpa [hSupported.normalizedFields] using hcompile)
        (hSupported.selectorFunctionParamsSupported hfn)
        hcalldataSizeFits hbind hsource hbodyExec hmatch
    have hcompiled :=
      compileFunctionSpec_ok_of_components model.fields model.events model.errors
        selector fn returns bodyStmts hvalidate hreturns hbodyCompile
    have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
      rw [hcompile] at hcompiled
      injection hcompiled
    subst hirFn
    have hbodyFuel :
        (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
          sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
      have hlenle :
          (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
            sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
        exact Nat.le_of_add_le_add_right
          (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
      dsimp [extraFuel]
      simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
    have hfuelEq' :
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel)) =
          1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by
      have hbodyFuel' :
          (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
            sizeOf (genParamLoads fn.params ++ bodyStmts) := by
        simpa [compiledFunctionIR] using hbodyFuel
      calc
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel))
            = ((genParamLoads fn.params ++ bodyStmts).length + extraFuel) + 1 := by
                simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = sizeOf (genParamLoads fn.params ++ bodyStmts) + 1 := by rw [hbodyFuel']
        _ = 1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by omega
    have hadequacy :
        Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
          execIRFunction (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState := by
      simpa [Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal] using
        (Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState)
    have hfuel' :
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState) := by
      simpa [compiledFunctionIR, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        hfuelEq'] using hfuel
    simpa [hadequacy] using hfuel'
theorem supported_function_correct_with_helper_proofs_body_goal
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (_hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (_hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec)
    (selector : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (_htxNormalized : TxContextNormalized tx)
    (extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersIRPreservationGoal
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  rcases hbodyCorrect with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
      selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled
  have hrollbackStorage :
        initialState.storage = fun s =>
          Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
            (SourceSemantics.encodeStorage model
              (SourceSemantics.withTransactionContext initialWorld tx) s.toNat) := by
    funext s
    simp [initialState, FunctionBody.initialIRStateForTx,
      FunctionBody.encodeStorage_withTransactionContext]
  have hrollbackEvents :
      initialState.events =
        SourceSemantics.encodeEvents
          (SourceSemantics.withTransactionContext initialWorld tx).events := by
    simp [initialState, FunctionBody.initialIRStateForTx]
  have hsourceMatch :
      FunctionBody.sourceResultMatchesIRResult
        (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
        (execResultToIRResult initialState irExec) := by
    have hpack :=
      FunctionBody.stmtResultToSourceResult_matches_irExecResult
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (initialWorld := SourceSemantics.withTransactionContext initialWorld tx)
        (rollback := initialState)
        (sourceResult := sourceResult)
        (irResult := irExec)
        hrollbackStorage hrollbackEvents rfl hmatch
    simp only [supportedSourceFunctionSemantics,
      SourceSemantics.interpretFunctionWithHelpers,
      SourceSemantics.bindExternalParams_eq_some_of_bindSupportedParams _ hbind]
    rw [hsource]
    exact hpack
  have hcompiledExec :
      Compiler.Proofs.YulGeneration.execIRFunctionFuel
          ((genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1)
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
        execResultToIRResult initialState irExec := by
    exact exec_compiledFunctionIR_of_body_extraFuel
      (state := initialState) (selector := selector) (spec := fn)
      (returns := returns) (bodyStmts := bodyStmts) (bindings := bindings)
      (tailResult := irExec) (extraFuel := extraFuel)
      (hSupported.selectorFunctionParamsSupported hfn)
      hcalldataSizeFits hbind hbodyExec
  subst hirFn
  have hcompiledBodyFuel' :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (genParamLoads fn.params ++ bodyStmts) := by
    simpa [compiledFunctionIR] using hcompiledBodyFuel
  have hfuelEq'' :
      extraFuel + (bodyStmts.length + (1 + (genParamLoads fn.params).length)) =
        1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by
    have hbodyFuel'' :
        (genParamLoads fn.params).length + bodyStmts.length + extraFuel =
          sizeOf (genParamLoads fn.params ++ bodyStmts) := by
      simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hcompiledBodyFuel'
    omega
  have hadequacy :
      Compiler.Proofs.YulGeneration.execIRFunctionFuel
          (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
        execIRFunction (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState := by
    simpa [Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal] using
      (Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
        (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState)
  have hfuel' :
      FunctionBody.sourceResultMatchesIRResult
        (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
        (Compiler.Proofs.YulGeneration.execIRFunctionFuel
          (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState) := by
    rw [← hcompiledExec] at hsourceMatch
    simpa [compiledFunctionIR, hfuelEq'', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using hsourceMatch
  simpa [hadequacy] using hfuel'
private theorem supported_function_correct_with_scalar_events_body_goal_source_match
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors)
    (fn : FunctionSpec) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (initialState : IRState) (irExec : IRExecResult) (sourceResult : SourceSemantics.StmtResult)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hsource :
      SourceSemantics.execStmtListWithHelpers model (SourceSemantics.effectiveFields model)
        hSupported.helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector } fn.body = sourceResult)
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
    SourceSemantics.interpretFunctionWithHelpers,
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
    (fn : FunctionSpec) (selector : Nat) (returns : List ParamType) (bodyStmts : List YulStmt)
    (irFn : IRFunction) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hvalidate : validateFunctionSpec fn = Except.ok ()) (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (extraFuel : Nat)
    (hcompiledBodyFuel : (genParamLoads fn.params ++ bodyStmts).length + extraFuel = sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
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
  have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors selector fn returns bodyStmts hvalidate hreturns hbodyCompile
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
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  rcases hbodyCorrect with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hsourceMatch :
      FunctionBody.sourceResultMatchesIRResult
        (supportedSourceFunctionSemanticsWithScalarEvents model selectors hSupported fn tx initialWorld)
        (execResultToIRResult initialState irExec) :=
    supported_function_correct_with_scalar_events_body_goal_source_match
      model selectors hSupported fn tx initialWorld bindings initialState irExec sourceResult
      hbind hsource hmatch rfl
  have hcompiledExec := supported_function_correct_with_scalar_events_body_goal_compiled_exec
    model selectors hSupported fn selector returns bodyStmts tx initialWorld bindings hfn hbind
    hcalldataSizeFits extraFuel irExec hbodyExec
  exact supported_function_correct_with_scalar_events_body_goal_fuel
    model selectors hSupported fn selector returns bodyStmts irFn tx initialWorld hvalidate hreturns
    hbodyCompile hcompile extraFuel hcompiledBodyFuel irExec hcompiledExec hsourceMatch
theorem supported_function_correct_with_helper_proofs_body_goal_and_helper_ir
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
    (fn : FunctionSpec)
    (selector : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx)
    (extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hbodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts)
    (hhelperIR :
      execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      execIRFunction irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld))
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacyBody :
      SupportedFunctionBodyWithHelpersIRPreservationGoal
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel :=
    supported_function_body_with_helpers_ir_goal_of_helper_ir_goal_callsDisjoint
      runtimeContract
      model fn bodyStmts hSupported.helperFuel tx initialWorld
      (ParamLoading.applyBindingsToIRState
        (prebindRawArgs
          (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
        bindings)
      bindings extraFuel
      hbodyCorrect
      hbodyDisjoint
  have hlegacy :=
    supported_function_correct_with_helper_proofs_body_goal
      model selectors hSupported hHelperProofs hvalidateInputs fn selector returns
      bodyStmts irFn tx initialWorld bindings hfn hvalidate hreturns hbodyCompile
      hcompile hbind htxNormalized extraFuel hcompiledBodyFuel hlegacyBody hcalldataSizeFits
  simpa [hhelperIR] using hlegacy

/-- Direct helper-aware function theorem for compiled bodies that already prove
the exact `execIRStmtsWithInternals` preservation goal. This is the function
level analogue of the legacy param-load/body execution bridge: the generated
ABI param-load prefix runs first under `WithInternals`, then execution continues
with the helper-aware compiled body. -/
theorem supported_function_correct_with_helper_proofs_body_goal_with_internals
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (_hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (_hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
    (fn : FunctionSpec)
    (selector : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (internalFunctions : List FunctionSpec)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body internalFunctions = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn
        (internalFunctions := internalFunctions) = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (_htxNormalized : TxContextNormalized tx)
    (irFuelSlack : Nat)
    (extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + irFuelSlack)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hparamDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract (genParamLoads fn.params))
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract irFuelSlack irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  rcases hbodyCorrect with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hcompiled := compileFunctionSpec_ok_of_components_with_internals
      model.fields model.events model.errors internalFunctions selector fn returns bodyStmts
      hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled
  have hrollbackStorage :
        initialState.storage = fun s =>
          Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
            (SourceSemantics.encodeStorage model
              (SourceSemantics.withTransactionContext initialWorld tx) s.toNat) := by
    funext s
    simp [initialState, FunctionBody.initialIRStateForTx,
      FunctionBody.encodeStorage_withTransactionContext]
  have hrollbackEvents :
      initialState.events =
        SourceSemantics.encodeEvents
          (SourceSemantics.withTransactionContext initialWorld tx).events := by
    simp [initialState, FunctionBody.initialIRStateForTx]
  have hsourceMatch :
      FunctionBody.sourceResultMatchesIRResult
        (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
        (FunctionBody.irResultOfExecResultWithInternals initialState irExec) := by
    have hpack :=
      interpretFunctionWithHelpers_eq_execResultToIRResultWithInternals_of_body
        (model := model)
        (fn := fn)
        (helperFuel := hSupported.helperFuel)
        (tx := tx)
        (initialWorld := initialWorld)
        (sourceResult := sourceResult)
        (rollback := initialState)
        (irResult := irExec)
        (bindings := bindings)
        hbind hsource hrollbackStorage hrollbackEvents hmatch
    simpa [supportedSourceFunctionSemantics] using hpack
  subst hirFn
  have hcompiledBodyFuel' :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (genParamLoads fn.params ++ bodyStmts) + irFuelSlack := by
    simpa [compiledFunctionIR] using hcompiledBodyFuel
  have hcompiledExec :
      execIRStmtsWithInternals runtimeContract
          (sizeOf (genParamLoads fn.params ++ bodyStmts) + irFuelSlack + 1)
          (prebindRawArgs initialState fn.params)
          (genParamLoads fn.params ++ bodyStmts) =
        irExec := by
    have hprefix :=
      exec_compiledFunctionIR_withInternals_of_body_extraFuel
        (runtimeContract := runtimeContract)
        (state := initialState)
        (selector := selector)
        (spec := fn)
        (returns := returns)
        (bodyStmts := bodyStmts)
        (bindings := bindings)
        (tailResult := irExec)
        (extraFuel := extraFuel)
        (hSupported.selectorFunctionParamsSupported hfn)
        hcalldataSizeFits hbind hparamDisjoint hbodyExec
    have hfuel :
        (genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1 =
          sizeOf (genParamLoads fn.params ++ bodyStmts) + irFuelSlack + 1 := by
      omega
    rw [← hfuel]
    simpa [compiledFunctionIR] using hprefix
  have hfunctionExec :
      execIRFunctionWithInternals runtimeContract irFuelSlack
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
        FunctionBody.irResultOfExecResultWithInternals initialState irExec := by
    have hstateWithParams :
        List.foldl (fun s x => s.setVar x.1.name x.2) initialState
            ((List.map Param.toIRParam fn.params).zip tx.args) =
          prebindRawArgs initialState fn.params := by
      simp [prebindRawArgs, initialState, FunctionBody.initialIRStateForTx]
    rw [execIRFunctionWithInternals]
    simp [compiledFunctionIR, hstateWithParams]
    rw [hcompiledExec]
    rfl
  simpa [initialState, hfunctionExec] using hsourceMatch

/-- Helper-rich Function consumer.  Unlike the legacy wrapper above, this
theorem is gated by `SupportedSpecWithHelpers`, whose function inventory may
carry a `SupportedHelperRichBodyFragment`; no `SupportedStmtList` or
helper-free body witness is required. -/
theorem supported_function_correct_with_helper_rich_support_body_goal_with_internals
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecWithHelpers model selectors)
    (_hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
    (fn : FunctionSpec)
    (selector : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (internalFunctions : List FunctionSpec)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body internalFunctions = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn
        (internalFunctions := internalFunctions) = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (_htxNormalized : TxContextNormalized tx)
    (irFuelSlack extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + irFuelSlack)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hparamDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract (genParamLoads fn.params))
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemanticsWithHelpers
        model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract irFuelSlack irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  rcases hbodyCorrect with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hcompiled := compileFunctionSpec_ok_of_components_with_internals
      model.fields model.events model.errors internalFunctions selector fn returns bodyStmts
      hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled
  have hrollbackStorage :
        initialState.storage = fun s =>
          Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
            (SourceSemantics.encodeStorage model
              (SourceSemantics.withTransactionContext initialWorld tx) s.toNat) := by
    funext s
    simp [initialState, FunctionBody.initialIRStateForTx,
      FunctionBody.encodeStorage_withTransactionContext]
  have hrollbackEvents :
      initialState.events =
        SourceSemantics.encodeEvents
          (SourceSemantics.withTransactionContext initialWorld tx).events := by
    simp [initialState, FunctionBody.initialIRStateForTx]
  have hsourceMatch :
      FunctionBody.sourceResultMatchesIRResult
        (supportedSourceFunctionSemanticsWithHelpers
          model selectors hSupported fn tx initialWorld)
        (FunctionBody.irResultOfExecResultWithInternals initialState irExec) := by
    simpa [supportedSourceFunctionSemanticsWithHelpers] using
      (interpretFunctionWithHelpers_eq_execResultToIRResultWithInternals_of_body
      (model := model) (fn := fn) (helperFuel := hSupported.helperFuel)
      (tx := tx) (initialWorld := initialWorld) (sourceResult := sourceResult)
      (rollback := initialState) (irResult := irExec) (bindings := bindings)
      hbind hsource hrollbackStorage hrollbackEvents hmatch)
  subst hirFn
  have hcompiledBodyFuel' :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (genParamLoads fn.params ++ bodyStmts) + irFuelSlack := by
    simpa [compiledFunctionIR] using hcompiledBodyFuel
  have hcompiledExec :
      execIRStmtsWithInternals runtimeContract
          (sizeOf (genParamLoads fn.params ++ bodyStmts) + irFuelSlack + 1)
          (prebindRawArgs initialState fn.params)
          (genParamLoads fn.params ++ bodyStmts) = irExec := by
    have hprefix :=
      exec_compiledFunctionIR_withInternals_of_body_extraFuel
        (runtimeContract := runtimeContract) (state := initialState)
        (selector := selector) (spec := fn) (returns := returns)
        (bodyStmts := bodyStmts) (bindings := bindings) (tailResult := irExec)
        (extraFuel := extraFuel)
        (hSupported.selectorFunctionParamsSupported hfn)
        hcalldataSizeFits hbind hparamDisjoint hbodyExec
    have hfuel :
        (genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1 =
          sizeOf (genParamLoads fn.params ++ bodyStmts) + irFuelSlack + 1 := by
      omega
    rw [← hfuel]
    simpa [compiledFunctionIR] using hprefix
  have hfunctionExec :
      execIRFunctionWithInternals runtimeContract irFuelSlack
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
        FunctionBody.irResultOfExecResultWithInternals initialState irExec := by
    have hstateWithParams :
        List.foldl (fun s x => s.setVar x.1.name x.2) initialState
            ((List.map Param.toIRParam fn.params).zip tx.args) =
          prebindRawArgs initialState fn.params := by
      simp [prebindRawArgs, initialState, FunctionBody.initialIRStateForTx]
    rw [execIRFunctionWithInternals]
    simp [compiledFunctionIR, hstateWithParams]
    rw [hcompiledExec]
    rfl
  simpa [initialState, hfunctionExec] using hsourceMatch

/-- Structured exact helper-aware function/IR wrapper under compiled-body
disjointness. The exact helper-aware body theorem can now be reused all the way
up to function-level results without requiring callers to restate the
conservative-extension equality manually. -/
theorem supported_function_correct_with_helper_proofs_body_goal_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
    (fn : FunctionSpec)
    (selector : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx)
    (extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hfnBodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
      selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled
  have hbodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts := by
    subst hirFn
    simpa [compiledFunctionIR] using
      YulStmtListCallsDisjointFromInternalTable.of_append_prefix
        (contract := runtimeContract)
        (pre := genParamLoads fn.params)
        (suf := bodyStmts)
        hfnBodyDisjoint
  exact
    supported_function_correct_with_helper_proofs_body_goal_and_helper_ir
      model selectors hSupported hHelperProofs hvalidateInputs runtimeContract
      fn selector returns bodyStmts irFn tx initialWorld bindings hfn hvalidate
      hreturns hbodyCompile hcompile hbind htxNormalized extraFuel hcompiledBodyFuel hbodyCorrect
      hbodyDisjoint
      (execIRFunctionWithInternals_eq_execIRFunction_of_bodyCallsDisjoint
        runtimeContract
        irFn
        tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)
        hfnBodyDisjoint)
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
        selector := tx.functionSelector }
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
          selector := tx.functionSelector }
        (prebindRawArgs initialState fn.params) := by
    simpa [initialState] using
      runtimeStateMatchesIR_prebindRawArgs
        (state := initialState)
        (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx,
                      bindings := [],
                      selector := tx.functionSelector })
        (fields := SourceSemantics.effectiveFields model)
        (params := fn.params)
        (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized
          hcalldataSizeFits)
  exact runtimeStateMatchesIR_applyBindingsToIRState
    (state := prebindRawArgs initialState fn.params)
    (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx,
                  bindings := [],
                  selector := tx.functionSelector })
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

/-- Function-level bridge from helper-aware `compileFunctionSpec` facts to the
mixed `WithInternals` body consumer.

The compile fact is reconstructed in the `model.functions` helper world and is
then threaded directly into the split-interface body theorem introduced for the
mixed helper-IR path. This packages the state/binding plumbing that callers
otherwise had to rebuild before they could consume
`supported_function_body_correct_from_exact_state_generic_split_helper_steps_and_helper_ir_with_internals`.
-/
theorem supported_function_body_with_internals_goal_of_compileFunctionSpec_with_internals
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (fn : FunctionSpec)
    (selector : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors model.adtTypes
        selector fn .cancun model.functions = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hfuelPos : 0 < hSupported.helperFuel)
    (hhelperFree :
      StmtListHelperFreeStepInterfaceWithInternals
        runtimeContract model (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name)) fn.body)
    (hcall :
      StmtListDirectInternalHelperCallStepInterfaceWithInternals
        runtimeContract model (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name)) fn.body)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterfaceWithInternals
        runtimeContract model (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name)) fn.body)
    (hexpr :
      StmtListExprInternalHelperStepInterfaceWithInternals
        runtimeContract model (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name)) fn.body)
    (hstruct :
      StmtListStructuralInternalHelperStepInterfaceWithInternals
        runtimeContract model (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name)) fn.body)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterfaceWithInternals
        runtimeContract model (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name)) fn.body) :
    ∃ returns bodyStmts extraFuel,
      irFn = compiledFunctionIR selector fn returns bodyStmts ∧
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel := by
  classical
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  rcases FunctionShape.compileFunctionSpec_ok_components_with_internals
      model.fields model.events model.errors model.adtTypes model.functions
      selector fn irFn hcompile with
    ⟨returns, bodyStmts, _hvalidate, _hreturns, hbodyCompile, hirFn⟩
  have hirFnLocal : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    convert hirFn using 1 <;> rfl
  let extraFuel := sizeOf irFn.body - irFn.body.length
  have hbodyExtraFuelLower :
      sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
    dsimp [extraFuel]
    rw [hirFnLocal]
    simpa [compiledFunctionIR] using
      yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts
  have hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
    exact function_body_scopeNamesPresent_of_bindSupportedParams fn tx bindings hbind
  have hbounded : FunctionBody.bindingsBounded bindings :=
    FunctionBody.bindingsBounded_of_bindSupportedParams hbind
  have hbodyStateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) := by
    simpa [initialState] using
      function_body_state_runtime_of_bindSupportedParams
        model fn tx initialWorld bindings htxNormalized hcalldataSizeFits
  have hbodyStateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) := by
    simpa [initialState] using
      function_body_state_bindings_of_bindSupportedParams
        model selectors hSupported fn tx initialWorld bindings hfn hbind
  have hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings)
        bindings extraFuel :=
    supported_function_body_correct_from_exact_state_generic_split_helper_steps_and_helper_ir_with_internals
      runtimeContract model fn bodyStmts hSupported.helperFuel tx initialWorld
      (ParamLoading.applyBindingsToIRState
        (prebindRawArgs initialState fn.params) bindings)
      bindings extraFuel hbodyExtraFuelLower
      hfuelPos
      (by simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
      hSupported.noEvents
      hSupported.noErrors
      hSupported.noAdtTypes
      hhelperFree
      hcall
      hassign
      hexpr
      hstruct
      hresidual
      hbodyCompile
      hscope
      hbounded
      hbodyStateRuntime
      hbodyStateBindings
  exact ⟨returns, bodyStmts, extraFuel, hirFnLocal, hbodyCorrect⟩

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
    (hsupported : SupportedExternalParamType ty) :
    LegacyCompatibleExternalStmtList (genScalarLoad loadWord name ty offset) := by
  cases ty <;> simp [SupportedExternalParamType] at hsupported ⊢
  all_goals exact .let_ _ _ [] .nil

private theorem genParamLoadBodyFrom_scalar_legacy
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr) (headSize baseOffset : Nat) :
    ∀ (params : List Param) (headOffset : Nat),
      (∀ param ∈ params, SupportedExternalParamType param.ty) →
        LegacyCompatibleExternalStmtList
          (genParamLoadBodyFrom loadWord sizeExpr headSize baseOffset params headOffset)
  | [], _, _ => .nil
  | param :: rest, headOffset, hsupported => by
      have htail := genParamLoadBodyFrom_scalar_legacy loadWord sizeExpr headSize
        baseOffset rest (headOffset + paramHeadSize param.ty)
        (by intro p hp; exact hsupported p (by simp [hp]))
      cases hty : param.ty <;> simp [SupportedExternalParamType, hty] at hsupported
      all_goals
        simpa [genParamLoadBodyFrom, genSingleParamLoad, genScalarLoad, hty]
          using legacyCompatibleExternalStmtList_append (.let_ _ _ [] .nil) htail

private theorem genParamLoads_scalar_legacy
    (params : List Param)
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty) :
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

/-- Generic compile-core statement lists discharge the per-head legacy-compatible
compiled-output interface consumed by the helper-aware whole-contract bridge.

The compiler scope is deliberately independent of the proof scope: core
statement heads do not use the scope to choose their emitted Yul constructors,
and the tail is threaded through the compiler's `stmtNextScope`. -/
theorem stmtListCompileCore_compiledLegacyCompatible
    (fields : List Field) :
    ∀ {proofScope compilerScope : List String} {stmts : List Stmt},
      FunctionBody.StmtListCompileCore proofScope stmts →
        StmtListCompiledLegacyCompatible fields compilerScope stmts
  | _, _, [], .nil => .nil
  | _, compilerScope, .letVar name value :: rest,
      .letVar _hvalue _hscope hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            bind, Except.bind] at hcompile
          split at hcompile <;> cases hcompile
          exact .let_ _ _ [] .nil)
        (stmtListCompileCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope (.letVar name value)) hrest)
  | _, compilerScope, .assignVar name value :: rest,
      .assignVar _hvalue _hscope hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            bind, Except.bind] at hcompile
          split at hcompile <;> cases hcompile
          exact .assign _ _ [] .nil)
        (stmtListCompileCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope (.assignVar name value)) hrest)
  | _, compilerScope, .require cond message :: rest,
      .require_ _hcond _hscope hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            bind, Except.bind] at hcompile
          split at hcompile <;> cases hcompile
          exact .if_ _ _ [] (revertWithMessage_legacyCompatible message) .nil)
        (stmtListCompileCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope (.require cond message)) hrest)
  | _, compilerScope, .return value :: rest,
      .return_ _hvalue _hscope hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            bind, Except.bind] at hcompile
          split at hcompile <;> cases hcompile
          exact .exprStmt _ _ (.exprStmt _ _ .nil))
        (stmtListCompileCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope (.return value)) hrest)
  | _, compilerScope, .stop :: rest, .stop hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hcompile
          cases hcompile
          exact .exprStmt _ _ .nil)
        (stmtListCompileCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope .stop) hrest)
  | _, compilerScope, .mstore offset value :: rest,
      .mstore _hoffset _hscopeOffset _hvalue _hscopeValue hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            bind, Except.bind] at hcompile
          split at hcompile <;> try contradiction
          split at hcompile <;> cases hcompile
          exact .exprStmt _ _ .nil)
        (stmtListCompileCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope (.mstore offset value)) hrest)
  | _, compilerScope, .tstore offset value :: rest,
      .tstore _hoffset _hscopeOffset _hvalue _hscopeValue hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            bind, Except.bind] at hcompile
          split at hcompile <;> try contradiction
          split at hcompile <;> cases hcompile
          exact .exprStmt _ _ .nil)
        (stmtListCompileCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope (.tstore offset value)) hrest)

/-- Terminal-core statement lists also discharge the per-head legacy-compatible
compiled-output interface.  The `ite` case uses the existing list bridge on the
terminal branches and compile-core tail. -/
theorem stmtListTerminalCore_compiledLegacyCompatible
    (fields : List Field) :
    ∀ {proofScope compilerScope : List String} {stmts : List Stmt},
      FunctionBody.StmtListTerminalCore proofScope stmts →
        StmtListCompiledLegacyCompatible fields compilerScope stmts
  | _, compilerScope, .letVar name value :: rest,
      .letVar _hvalue _hscope hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            bind, Except.bind] at hcompile
          split at hcompile <;> cases hcompile
          exact .let_ _ _ [] .nil)
        (stmtListTerminalCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope (.letVar name value)) hrest)
  | _, compilerScope, .assignVar name value :: rest,
      .assignVar _hvalue _hscope hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            bind, Except.bind] at hcompile
          split at hcompile <;> cases hcompile
          exact .assign _ _ [] .nil)
        (stmtListTerminalCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope (.assignVar name value)) hrest)
  | _, compilerScope, .require cond message :: rest,
      .require_ _hcond _hscope hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            bind, Except.bind] at hcompile
          split at hcompile <;> cases hcompile
          exact .if_ _ _ [] (revertWithMessage_legacyCompatible message) .nil)
        (stmtListTerminalCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope (.require cond message)) hrest)
  | _, compilerScope, .return value :: rest,
      .return_ _hvalue _hscope hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            bind, Except.bind] at hcompile
          split at hcompile <;> cases hcompile
          exact .exprStmt _ _ (.exprStmt _ _ .nil))
        (stmtListCompileCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope (.return value)) hrest)
  | _, compilerScope, .stop :: rest, .stop hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hcompile
          cases hcompile
          exact .exprStmt _ _ .nil)
        (stmtListCompileCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope .stop) hrest)
  | _, compilerScope, .mstore offset value :: rest,
      .mstore _hoffset _hscopeOffset _hvalue _hscopeValue hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            bind, Except.bind] at hcompile
          split at hcompile <;> try contradiction
          split at hcompile <;> cases hcompile
          exact .exprStmt _ _ .nil)
        (stmtListTerminalCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope (.mstore offset value)) hrest)
  | _, compilerScope, .tstore offset value :: rest,
      .tstore _hoffset _hscopeOffset _hvalue _hscopeValue hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            bind, Except.bind] at hcompile
          split at hcompile <;> try contradiction
          split at hcompile <;> cases hcompile
          exact .exprStmt _ _ .nil)
        (stmtListTerminalCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope (.tstore offset value)) hrest)
  | _, compilerScope, .ite cond thenBranch elseBranch :: rest,
      .ite _hcond _hscope hthen helse hrest =>
      .cons
        (fun compiledIR hcompile => by
          simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            bind, Except.bind] at hcompile
          split at hcompile <;> try contradiction
          rename_i condIR hcondIR
          split at hcompile <;> try contradiction
          rename_i thenIR hthenIR
          split at hcompile <;> try contradiction
          rename_i elseIR helseIR
          have hthenLegacy :
              LegacyCompatibleExternalStmtList thenIR :=
            compileStmtList_legacyCompatible_of_interface
              (stmtListTerminalCore_compiledLegacyCompatible fields
                (compilerScope := compilerScope) hthen)
              hthenIR
          have helseLegacy :
              LegacyCompatibleExternalStmtList elseIR :=
            compileStmtList_legacyCompatible_of_interface
              (stmtListTerminalCore_compiledLegacyCompatible fields
                (compilerScope := compilerScope) helse)
              helseIR
          by_cases hempty : elseBranch.isEmpty
          · simp [hempty] at hcompile
            cases hcompile
            exact .if_ condIR thenIR [] hthenLegacy .nil
          · simp [hempty] at hcompile
            cases hcompile
            exact .block
              [YulStmt.let_
                (pickFreshName "__ite_cond"
                  (compilerScope ++
                    (collectExprNames cond ++
                      (collectStmtListNames thenBranch ++ collectStmtListNames elseBranch))))
                condIR,
               YulStmt.if_
                (YulExpr.ident
                  (pickFreshName "__ite_cond"
                    (compilerScope ++
                      (collectExprNames cond ++
                        (collectStmtListNames thenBranch ++ collectStmtListNames elseBranch)))))
                thenIR,
               YulStmt.if_
                (YulExpr.call "iszero"
                  [YulExpr.ident
                    (pickFreshName "__ite_cond"
                      (compilerScope ++
                        (collectExprNames cond ++
                          (collectStmtListNames thenBranch ++ collectStmtListNames elseBranch))))])
                elseIR]
              []
              (.let_ _ _ _
                (.if_ _ _ _
                  hthenLegacy
                  (.if_ _ _ _ helseLegacy .nil)))
              .nil)
        (stmtListCompileCore_compiledLegacyCompatible fields
          (compilerScope := stmtNextScope compilerScope (.ite cond thenBranch elseBranch)) hrest)

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
    (fields : List Field) (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (hparams : ∀ param ∈ spec.params, SupportedExternalParamType param.ty)
    (hbodyInterface :
      StmtListCompiledLegacyCompatible fields (spec.params.map (·.name)) spec.body)
    (hcompile : compileFunctionSpec fields [] [] [] selector spec = Except.ok irFn) :
    LegacyCompatibleExternalStmtList irFn.body := by
  obtain ⟨returns, bodyStmts, _hvalidate, _hreturns, hbodyCompile, hirFn⟩ :=
    compileFunctionSpec_ok_components fields [] [] selector spec irFn hcompile
  subst hirFn
  simp only [compiledFunctionIR]
  exact legacyCompatibleExternalStmtList_append
    (genParamLoads_scalar_legacy spec.params hparams)
    (compileStmtList_legacyCompatible_of_interface hbodyInterface hbodyCompile)

/-- Function-level legacy-compatibility package for the generic compile-core
body fragment. This discharges #2080's per-statement legacy interface for
external functions whose source body is already in `StmtListCompileCore`. -/
theorem compileFunctionSpec_body_legacyCompatible_of_compileCore
    (fields : List Field) (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (hparams : ∀ param ∈ spec.params, SupportedExternalParamType param.ty)
    (hbodyCore :
      FunctionBody.StmtListCompileCore (spec.params.map (·.name)) spec.body)
    (hcompile : compileFunctionSpec fields [] [] [] selector spec = Except.ok irFn) :
    LegacyCompatibleExternalStmtList irFn.body :=
  compileFunctionSpec_body_legacyCompatible_of_interface
    fields selector spec irFn hparams
    (stmtListCompileCore_compiledLegacyCompatible fields
      (compilerScope := spec.params.map (·.name)) hbodyCore)
    hcompile

/-- Function-level legacy-compatibility package for the terminal-core body
fragment, including terminal `ite` bodies. -/
theorem compileFunctionSpec_body_legacyCompatible_of_terminalCore
    (fields : List Field) (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (hparams : ∀ param ∈ spec.params, SupportedExternalParamType param.ty)
    (hbodyTerminal :
      FunctionBody.StmtListTerminalCore (spec.params.map (·.name)) spec.body)
    (hcompile : compileFunctionSpec fields [] [] [] selector spec = Except.ok irFn) :
    LegacyCompatibleExternalStmtList irFn.body :=
  compileFunctionSpec_body_legacyCompatible_of_interface
    fields selector spec irFn hparams
    (stmtListTerminalCore_compiledLegacyCompatible fields
      (compilerScope := spec.params.map (·.name)) hbodyTerminal)
    hcompile

/-- Disjointness of a single scalar param-load (with the `calldataload` word
loader used by `genParamLoads`) from a runtime contract's internal-function
table. Every EVM/Yul builtin emitted by `genScalarLoad`
(`calldataload`, `and`, `signextend`, `iszero`) is assumed absent from the table; the
generated statement introduces no other calls. -/
private theorem genScalarLoad_calldataload_callsDisjoint
    (runtimeContract : IRContract) (name : String) (ty : ParamType) (offset : Nat)
    (hsupported : SupportedExternalParamType ty)
    (hcd : findInternalFunction? runtimeContract "calldataload" = none)
    (hand : findInternalFunction? runtimeContract "and" = none)
    (hsignextend : findInternalFunction? runtimeContract "signextend" = none)
    (hiszero : findInternalFunction? runtimeContract "iszero" = none) :
    YulStmtListCallsDisjointFromInternalTable runtimeContract
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty offset) := by
  have hload : yulExprCallsDisjointFromInternalTable runtimeContract
      (YulExpr.call "calldataload" [YulExpr.lit offset]) := by
    simp only [yulExprCallsDisjointFromInternalTable]
    refine ⟨hcd, ?_⟩
    intro arg harg; simp only [List.mem_singleton] at harg
    subst harg
    simp only [yulExprCallsDisjointFromInternalTable]
  cases ty <;> simp only [SupportedExternalParamType] at hsupported ⊢
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

/-- Disjointness of the whole param-load body (the recursive `genSingleParamLoad`
sequence used by `genParamLoads`) from a runtime contract's internal-function
table, given the three scalar-load builtins are absent. Recurses over the
supported scalar params, appending per-param disjointness. -/
private theorem genParamLoadBodyFrom_calldataload_callsDisjoint
    (runtimeContract : IRContract)
    (hcd : findInternalFunction? runtimeContract "calldataload" = none)
    (hand : findInternalFunction? runtimeContract "and" = none)
    (hsignextend : findInternalFunction? runtimeContract "signextend" = none)
    (hiszero : findInternalFunction? runtimeContract "iszero" = none)
    (sizeExpr : YulExpr) (headSize baseOffset : Nat) :
    ∀ (params : List Param) (headOffset : Nat),
      (∀ param ∈ params, SupportedExternalParamType param.ty) →
        YulStmtListCallsDisjointFromInternalTable runtimeContract
          (genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
            sizeExpr headSize baseOffset params headOffset)
  | [], _, _ => .nil
  | param :: rest, headOffset, hsupported => by
      have htail := genParamLoadBodyFrom_calldataload_callsDisjoint runtimeContract
        hcd hand hsignextend hiszero sizeExpr headSize baseOffset rest
        (headOffset + paramHeadSize param.ty)
        (by intro p hp; exact hsupported p (by simp [hp]))
      have hhead_sup : SupportedExternalParamType param.ty := hsupported param (by simp)
      have hhead := genScalarLoad_calldataload_callsDisjoint runtimeContract
        param.name param.ty headOffset hhead_sup hcd hand hsignextend hiszero
      cases hty : param.ty <;>
        simp only [SupportedExternalParamType, hty] at hhead_sup <;>
        simpa only [genParamLoadBodyFrom, genSingleParamLoad, hty]
          using yulStmtListCallsDisjoint_append hhead htail

/-- Disjointness of the full `genParamLoads` output (min-input-size guard plus
the param-load body) from a runtime contract's internal-function table, given
that none of the seven EVM/Yul builtins it emits (`calldataload`, `calldatasize`,
`lt`, `revert`, `and`, `signextend`, `iszero`) collide with an internal helper. -/
private theorem genParamLoads_callsDisjoint_of_builtins
    (runtimeContract : IRContract) (params : List Param)
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty)
    (hcd : findInternalFunction? runtimeContract "calldataload" = none)
    (hcdsize : findInternalFunction? runtimeContract "calldatasize" = none)
    (hlt : findInternalFunction? runtimeContract "lt" = none)
    (hrevert : findInternalFunction? runtimeContract "revert" = none)
    (hand : findInternalFunction? runtimeContract "and" = none)
    (hsignextend : findInternalFunction? runtimeContract "signextend" = none)
    (hiszero : findInternalFunction? runtimeContract "iszero" = none) :
    YulStmtListCallsDisjointFromInternalTable runtimeContract (genParamLoads params) := by
  have hbody := genParamLoadBodyFrom_calldataload_callsDisjoint runtimeContract
    hcd hand hsignextend hiszero (YulExpr.call "calldatasize" [])
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
`checked_`-, or `panic_error_`-prefixed), while the seven builtins emitted by the
param-load prologue (`calldataload`, `calldatasize`, `lt`, `revert`, `and`,
`signextend`, `iszero`) are provably *not* reserved, so none of them can resolve to a helper.
This is the true seam that replaces the false "every helper is `internal_`-prefixed"
premise: real compiler helpers are not `internal_`-prefixed, but they *are*
reserved, so the invariant is dischargeable from actual compilation output. -/
theorem genParamLoads_callsDisjoint_of_reserved
    (runtimeContract : IRContract) (params : List Param)
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty)
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

/-- Package `genParamLoads` disjointness from the `internal_`-prefix naming
invariant, routed through the reserved-name seam
(`genParamLoads_callsDisjoint_of_reserved` +
`InternalTableNamesReserved_of_internalPrefixed`). Retained as the compiled-only
entry point; the populated-table path uses the reserved variant directly. -/
theorem genParamLoads_callsDisjoint_of_internalNamesPrefixed
    (runtimeContract : IRContract) (params : List Param)
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty)
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
      { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector }
      state := by
  subst hstate
  subst hinitialState
  have hpreboundRuntime :
      FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector }
        (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params) := by
    exact runtimeStateMatchesIR_prebindRawArgs
      (state := FunctionBody.initialIRStateForTx model tx initialWorld)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
      (fields := SourceSemantics.effectiveFields model) (params := fn.params)
      (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized hcalldataSizeFits)
  exact runtimeStateMatchesIR_applyBindingsToIRState
    (state := prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
    (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
    (fields := SourceSemantics.effectiveFields model) (bindings := bindings) hpreboundRuntime

private theorem supported_function_correct_with_scalar_events_body_extraFuelLower
    (model : CompilationModel) (fn : FunctionSpec) (selector : Nat) (returns : List ParamType)
    (bodyStmts : List YulStmt) (irFn : IRFunction)
    (hvalidate : validateFunctionSpec fn = Except.ok ()) (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile : compileStmtList model.fields model.events model.errors .calldata [] false (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (extraFuel : Nat) (hextraFuel : extraFuel = sizeOf irFn.body - irFn.body.length) :
    sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
  have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors selector fn returns bodyStmts hvalidate hreturns hbodyCompile
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
      { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector } state)
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
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  let state := ParamLoading.applyBindingsToIRState (prebindRawArgs initialState fn.params) bindings
  let extraFuel := sizeOf irFn.body - irFn.body.length
  have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled; injection hcompiled
  have hbodyExtraFuelLower : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel :=
    supported_function_correct_with_scalar_events_body_extraFuelLower
      model fn selector returns bodyStmts irFn hvalidate hreturns hbodyCompile hcompile extraFuel rfl
  have hinit : FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
    simpa [initialState] using FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
  have hstateRuntime : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model) { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector } state :=
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
  rcases compileFunctionSpec_ok_components model.fields model.events model.errors sel fn irFn
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
  | .literal _, _, _, _ => by simp [compileExprWithInternals]
  | .param _, _, _, _ => by simp [compileExprWithInternals]
  | .constructorArg _, _, _, _ => by simp [compileExprWithInternals]
  | .storage _, _, _, _ => by simp [compileExprWithInternals]
  | .storageAddr _, _, _, _ => by simp [compileExprWithInternals]
  | .mapping _ _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .mappingWord _ _ _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .mappingPackedWord _ _ _ _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .mapping2 _ _ _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .mapping2Word _ _ _ _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .mappingUint _ _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .mappingChain _ _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .structMember _ _ _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .structMember2 _ _ _ _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .caller, _, _, _ => by simp [compileExprWithInternals]
  | .contractAddress, _, _, _ => by simp [compileExprWithInternals]
  | .txOrigin, _, _, _ => by simp [compileExprWithInternals]
  | .chainid, _, _, _ => by simp [compileExprWithInternals]
  | .msgValue, _, _, _ => by simp [compileExprWithInternals]
  | .blockTimestamp, _, _, _ => by simp [compileExprWithInternals]
  | .blockNumber, _, _, _ => by simp [compileExprWithInternals]
  | .blobbasefee, _, _, _ => by simp [compileExprWithInternals]
  | .mload _, hcore, hcall, hraw => by
      simp only [exprTouchesUnsupportedCoreSurface] at hcore
      simp only [exprTouchesUnsupportedCallSurface] at hcall
      simp only [exprTouchesUnsupportedConstructorRawCalldataSurface] at hraw
      simp [compileExprWithInternals, compileExpr_constructor_mode_eq hcore hcall hraw]
  | .tload _, hcore, hcall, hraw => by
      simp only [exprTouchesUnsupportedCoreSurface] at hcore
      simp only [exprTouchesUnsupportedCallSurface] at hcall
      simp only [exprTouchesUnsupportedConstructorRawCalldataSurface] at hraw
      simp [compileExprWithInternals, compileExpr_constructor_mode_eq hcore hcall hraw]
  | .keccak256 offset size, hcore, hcall, hraw => by
      simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff] at hcore
      simp only [exprTouchesUnsupportedCallSurface, Bool.or_eq_false_iff] at hcall
      simp only [exprTouchesUnsupportedConstructorRawCalldataSurface,
        Bool.or_eq_false_iff] at hraw
      simp [compileExprWithInternals,
        compileExpr_constructor_mode_eq hcore.1 hcall.1 hraw.1,
        compileExpr_constructor_mode_eq hcore.2 hcall.2 hraw.2]
  | .call .., hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .staticcall .., hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .delegatecall .., hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .calldatasize, _, _, hraw => by simp [exprTouchesUnsupportedConstructorRawCalldataSurface] at hraw
  | .calldataload _, _, _, hraw => by simp [exprTouchesUnsupportedConstructorRawCalldataSurface] at hraw
  | .returndataSize, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .extcodesize _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .returndataOptionalBoolAt _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .localVar _, _, _, _ => by simp [compileExprWithInternals]
  | .externalCall _ _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .internalCall _ _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .arrayLength _, _, hcall, _ => by simp [exprTouchesUnsupportedCallSurface] at hcall
  | .arrayElement _ _, _, hcall, _ => by simp [exprTouchesUnsupportedCallSurface] at hcall
  | .storageArrayLength _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .storageArrayElement _ _, hcore, _, _ => by simp [exprTouchesUnsupportedCoreSurface] at hcore
  | .dynamicBytesEq _ _, _, hcall, _ => by simp [exprTouchesUnsupportedCallSurface] at hcall
  | .add a b, hcore, hcall, hraw
  | .sub a b, hcore, hcall, hraw
  | .mul a b, hcore, hcall, hraw
  | .div a b, hcore, hcall, hraw
  | .sdiv a b, hcore, hcall, hraw
  | .mod a b, hcore, hcall, hraw
  | .smod a b, hcore, hcall, hraw
  | .bitAnd a b, hcore, hcall, hraw
  | .bitOr a b, hcore, hcall, hraw
  | .bitXor a b, hcore, hcall, hraw
  | .shl a b, hcore, hcall, hraw
  | .shr a b, hcore, hcall, hraw
  | .sar a b, hcore, hcall, hraw
  | .byte a b, hcore, hcall, hraw
  | .signextend a b, hcore, hcall, hraw
  | .eq a b, hcore, hcall, hraw
  | .ge a b, hcore, hcall, hraw
  | .gt a b, hcore, hcall, hraw
  | .sgt a b, hcore, hcall, hraw
  | .lt a b, hcore, hcall, hraw
  | .slt a b, hcore, hcall, hraw
  | .le a b, hcore, hcall, hraw
  | .logicalAnd a b, hcore, hcall, hraw
  | .logicalOr a b, hcore, hcall, hraw
  | .ceilDiv a b, hcore, hcall, hraw
  | .wMulDown a b, hcore, hcall, hraw
  | .wDivUp a b, hcore, hcall, hraw
  | .min a b, hcore, hcall, hraw
  | .max a b, hcore, hcall, hraw => by
      simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff] at hcore
      simp only [exprTouchesUnsupportedCallSurface, Bool.or_eq_false_iff] at hcall
      simp only [exprTouchesUnsupportedConstructorRawCalldataSurface,
        Bool.or_eq_false_iff] at hraw
      rcases hcore with ⟨hcoreA, hcoreB⟩
      rcases hcall with ⟨hcallA, hcallB⟩
      rcases hraw with ⟨hrawA, hrawB⟩
      simp [compileExprWithInternals, compileExpr_constructor_mode_eq hcoreA hcallA hrawA,
        compileExpr_constructor_mode_eq hcoreB hcallB hrawB]
  | .bitNot a, hcore, hcall, hraw
  | .logicalNot a, hcore, hcall, hraw => by
      simp only [exprTouchesUnsupportedCoreSurface] at hcore
      simp only [exprTouchesUnsupportedCallSurface] at hcall
      simp only [exprTouchesUnsupportedConstructorRawCalldataSurface] at hraw
      simp [compileExprWithInternals, compileExpr_constructor_mode_eq hcore hcall hraw]
  | .mulDivDown a b c, hcore, hcall, hraw
  | .mulDivUp a b c, hcore, hcall, hraw
  | .ite a b c, hcore, hcall, hraw => by
      simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff,
        Bool.or_assoc] at hcore
      simp only [exprTouchesUnsupportedCallSurface, Bool.or_eq_false_iff,
        Bool.or_assoc] at hcall
      simp only [exprTouchesUnsupportedConstructorRawCalldataSurface,
        Bool.or_eq_false_iff, Bool.or_assoc] at hraw
      rcases hcore with ⟨hcoreA, hcoreB, hcoreC⟩
      rcases hcall with ⟨hcallA, hcallB, hcallC⟩
      rcases hraw with ⟨hrawA, hrawB, hrawC⟩
      simp [compileExprWithInternals, compileExpr_constructor_mode_eq hcoreA hcallA hrawA,
        compileExpr_constructor_mode_eq hcoreB hcallB hrawB,
        compileExpr_constructor_mode_eq hcoreC hcallC hrawC]

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
    cases stmt <;>
      try simp [stmtTouchesUnsupportedEffectSurface] at heffectsClosed <;>
      try simp [stmtTouchesUnsupportedCoreSurface] at hcoreClosed <;>
      try simp [stmtTouchesUnsupportedCallSurface] at hcallClosed <;>
      try simp [stmtTouchesUnsupportedConstructorRawCalldataSurface] at hrawClosed <;>
      simp_all [compileStmtWithFork,
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

/-- Constructor-body bridge for the currently proved statement fragment.
This proves the user-written constructor body after constructor arguments have
already been decoded into IR locals. The initcode wrapper that materializes
those locals from deploy-time bytecode is still outside the current proof
interpreter surface.

## Remaining bridge shape
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
theorem supported_constructor_body_correct_with_body_interface
    (model : CompilationModel)
    (ctor : ConstructorSpec)
    (helperFuel : Nat)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hfunctionNamesNodup : (model.functions.map (·.name)).Nodup)
    (hSupported : SupportedConstructor model ctor)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : ∀ stmt ∈ ctor.body, StmtMappingWriteSlotSafe model.fields stmt)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (ctorBindings : List (String × Nat))
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
    let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
    let ctorFn := constructorAsFunctionSpec ctor
    have hrawUnsupported :
        SourceSemantics.constructorTouchesUnsupportedRawCalldataSurface model ctor = false :=
      constructorTouchesUnsupportedRawCalldataSurface_eq_false hSupported
    have hconstructorAliases :
        SourceSemantics.bindConstructorArgAliases ctor.params tx.args bindings =
          some ctorBindings := by
      unfold SourceSemantics.constructorExecutionBindings at hconstructorBindings
      simpa [hbind] using hconstructorBindings
    have hbodyCompileCalldata :
        compileStmtList model.fields [] [] .calldata [] false
          (constructorBodyScope ctor.params) [] ctor.body = Except.ok bodyStmts := by
      have hmode :=
        compileStmtList_constructor_mode_eq' (fields := model.fields)
          (events := model.events) (errors := model.errors)
          (scope := constructorBodyScope ctor.params)
          (body := ctor.body)
          hSupported.body.effects.surfaceClosed
          hSupported.body.core.surfaceClosed
          (SupportedBodyCallInterface.surfaceClosed_exceptMappingWrites hSupported.body)
          hSupported.rawCalldataSurfaceClosed
      rw [hbodyCompile] at hmode
      exact hmode.symm
    have hbodyCompileEffective :
        compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
          (constructorBodyScope ctor.params) [] ctor.body = Except.ok bodyStmts := by
      simpa [SourceSemantics.effectiveFields, hnormalized] using hbodyCompileCalldata
    have hstateRuntime :
        FunctionBody.runtimeStateMatchesIR
            (SourceSemantics.effectiveFields model)
            { world := SourceSemantics.withTransactionContext initialWorld tx
              bindings := ctorBindings
              selector := tx.functionSelector }
          (ParamLoading.applyBindingsToIRState initialState ctorBindings) := by
      have hinitRuntime :
          FunctionBody.runtimeStateMatchesIR
            (SourceSemantics.effectiveFields model)
            { world := SourceSemantics.withTransactionContext initialWorld tx
              bindings := []
              selector := tx.functionSelector }
            initialState := by
        simpa [initialState] using
          initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized
            (txCalldataSizeFitsEvm_of_constructorCalldataSizeFitsEvm hcalldataSizeFits)
      simpa [FunctionBody.runtimeStateMatchesIR] using
        runtimeStateMatchesIR_applyBindingsToIRState
          (fields := SourceSemantics.effectiveFields model)
          (state := initialState)
          hinitRuntime ctorBindings
    have hstateBindings :
        FunctionBody.bindingsExactlyMatchIRVars ctorBindings
          (ParamLoading.applyBindingsToIRState initialState ctorBindings) := by
      have hctorBindingsNodup : (ctorBindings.map Prod.fst).Nodup :=
        bindConstructorArgAliases_names_nodup
          hconstructorAliases
          (ParamLoading.bindSupportedParams_names_nodup
            hSupported.params.namesNodup hbind)
      exact bindingsExactlyMatchIRVars_applyBindingsToIRState_self
        (state := initialState)
        (bindings := ctorBindings)
        (by simpa [initialState] using
          FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld)
        hctorBindingsNodup
    have hscope :
        FunctionBody.scopeNamesPresent (constructorBodyScope ctor.params) ctorBindings := by
      intro name hmem
      simp [constructorBodyScope, constructorArgAliasNames] at hmem
      rcases hmem with hmemAlias | hmemParam
      · rcases hmemAlias with ⟨idx, hidx, rfl⟩
        exact SourceSemantics.constructorExecutionBindings_argAlias_present
          hconstructorBindings hidx
      · have hdecodedPresent :
            ∃ value, SourceSemantics.lookupBinding? bindings name = some value := by
          have hmemBindings : name ∈ bindings.map Prod.fst := by
            rw [ParamLoading.bindSupportedParams_names hbind]
            simpa using hmemParam
          rcases lookupBinding?_some_of_mem bindings name hmemBindings with ⟨value, hvalue⟩
          exact ⟨value, by simpa [FunctionBody.lookupBinding?,
            SourceSemantics.lookupBinding?] using hvalue⟩
        exact SourceSemantics.bindConstructorArgAliasesFrom_preserves_lookup
          (by simpa [SourceSemantics.bindConstructorArgAliases] using hconstructorAliases)
          hdecodedPresent
    have hbounded : FunctionBody.bindingsBounded ctorBindings :=
      bindConstructorArgAliases_bounded hconstructorAliases
        (FunctionBody.bindingsBounded_of_bindSupportedParams hbind)
    have hhelperFree :
        StmtListHelperFreeStepInterface
          (SourceSemantics.effectiveFields model)
          (constructorBodyScope ctor.params)
          ctor.body := by
      have hscopeEq :
          (constructorAsFunctionSpec ctor).params.map (·.name) =
            constructorBodyScope ctor.params := by
        simp [constructorAsFunctionSpec, constructorBodyScope,
          constructorArgAliasNames, Function.comp_apply, List.map_map,
          Param.toIRParam]
      rw [show SourceSemantics.effectiveFields model = model.fields by
        simp [SourceSemantics.effectiveFields, hnormalized]]
      rw [← hscopeEq]
      exact hSupported.body.helperFreeStepInterface_stmtSafety hnoConflict hsafety
    have hgeneric :
        StmtListGenericWithHelpers model (SourceSemantics.effectiveFields model)
          (constructorBodyScope ctor.params) ctor.body :=
      stmtListGenericWithHelpers_of_helperFreeStepInterface_and_helperSurfaceClosed
        (spec := model)
        (hhelperFree := hhelperFree)
        (hnoEvents := hnoEvents)
        (hnoErrors := hnoErrors)
        (hsurface := by simpa [ctorFn, constructorAsFunctionSpec] using
          hSupported.body.helperSurfaceClosed)
    rcases exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (state := ParamLoading.applyBindingsToIRState initialState ctorBindings)
        (scope := constructorBodyScope ctor.params)
        (stmts := ctor.body)
        (helperFuel := helperFuel)
        (extraFuel := 0)
        hgeneric
        hscope
        (FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings)
        hbounded
        hnoEvents
        hnoErrors
        hstateRuntime with
      ⟨bodyIR, hcompileIR, hmatch⟩
    have hbodyIR : bodyIR = bodyStmts := by
      rw [hbodyCompileEffective] at hcompileIR
      injection hcompileIR with hEq
      exact hEq.symm
    subst bodyIR
    have hrollbackStorage :
          initialState.storage = fun s =>
            Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
              (SourceSemantics.encodeStorage model
                (SourceSemantics.withTransactionContext initialWorld tx) s.toNat) := by
      funext s
      simp [initialState, FunctionBody.initialIRStateForTx,
        FunctionBody.encodeStorage_withTransactionContext]
    have hrollbackEvents :
        initialState.events =
          SourceSemantics.encodeEvents
            (SourceSemantics.withTransactionContext initialWorld tx).events := by
      simp [initialState, FunctionBody.initialIRStateForTx,
        SourceSemantics.withTransactionContext]
    have hpack :=
      FunctionBody.stmtResultToSourceResult_matches_irExecResult
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (initialWorld := SourceSemantics.withTransactionContext initialWorld tx)
        (rollback := initialState)
        (sourceResult := SourceSemantics.execStmtListWithHelpers model
          (SourceSemantics.effectiveFields model) helperFuel
          { world := SourceSemantics.withTransactionContext initialWorld tx
            bindings := ctorBindings
            selector := tx.functionSelector }
          ctor.body)
        (irResult := execIRStmts (sizeOf bodyStmts + 1)
          (ParamLoading.applyBindingsToIRState initialState ctorBindings) bodyStmts)
        hrollbackStorage
        hrollbackEvents
        rfl
        hmatch
    rw [SourceSemantics.interpretConstructorWithHelpers, hrawUnsupported,
      hconstructorBindings]
    exact hpack


/-- Function-level Tier 2 bridge for bodies admitted by the alternate
singleton storage-write state interface. This keeps the theorem local to one
function: global normalization and no-event/no-error assumptions remain
explicit, while the body proof can now use the non-vacuous singleton
mapping-write step interfaces instead of contradiction. -/
theorem supported_function_correct_with_body_interface_except_mapping_writes
    (model : CompilationModel)
    (fn : FunctionSpec)
    (helperFuel : Nat)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hparams : SupportedParamProfile fn.params)
    (hBody : SupportedBodyInterfaceExceptMappingWrites model fn)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (selector : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
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
      (SourceSemantics.interpretFunctionWithHelpers model helperFuel fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  have hinitBindings :
      FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
    simpa [initialState] using
      FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
  have hparamNamesNodup :
      (fn.params.map (·.name)).Nodup :=
    hparams.namesNodup
  have hbodyStateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) := by
    have hpreboundRuntime :
        FunctionBody.runtimeStateMatchesIR
          (SourceSemantics.effectiveFields model)
          { world := SourceSemantics.withTransactionContext initialWorld tx
            bindings := []
            selector := tx.functionSelector }
          (prebindRawArgs initialState fn.params) := by
      simpa [initialState] using
        runtimeStateMatchesIR_prebindRawArgs
          (state := initialState)
          (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
          (fields := SourceSemantics.effectiveFields model)
          (params := fn.params)
          (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized hcalldataSizeFits)
    exact runtimeStateMatchesIR_applyBindingsToIRState
      (state := prebindRawArgs initialState fn.params)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
      (fields := SourceSemantics.effectiveFields model)
      (bindings := bindings)
      hpreboundRuntime
  have hbodyStateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) := by
    exact supported_function_param_state_exact
      initialState fn.params bindings hinitBindings hparamNamesNodup hbind
  have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
      selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled
  let extraFuel := sizeOf irFn.body - irFn.body.length
  have hbodyExtraFuelLower :
      sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
    subst hirFn
    dsimp [extraFuel]
    simpa [compiledFunctionIR] using
      yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts
  have hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
    subst hirFn
    dsimp [extraFuel]
    have hlenle :
        (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
          sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
      exact Nat.le_of_add_le_add_right
        (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
    simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
  have hbodyWithHelpers :
      SupportedFunctionBodyWithHelpersIRPreservationGoal
        model fn bodyStmts helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings)
        bindings extraFuel := by
    by_cases hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body
    · rcases supported_function_body_correct_from_exact_state_terminal_core_extraFuel
          (model := model)
          (fn := fn)
          (bodyStmts := bodyStmts)
          (tx := tx)
          (initialWorld := initialWorld)
          (state := ParamLoading.applyBindingsToIRState
            (prebindRawArgs initialState fn.params) bindings)
          (bindings := bindings)
          (extraFuel := extraFuel)
          (hextraFuel := hbodyExtraFuelLower)
          (hnormalized := by
            simpa [SourceSemantics.effectiveFields] using hnormalized)
          (hnoEvents := hnoEvents)
          (hnoErrors := hnoErrors)
          hbind
          hterminal
          hbodyCompile
          hbodyStateRuntime
          hbodyStateBindings with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
      refine ⟨sourceResult, irExec, ?_, hbodyExec, hmatch⟩
      have hhelperGoal :
          SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
            model
            (SourceSemantics.effectiveFields model)
            helperFuel
            { world := SourceSemantics.withTransactionContext initialWorld tx
              bindings := bindings
              selector := tx.functionSelector }
            fn.body :=
        SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
          (spec := model)
          (fields := SourceSemantics.effectiveFields model)
          (fuel := helperFuel)
          (state := { world := SourceSemantics.withTransactionContext initialWorld tx
                      bindings := bindings
                      selector := tx.functionSelector })
          (stmts := fn.body)
          hBody.helperSurfaceClosed
      have hsourceWithEvents :
          SourceSemantics.execStmtListWithEvents (SourceSemantics.effectiveFields model) model.events
            { world := SourceSemantics.withTransactionContext initialWorld tx
              bindings := bindings
              selector := tx.functionSelector }
            fn.body = sourceResult := by
        simpa [hnoEvents] using hsource
      simpa [SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal] using
        hhelperGoal.trans hsourceWithEvents
    · have hscope :
          FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
        intro name hmem
        have hmemBindings : name ∈ bindings.map Prod.fst := by
          rw [ParamLoading.bindSupportedParams_names hbind]
          simpa using hmem
        exact lookupBinding?_some_of_mem bindings name hmemBindings
      have hbounded : FunctionBody.bindingsBounded bindings :=
        FunctionBody.bindingsBounded_of_bindSupportedParams hbind
      have hhelperFree :
          StmtListHelperFreeStepInterface
            (SourceSemantics.effectiveFields model)
            (fn.params.map (·.name))
            fn.body := by
        simpa [SourceSemantics.effectiveFields, hnormalized] using
          hBody.helperFreeStepInterface hnoConflict hsafety
      exact supported_function_body_correct_from_exact_state_generic_with_helpers
        model fn bodyStmts helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings)
        bindings extraFuel hbodyExtraFuelLower
        (by simpa [SourceSemantics.effectiveFields] using hnormalized)
        hnoEvents
        hnoErrors
        hnoAdtTypes
        hBody.helperSurfaceClosed
        hhelperFree
        (by rw [hnoAdtTypes]; exact hbodyCompile)
        hscope
        hbounded
        hbodyStateRuntime
        hbodyStateBindings
  rcases hbodyWithHelpers with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hhelperGoal :
      SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
        model
        (SourceSemantics.effectiveFields model)
        helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body :=
    SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
      (spec := model)
      (fields := SourceSemantics.effectiveFields model)
      (fuel := helperFuel)
      (state := { world := SourceSemantics.withTransactionContext initialWorld tx
                  bindings := bindings
                  selector := tx.functionSelector })
      (stmts := fn.body)
      hBody.helperSurfaceClosed
  have hsourceLegacy :
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body = sourceResult := by
    have hsourceWithEvents :=
      hhelperGoal.symm.trans hsource
    simpa [hnoEvents] using hsourceWithEvents
  have hlegacy :
      FunctionBody.sourceResultMatchesIRResult
        (SourceSemantics.interpretFunction model fn tx initialWorld)
        (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    have hfuel :=
      compileFunctionSpec_correct_of_body_normalized_extraFuel
        model
        hnormalized
        selector fn irFn returns bodyStmts tx initialWorld sourceResult irExec
        bindings extraFuel hvalidate hreturns
        (by simpa [hnormalized] using hbodyCompile)
        (by simpa [hnormalized] using hcompile)
        hparams.supported
        hcalldataSizeFits
        hbind
        hnoEvents
        hsourceLegacy
        hbodyExec
        hmatch
    subst hirFn
    have hbodyFuel :
        (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
          sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
      have hlenle :
          (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
            sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
        exact Nat.le_of_add_le_add_right
          (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
      dsimp [extraFuel]
      simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
    have hfuelEq' :
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel)) =
          1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by
      have hbodyFuel' :
          (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
            sizeOf (genParamLoads fn.params ++ bodyStmts) := by
        simpa [compiledFunctionIR] using hbodyFuel
      calc
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel))
            = ((genParamLoads fn.params ++ bodyStmts).length + extraFuel) + 1 := by
                simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = sizeOf (genParamLoads fn.params ++ bodyStmts) + 1 := by rw [hbodyFuel']
        _ = 1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by omega
    have hadequacy :
        Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
          execIRFunction (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState := by
      simpa [Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal] using
        (Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState)
    have hfuel' :
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState) := by
      simpa [compiledFunctionIR, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        hfuelEq'] using hfuel
    simpa [hadequacy] using hfuel'
  simpa [SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
    model helperFuel fn tx initialWorld hBody.helperSurfaceClosed] using hlegacy

/-- Body-local variant of
`supported_function_correct_with_body_interface_except_mapping_writes`.
This keeps the alternate Tier 2 theorem usable for concrete contracts whose
mapping-write safety argument is only available for the statements that
actually occur in the current body. -/
theorem supported_function_correct_with_body_interface_except_mapping_writes_stmtSafety
    (model : CompilationModel)
    (fn : FunctionSpec)
    (helperFuel : Nat)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hparams : SupportedParamProfile fn.params)
    (hBody : SupportedBodyInterfaceExceptMappingWrites model fn)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : ∀ stmt ∈ fn.body, StmtMappingWriteSlotSafe model.fields stmt)
    (selector : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
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
      (SourceSemantics.interpretFunctionWithHelpers model helperFuel fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  have hinitBindings :
      FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
    simpa [initialState] using
      FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
  have hparamNamesNodup :
      (fn.params.map (·.name)).Nodup :=
    hparams.namesNodup
  have hbodyStateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) := by
    have hpreboundRuntime :
        FunctionBody.runtimeStateMatchesIR
          (SourceSemantics.effectiveFields model)
          { world := SourceSemantics.withTransactionContext initialWorld tx
            bindings := []
            selector := tx.functionSelector }
          (prebindRawArgs initialState fn.params) := by
      simpa [initialState] using
        runtimeStateMatchesIR_prebindRawArgs
          (state := initialState)
          (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
          (fields := SourceSemantics.effectiveFields model)
          (params := fn.params)
          (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized hcalldataSizeFits)
    exact runtimeStateMatchesIR_applyBindingsToIRState
      (state := prebindRawArgs initialState fn.params)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
      (fields := SourceSemantics.effectiveFields model)
      (bindings := bindings)
      hpreboundRuntime
  have hbodyStateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) := by
    exact supported_function_param_state_exact
      initialState fn.params bindings hinitBindings hparamNamesNodup hbind
  have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
      selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled
  let extraFuel := sizeOf irFn.body - irFn.body.length
  have hbodyExtraFuelLower :
      sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
    subst hirFn
    dsimp [extraFuel]
    simpa [compiledFunctionIR] using
      yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts
  have hbodyWithHelpers :
      SupportedFunctionBodyWithHelpersIRPreservationGoal
        model fn bodyStmts helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings)
        bindings extraFuel := by
    by_cases hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body
    · rcases supported_function_body_correct_from_exact_state_terminal_core_extraFuel
          (model := model)
          (fn := fn)
          (bodyStmts := bodyStmts)
          (tx := tx)
          (initialWorld := initialWorld)
          (state := ParamLoading.applyBindingsToIRState
            (prebindRawArgs initialState fn.params) bindings)
          (bindings := bindings)
          (extraFuel := extraFuel)
          (hextraFuel := hbodyExtraFuelLower)
          (hnormalized := by
            simpa [SourceSemantics.effectiveFields] using hnormalized)
          (hnoEvents := hnoEvents)
          (hnoErrors := hnoErrors)
          hbind
          hterminal
          hbodyCompile
          hbodyStateRuntime
          hbodyStateBindings with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
      refine ⟨sourceResult, irExec, ?_, hbodyExec, hmatch⟩
      have hhelperGoal :
          SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
            model
            (SourceSemantics.effectiveFields model)
            helperFuel
            { world := SourceSemantics.withTransactionContext initialWorld tx
              bindings := bindings
              selector := tx.functionSelector }
            fn.body :=
        SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
          (spec := model)
          (fields := SourceSemantics.effectiveFields model)
          (fuel := helperFuel)
          (state := { world := SourceSemantics.withTransactionContext initialWorld tx
                      bindings := bindings
                      selector := tx.functionSelector })
          (stmts := fn.body)
          hBody.helperSurfaceClosed
      have hsourceWithEvents :
          SourceSemantics.execStmtListWithEvents (SourceSemantics.effectiveFields model) model.events
            { world := SourceSemantics.withTransactionContext initialWorld tx
              bindings := bindings
              selector := tx.functionSelector }
            fn.body = sourceResult := by
        simpa [hnoEvents] using hsource
      simpa [SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal] using
        hhelperGoal.trans hsourceWithEvents
    · have hscope :
          FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
        intro name hmem
        have hmemBindings : name ∈ bindings.map Prod.fst := by
          rw [ParamLoading.bindSupportedParams_names hbind]
          simpa using hmem
        exact lookupBinding?_some_of_mem bindings name hmemBindings
      have hbounded : FunctionBody.bindingsBounded bindings :=
        FunctionBody.bindingsBounded_of_bindSupportedParams hbind
      have hhelperFree :
          StmtListHelperFreeStepInterface
            (SourceSemantics.effectiveFields model)
            (fn.params.map (·.name))
            fn.body := by
        simpa [SourceSemantics.effectiveFields, hnormalized] using
          hBody.helperFreeStepInterface_stmtSafety hnoConflict hsafety
      exact supported_function_body_correct_from_exact_state_generic_with_helpers
        model fn bodyStmts helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings)
        bindings extraFuel hbodyExtraFuelLower
        (by simpa [SourceSemantics.effectiveFields] using hnormalized)
        hnoEvents
        hnoErrors
        hnoAdtTypes
        hBody.helperSurfaceClosed
        hhelperFree
        (by rw [hnoAdtTypes]; exact hbodyCompile)
        hscope
        hbounded
        hbodyStateRuntime
        hbodyStateBindings
  rcases hbodyWithHelpers with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hhelperGoal :
      SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
        model
        (SourceSemantics.effectiveFields model)
        helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body :=
    SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
      (spec := model)
      (fields := SourceSemantics.effectiveFields model)
      (fuel := helperFuel)
      (state := { world := SourceSemantics.withTransactionContext initialWorld tx
                  bindings := bindings
                  selector := tx.functionSelector })
      (stmts := fn.body)
      hBody.helperSurfaceClosed
  have hsourceLegacy :
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body = sourceResult := by
    have hsourceWithEvents :=
      hhelperGoal.symm.trans hsource
    simpa [hnoEvents] using hsourceWithEvents
  have hlegacy :
      FunctionBody.sourceResultMatchesIRResult
        (SourceSemantics.interpretFunction model fn tx initialWorld)
        (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    have hfuel :=
      compileFunctionSpec_correct_of_body_normalized_extraFuel
        model
        hnormalized
        selector fn irFn returns bodyStmts tx initialWorld sourceResult irExec
        bindings extraFuel hvalidate hreturns
        (by simpa [hnormalized] using hbodyCompile)
        (by simpa [hnormalized] using hcompile)
        hparams.supported
        hcalldataSizeFits
        hbind
        hnoEvents
        hsourceLegacy
        hbodyExec
        hmatch
    subst hirFn
    have hbodyFuel :
        (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
          sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
      have hlenle :
          (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
            sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
        exact Nat.le_of_add_le_add_right
          (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
      dsimp [extraFuel]
      simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
    have hfuelEq' :
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel)) =
          1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by
      have hbodyFuel' :
          (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
            sizeOf (genParamLoads fn.params ++ bodyStmts) := by
        simpa [compiledFunctionIR] using hbodyFuel
      calc
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel))
            = ((genParamLoads fn.params ++ bodyStmts).length + extraFuel) + 1 := by
                simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = sizeOf (genParamLoads fn.params ++ bodyStmts) + 1 := by rw [hbodyFuel']
        _ = 1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by omega
    have hadequacy :
        Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
          execIRFunction (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState := by
      simpa [Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal] using
        (Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState)
    have hfuel' :
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState) := by
      simpa [compiledFunctionIR, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        hfuelEq'] using hfuel
    simpa [hadequacy] using hfuel'
  simpa [SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
    model helperFuel fn tx initialWorld hBody.helperSurfaceClosed] using hlegacy

/-- Function-level Tier 2 bridge from the alternate contract support witness.
This is the selector-dispatched analogue of `supported_function_correct`,
reusing the weakened body interface instead of the default fail-closed state
surface. -/
theorem supported_function_correct_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (fn : FunctionSpec)
    (selector : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rcases compileFunctionSpec_ok_components
      model.fields model.events model.errors selector fn irFn hcompileFn with
    ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
  subst hirFn
  have hcorrect :=
    supported_function_correct_with_body_interface_except_mapping_writes
      (model := model)
      (fn := fn)
      (helperFuel := hSupported.helperFuel)
      (hnormalized := hSupported.normalizedFields)
      (hnoEvents := hSupported.noEvents)
      (hnoErrors := hSupported.noErrors)
      (hnoAdtTypes := hSupported.noAdtTypes)
      (hparams := (hSupported.supportedFunctionOfSelectorDispatched hfn).params)
      (hBody := (hSupported.supportedFunctionOfSelectorDispatched hfn).body)
      (hnoConflict := hnoConflict)
      (hsafety := hsafety)
      (selector := selector)
      (returns := returns)
      (bodyStmts := bodyStmts)
      (irFn := compiledFunctionIR selector fn returns bodyStmts)
      (tx := tx)
      (initialWorld := initialWorld)
      (bindings := bindings)
      (hvalidate := hvalidate)
      (hreturns := hreturns)
      (hbodyCompile := hbodyCompile)
      (hcompile := by simpa using hcompileFn)
      (hbind := hbind)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
  simpa [SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
    model hSupported.helperFuel fn tx initialWorld
    (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed] using hcorrect

theorem supported_function_correct_except_mapping_writes_stmtSafety
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (fn : FunctionSpec)
    (selector : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : ∀ stmt ∈ fn.body, StmtMappingWriteSlotSafe model.fields stmt)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rcases compileFunctionSpec_ok_components
      model.fields model.events model.errors selector fn irFn hcompileFn with
    ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
  subst hirFn
  have hcorrect :=
    supported_function_correct_with_body_interface_except_mapping_writes_stmtSafety
      (model := model)
      (fn := fn)
      (helperFuel := hSupported.helperFuel)
      (hnormalized := hSupported.normalizedFields)
      (hnoEvents := hSupported.noEvents)
      (hnoErrors := hSupported.noErrors)
      (hnoAdtTypes := hSupported.noAdtTypes)
      (hparams := (hSupported.supportedFunctionOfSelectorDispatched hfn).params)
      (hBody := (hSupported.supportedFunctionOfSelectorDispatched hfn).body)
      (hnoConflict := hnoConflict)
      (hsafety := hsafety)
      (selector := selector)
      (returns := returns)
      (bodyStmts := bodyStmts)
      (irFn := compiledFunctionIR selector fn returns bodyStmts)
      (tx := tx)
      (initialWorld := initialWorld)
      (bindings := bindings)
      (hvalidate := hvalidate)
      (hreturns := hreturns)
      (hbodyCompile := hbodyCompile)
      (hcompile := by simpa using hcompileFn)
      (hbind := hbind)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
  simpa [SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
    model hSupported.helperFuel fn tx initialWorld
    (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed] using hcorrect

/-- Goal-based helper-proof-carrying variant of `supported_function_correct`.
This keeps the current helper-free source-side conservative-extension premise
available as a wrapper, but the exact future helper seam is now the direct
helper-aware body/IR goal exposed by
`supported_function_correct_with_helper_proofs_body_goal`. -/
theorem supported_function_correct_with_helper_proofs_goal
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec)
    (selector : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors [] selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (htxNormalized : TxContextNormalized tx)
    (hbodyHelperGoal :
      SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
        model
        (SourceSemantics.effectiveFields model)
        hSupported.helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  classical
  let _ := hvalidateInputs
  have hsupportedFn := hSupported.supportedFunctionOfSelectorDispatched hfn
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  have hinitBindings :
      FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
    simpa [initialState] using
      FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
  have hparamNamesNodup :
      (fn.params.map (·.name)).Nodup :=
    hSupported.selectorFunctionParamNamesNodup hfn
  have hbodyStateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) := by
    have hpreboundRuntime :
        FunctionBody.runtimeStateMatchesIR
          (SourceSemantics.effectiveFields model)
          { world := SourceSemantics.withTransactionContext initialWorld tx
            bindings := []
            selector := tx.functionSelector }
          (prebindRawArgs initialState fn.params) := by
      simpa [initialState] using
        runtimeStateMatchesIR_prebindRawArgs
          (state := initialState)
          (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
          (fields := SourceSemantics.effectiveFields model)
          (params := fn.params)
          (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized
            hcalldataSizeFits)
    exact runtimeStateMatchesIR_applyBindingsToIRState
      (state := prebindRawArgs initialState fn.params)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
      (fields := SourceSemantics.effectiveFields model)
      (bindings := bindings)
      hpreboundRuntime
  have hbodyStateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) := by
    exact supported_function_param_state_exact
      initialState fn.params bindings hinitBindings hparamNamesNodup hbind
  have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
      selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled
  let extraFuel := sizeOf irFn.body - irFn.body.length
  have hbodyExtraFuelLower :
      sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
    subst hirFn
    dsimp [extraFuel]
    simpa [compiledFunctionIR] using
      yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts
  have hbodyWithHelpers :
      SupportedFunctionBodyWithHelpersIRPreservationGoal
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings)
        bindings extraFuel := by
    by_cases hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body
    · rcases supported_function_body_correct_from_exact_state_terminal_core_extraFuel
          (model := model)
          (fn := fn)
          (bodyStmts := bodyStmts)
          (tx := tx)
          (initialWorld := initialWorld)
          (state := ParamLoading.applyBindingsToIRState
            (prebindRawArgs initialState fn.params) bindings)
          (bindings := bindings)
          (extraFuel := extraFuel)
          (hextraFuel := hbodyExtraFuelLower)
          (hnormalized := by
            simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
          (hnoEvents := hSupported.noEvents)
          (hnoErrors := hSupported.noErrors)
          hbind
          hterminal
          hbodyCompile
          hbodyStateRuntime
          hbodyStateBindings with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
      refine ⟨sourceResult, irExec, ?_, hbodyExec, hmatch⟩
      have hsourceWithEvents :
          SourceSemantics.execStmtListWithEvents (SourceSemantics.effectiveFields model) model.events
            { world := SourceSemantics.withTransactionContext initialWorld tx
              bindings := bindings
              selector := tx.functionSelector }
            fn.body = sourceResult := by
        simpa [hSupported.noEvents] using hsource
      simpa [SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal] using
        hbodyHelperGoal.trans hsourceWithEvents
    · have hscope :
          FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
        intro name hmem
        have hmemBindings : name ∈ bindings.map Prod.fst := by
          rw [ParamLoading.bindSupportedParams_names hbind]
          simpa using hmem
        exact lookupBinding?_some_of_mem bindings name hmemBindings
      have hbounded : FunctionBody.bindingsBounded bindings :=
        FunctionBody.bindingsBounded_of_bindSupportedParams hbind
      have hnoConflict :
          firstFieldWriteSlotConflict model.fields = none := by
        simpa [hSupported.normalizedFields] using
          firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs
            (spec := model)
            (selectors := selectors)
            hvalidateInputs
      have hhelperFreeFields :
          StmtListHelperFreeStepInterface
            model.fields
            (fn.params.map (·.name))
            fn.body :=
        hsupportedFn.body.helperFreeStepInterface hnoConflict
      have hhelperFree :
          StmtListHelperFreeStepInterface
            (SourceSemantics.effectiveFields model)
            (fn.params.map (·.name))
            fn.body := by
        simpa [SourceSemantics.effectiveFields, hSupported.normalizedFields] using hhelperFreeFields
      exact supported_function_body_correct_from_exact_state_generic_with_helpers
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings)
        bindings extraFuel hbodyExtraFuelLower
        (by simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
        hSupported.noEvents
        hSupported.noErrors
        hSupported.noAdtTypes
        hsupportedFn.body.helperSurfaceClosed
        hhelperFree
        (hSupported.noAdtTypes ▸ hbodyCompile)
        hscope
        hbounded
        hbodyStateRuntime
        hbodyStateBindings
  have hbodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
    subst hirFn
    dsimp [extraFuel]
    have hlenle :
        (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
          sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
      exact Nat.le_of_add_le_add_right
        (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
    simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
  exact supported_function_correct_with_helper_proofs_body_goal
    model selectors hSupported hHelperProofs hvalidateInputs fn selector returns
    bodyStmts irFn tx initialWorld bindings hfn hvalidate hreturns hbodyCompile
    hcompile hbind htxNormalized extraFuel hbodyFuel hbodyWithHelpers hcalldataSizeFits
theorem supported_function_correct_with_helper_proofs
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec)
    (selector : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
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
  classical
  let _ := hvalidateInputs
  have hsupportedFn := hSupported.supportedFunctionOfSelectorDispatched hfn
  have hbodyHelperGoal :
      SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
        model
        (SourceSemantics.effectiveFields model)
        hSupported.helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body :=
    SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
      (spec := model)
      (fields := SourceSemantics.effectiveFields model)
      (fuel := hSupported.helperFuel)
      (state := { world := SourceSemantics.withTransactionContext initialWorld tx
                  bindings := bindings
                  selector := tx.functionSelector })
      (stmts := fn.body)
      hsupportedFn.body.helperSurfaceClosed
  exact supported_function_correct_with_helper_proofs_goal
    model selectors hSupported hHelperProofs hvalidateInputs fn selector returns
    bodyStmts irFn tx initialWorld bindings hfn hvalidate hreturns hbodyCompile
    hcompile hbind htxNormalized hbodyHelperGoal hcalldataSizeFits
