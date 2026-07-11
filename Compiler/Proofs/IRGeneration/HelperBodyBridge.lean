import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.InternalHelperBodyCorrespondence
import Compiler.Proofs.IRGeneration.SourceSemantics
import Compiler.CompilationModel.Compile
import Compiler.Proofs.IRGeneration.SupportedSpec

namespace Compiler.Proofs.IRGeneration

open Compiler.CompilationModel
open Compiler.Yul

private theorem bindInternalArgs_length_eq_of_some
    {params : List Param} {args : List Nat} {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindInternalArgs params args = some bindings) :
    params.length = args.length := by
  induction params generalizing args bindings with
  | nil =>
      cases args <;> simp [SourceSemantics.bindInternalArgs] at hbind
      cases hbind
      rfl
  | cons param rest ih =>
      cases args with
      | nil =>
          simp [SourceSemantics.bindInternalArgs] at hbind
      | cons arg restArgs =>
          cases htail : SourceSemantics.bindInternalArgs rest restArgs with
          | none =>
              simp [SourceSemantics.bindInternalArgs, htail] at hbind
          | some tailBindings =>
            simp [SourceSemantics.bindInternalArgs, htail] at hbind
            cases hbind
            have hlen := ih htail
            simp [hlen]

mutual

/-- Sufficient syntactic exclusion for statement forms whose compilation can
depend on internal-return targets.  This intentionally follows the conservative
shape of `stmtTouchesUnsupportedHelperSurface`: unsupported wrappers and ADT
matches are rejected at the head instead of recursively inspected. -/
def stmtUsesReturnFamily : Stmt → Bool
  | .return _ | .returnValues _ | .returnArray _ | .returnBytes _
  | .returnStorageWords _ | .returnCodeData _ => true
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true
  | .ite _ thenBranch elseBranch =>
      stmtListUsesReturnFamily thenBranch ||
        stmtListUsesReturnFamily elseBranch
  | .forEach _ _ body | .forEachSetBit _ _ body =>
      stmtListUsesReturnFamily body
  | _ => false

/-- List form of `stmtUsesReturnFamily`. -/
def stmtListUsesReturnFamily : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtUsesReturnFamily stmt ||
        stmtListUsesReturnFamily rest

end

mutual

/-- Sufficient syntactic exclusion for helper bodies that can halt the caller via
source-level `Stmt.stop`.  Conservative unsupported wrappers are rejected at the
head, matching `stmtUsesReturnFamily`. -/
def stmtUsesStop : Stmt → Bool
  | .stop => true
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true
  | .ite _ thenBranch elseBranch =>
      stmtListUsesStop thenBranch ||
        stmtListUsesStop elseBranch
  | .forEach _ _ body | .forEachSetBit _ _ body =>
      stmtListUsesStop body
  | _ => false

/-- List form of `stmtUsesStop`. -/
def stmtListUsesStop : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtUsesStop stmt ||
        stmtListUsesStop rest

end

mutual

/-- Internal-return parameters are irrelevant for statements that syntactically
avoid the return family and conservative unsupported wrappers. -/
theorem compileStmtWithFork_internal_shape_irrelevant_of_returnFree
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) (adtTypes : List AdtTypeDef)
    (targetFork : Verity.Core.Intrinsics.HardFork) (stmt : Stmt)
    (internalFunctions : List FunctionSpec)
    (hreturnFree : stmtUsesReturnFamily stmt = false) :
    CompilationModel.compileStmtWithFork fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes targetFork stmt internalFunctions =
    CompilationModel.compileStmtWithFork fields events errors dynamicSource
      [] false inScopeNames adtTypes targetFork stmt internalFunctions := by
  cases stmt <;>
    simp [stmtUsesReturnFamily, CompilationModel.compileStmtWithFork] at hreturnFree ⊢
  all_goals try (unfold CompilationModel.compileStmtWithFork; rfl)
  case ite cond thenBranch elseBranch =>
    rcases hreturnFree with ⟨hthen, helse⟩
    simp [
      compileStmtListWithFork_internal_shape_irrelevant_of_returnFree
        fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes
        targetFork thenBranch internalFunctions hthen,
      compileStmtListWithFork_internal_shape_irrelevant_of_returnFree
        fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes
        targetFork elseBranch internalFunctions helse
    ]
  case forEach varName count body =>
    simp [
      compileStmtListWithFork_internal_shape_irrelevant_of_returnFree
        fields events errors dynamicSource internalRetNames isInternal
        (CompilationModel.forEachBodyScope inScopeNames varName count body) adtTypes
        targetFork body internalFunctions hreturnFree
    ]
  case forEachSetBit varName bitmap body =>
    simp [
      compileStmtListWithFork_internal_shape_irrelevant_of_returnFree
        fields events errors dynamicSource internalRetNames isInternal
        (CompilationModel.forEachSetBitBodyScope inScopeNames varName bitmap body) adtTypes
        targetFork body internalFunctions hreturnFree,
      compileStmtListWithFork_internal_shape_irrelevant_of_returnFree
        fields events errors dynamicSource internalRetNames isInternal
        (CompilationModel.forEachSetBitFallbackBodyScope inScopeNames varName bitmap body) adtTypes
        targetFork body internalFunctions hreturnFree
    ]

/-- List form of `compileStmtWithFork_internal_shape_irrelevant_of_returnFree`. -/
theorem compileStmtListWithFork_internal_shape_irrelevant_of_returnFree
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) (adtTypes : List AdtTypeDef)
    (targetFork : Verity.Core.Intrinsics.HardFork) (stmts : List Stmt)
    (internalFunctions : List FunctionSpec)
    (hreturnFree : stmtListUsesReturnFamily stmts = false) :
    CompilationModel.compileStmtListWithFork fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes targetFork stmts internalFunctions =
    CompilationModel.compileStmtListWithFork fields events errors dynamicSource
      [] false inScopeNames adtTypes targetFork stmts internalFunctions := by
  cases stmts with
  | nil =>
      simp [CompilationModel.compileStmtListWithFork]
  | cons stmt rest =>
      rcases Bool.or_eq_false_iff.mp hreturnFree with ⟨hstmt, hrest⟩
      simp [
        CompilationModel.compileStmtListWithFork,
        compileStmtWithFork_internal_shape_irrelevant_of_returnFree
          fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes
          targetFork stmt internalFunctions hstmt,
        compileStmtListWithFork_internal_shape_irrelevant_of_returnFree
          fields events errors dynamicSource internalRetNames isInternal
          (collectStmtNames stmt ++ inScopeNames) adtTypes targetFork rest
          internalFunctions hrest
      ]

end

/-- Successful internal-helper compilation has the same body shape as external
statement-list compilation whenever the source body avoids return-family
statements.  The internal return slots may still be declared on the `funcDef`;
this theorem only identifies the helper body. -/
theorem compileInternalFunction_body_eq_external_of_returnFree
    {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    {adtTypes : List AdtTypeDef} {spec : FunctionSpec}
    {targetFork : Verity.Core.Intrinsics.HardFork}
    {internalFunctions : List FunctionSpec} {stmt : YulStmt}
    (hcompile :
      CompilationModel.compileInternalFunction fields events errors adtTypes spec
        (targetFork := targetFork) (internalFunctions := internalFunctions) = Except.ok stmt)
    (hreturnFree : stmtListUsesReturnFamily spec.body = false) :
    ∃ returns retNames bodyStmts,
      CompilationModel.functionReturns spec = Except.ok returns ∧
      CompilationModel.compileStmtListWithFork fields events errors .calldata
        [] false
        (CompilationModel.internalFunctionYulParamNames spec.params ++ retNames)
        adtTypes targetFork spec.body internalFunctions = Except.ok bodyStmts ∧
      stmt = YulStmt.funcDef
        (CompilationModel.internalFunctionYulName spec.name)
        (CompilationModel.internalFunctionYulParamNames spec.params) retNames bodyStmts := by
  simp only [CompilationModel.compileInternalFunction, bind, Except.bind] at hcompile
  cases hvalidate : CompilationModel.validateFunctionSpec spec with
  | error e =>
      simp [hvalidate] at hcompile
  | ok _ =>
      simp only [hvalidate] at hcompile
      cases hreturns : CompilationModel.functionReturns spec with
      | error e =>
          simp [hreturns] at hcompile
      | ok returns =>
          simp only [hreturns] at hcompile
          let paramNames := CompilationModel.internalFunctionYulParamNames spec.params
          let usedNames := paramNames ++ collectStmtListBindNames spec.body
          let retNames := CompilationModel.freshInternalRetNames returns usedNames
          have hirrel :
              CompilationModel.compileStmtListWithFork fields events errors .calldata
                retNames true (paramNames ++ retNames) adtTypes targetFork
                spec.body internalFunctions =
              CompilationModel.compileStmtListWithFork fields events errors .calldata
                [] false (paramNames ++ retNames) adtTypes targetFork
                spec.body internalFunctions :=
            compileStmtListWithFork_internal_shape_irrelevant_of_returnFree fields events errors
              .calldata retNames true (paramNames ++ retNames) adtTypes targetFork
              spec.body internalFunctions hreturnFree
          cases hbody :
              CompilationModel.compileStmtListWithFork fields events errors .calldata
                retNames true (paramNames ++ retNames) adtTypes targetFork spec.body
                internalFunctions with
          | error e =>
              rw [hbody] at hcompile
              cases hcompile
          | ok bodyStmts =>
              rw [hbody] at hcompile
              simp only [pure, Except.pure, Except.ok.injEq] at hcompile
              refine ⟨returns, retNames, bodyStmts, rfl, ?_, hcompile.symm⟩
              rw [← hirrel, hbody]

/-- Exact runtime-table lookup for a supported compiled helper, specialized to
the witness type consumed by helper-call bridge code.  The uniqueness
hypothesis is intentionally explicit: discharging it for whole compiled runtime
contracts is a separate contract-table obligation. -/
theorem findInternalFunction?_some_eq_compiledHelper_of_witness
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {calleeName : String}
    (compiledHelper :
      SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    (hunique : ∀ stmt ∈ runtimeContract.internalFunctions,
      ∀ p r b, irInternalFunctionDefOfStmt? stmt =
        some ⟨CompilationModel.internalFunctionYulName
          compiledHelper.sourceWitness.callee.name, p, r, b⟩ →
        stmt = compiledHelper.compiledStmt) :
    ∃ retNames bodyStmts,
      findInternalFunction? runtimeContract
          (CompilationModel.internalFunctionYulName calleeName) =
        some { name := CompilationModel.internalFunctionYulName calleeName,
               params := CompilationModel.internalFunctionYulParamNames
                 compiledHelper.sourceWitness.callee.params,
               rets := retNames,
               body := bodyStmts } ∧
      compiledHelper.compiledStmt = YulStmt.funcDef
        (CompilationModel.internalFunctionYulName calleeName)
        (CompilationModel.internalFunctionYulParamNames
          compiledHelper.sourceWitness.callee.params)
        retNames bodyStmts := by
  have hname : compiledHelper.sourceWitness.callee.name = calleeName :=
    compiledHelper.sourceWitness.nameEq
  rcases findInternalFunction?_exact_of_compileInternalFunction_mem_unique
      compiledHelper.compileOk
      compiledHelper.presentInRuntime
      hunique with
    ⟨retNames, bodyStmts, hfind, hshape⟩
  rw [hname] at hfind hshape
  exact ⟨retNames, bodyStmts, hfind, hshape⟩

/-- Return-free helper bodies found through the runtime helper table are exactly
the externally-shaped body produced by `compileStmtList ... [] false`.  This is
the body-level bridge used before applying the existing generic body theorem;
the uniqueness hypothesis is the same explicit runtime-table obligation as in
`findInternalFunction?_some_eq_compiledHelper_of_witness`. -/
theorem findInternalFunction?_external_body_of_witness_returnFree
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {calleeName : String}
    (compiledHelper :
      SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    (hreturnFree :
      stmtListUsesReturnFamily compiledHelper.sourceWitness.callee.body = false)
    (hunique : ∀ stmt ∈ runtimeContract.internalFunctions,
      ∀ p r b, irInternalFunctionDefOfStmt? stmt =
        some ⟨CompilationModel.internalFunctionYulName
          compiledHelper.sourceWitness.callee.name, p, r, b⟩ →
        stmt = compiledHelper.compiledStmt) :
    ∃ retNames bodyStmts,
      findInternalFunction? runtimeContract
          (CompilationModel.internalFunctionYulName calleeName) =
        some { name := CompilationModel.internalFunctionYulName calleeName,
               params := CompilationModel.internalFunctionYulParamNames
                 compiledHelper.sourceWitness.callee.params,
               rets := retNames,
               body := bodyStmts } ∧
      CompilationModel.compileStmtListWithFork
        (CompilationModel.applySlotAliasRanges spec.fields spec.slotAliasRanges)
        spec.events spec.errors .calldata [] false
        (CompilationModel.internalFunctionYulParamNames
          compiledHelper.sourceWitness.callee.params ++ retNames)
        spec.adtTypes Verity.Core.Intrinsics.HardFork.cancun
        compiledHelper.sourceWitness.callee.body =
          Except.ok bodyStmts ∧
      compiledHelper.compiledStmt = YulStmt.funcDef
        (CompilationModel.internalFunctionYulName calleeName)
        (CompilationModel.internalFunctionYulParamNames
          compiledHelper.sourceWitness.callee.params)
        retNames bodyStmts := by
  rcases findInternalFunction?_some_eq_compiledHelper_of_witness
      compiledHelper hunique with
    ⟨retNames, bodyStmts, hfind, hshape⟩
  rcases compileInternalFunction_body_eq_external_of_returnFree
      compiledHelper.compileOk hreturnFree with
    ⟨_returns, retNames', bodyStmts', _hreturns, hbodyCompile, hshape'⟩
  rw [hshape] at hshape'
  injection hshape' with _hname _hparams hrets hbody
  subst retNames'
  subst bodyStmts'
  exact ⟨retNames, bodyStmts, hfind, hbodyCompile, hshape⟩

section InternalHelperSummaryBoundary

variable {runtimeContract : IRContract}
variable {spec : CompilationModel}
variable {calleeName : String}
variable (compiledHelper :
  SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
variable (hreturnFree :
  stmtListUsesReturnFamily compiledHelper.sourceWitness.callee.body = false)
variable (hstopFree :
  stmtListUsesStop compiledHelper.sourceWitness.callee.body = false)
variable (hunique : ∀ stmt ∈ runtimeContract.internalFunctions,
  ∀ p r b, irInternalFunctionDefOfStmt? stmt =
    some ⟨CompilationModel.internalFunctionYulName
      compiledHelper.sourceWitness.callee.name, p, r, b⟩ →
    stmt = compiledHelper.compiledStmt)
variable (hsound : SourceSemantics.InternalHelperSummarySound spec
  compiledHelper.sourceWitness.callee
  compiledHelper.sourceWitness.summary.contract)

include hreturnFree hstopFree hunique hsound

/-- N1a boundary package: runtime lookup, return/stop exclusions, and real summary post. -/
theorem compiledInternalHelper_summary_boundary_of_witness_returnStopFree
    (fuel : Nat)
    (initialWorld : Verity.ContractState)
    (args : List Nat) :
    let callee := compiledHelper.sourceWitness.callee
    let yulName := CompilationModel.internalFunctionYulName calleeName
    let paramNames := CompilationModel.internalFunctionYulParamNames callee.params
    ∃ retNames bodyStmts,
      findInternalFunction? runtimeContract yulName =
        some { name := yulName, params := paramNames, rets := retNames, body := bodyStmts } ∧
      CompilationModel.compileStmtListWithFork
        (CompilationModel.applySlotAliasRanges spec.fields spec.slotAliasRanges)
        spec.events spec.errors .calldata [] false (paramNames ++ retNames)
        spec.adtTypes Verity.Core.Intrinsics.HardFork.cancun
        callee.body = Except.ok bodyStmts ∧
      stmtListUsesStop callee.body = false ∧
      let result := SourceSemantics.interpretInternalFunctionFuel spec fuel
        callee initialWorld args
      compiledHelper.sourceWitness.summary.contract.post fuel initialWorld args
        result.success result.returnValue result.world := by
  dsimp only
  rcases findInternalFunction?_external_body_of_witness_returnFree
      compiledHelper hreturnFree hunique with
    ⟨retNames, bodyStmts, hfind, hbodyCompile, _hshape⟩
  refine ⟨retNames, bodyStmts, hfind, hbodyCompile, hstopFree, ?_⟩
  exact hsound fuel initialWorld args

end InternalHelperSummaryBoundary

def internalHelperBodyIRExecResultAsCallResult
    (callerState : IRState) (helper : IRInternalFunctionDef) :
    IRExecResultWithInternals → IRValuesEvalResult
  | .continue finalState =>
      .values (internalReturnValues finalState helper.rets)
        (restoreCallerVars callerState finalState)
  | .leave finalState =>
      .values (internalReturnValues finalState helper.rets)
        (restoreCallerVars callerState finalState)
  | .stop finalState =>
      .stop (restoreCallerVars callerState finalState)
  | .return value finalState =>
      .return value (restoreCallerVars callerState finalState)
  | .revert _ =>
      .revert callerState

/-- N1a helper-body bridge: executing the compiled helper through
`execIRInternalFunctionWithInternals` unfolds to the helper-body execution that
is matched by `internal_helper_body_exec_matches...`, and the projected source
helper result satisfies the real internal-helper summary contract.

The execution equation intentionally leaves `.stop` and `.return` propagation
visible.  Callers that need ordinary helper return values must combine this with
the existing stop/return-family exclusions for the helper body. -/
theorem execIRInternalFunctionWithInternals_obeys_internal_helper_summary
    {runtimeContract : IRContract} {spec : CompilationModel}
    {callee : FunctionSpec} {helper : IRInternalFunctionDef}
    {callerState : IRState} {initialWorld : Verity.ContractState}
    {args : List Nat} {sourceBindings entryBindings : List (String × Nat)}
    {summary : InternalHelperSummaryContract}
    (helperFuel extraFuel : Nat) (hfuelPos : 0 < helperFuel)
    (ctx : InternalHelperBodyExecContext runtimeContract spec callee helper
      callerState initialWorld args sourceBindings entryBindings helperFuel)
    (hsound : SourceSemantics.InternalHelperSummarySound spec callee summary)
    (harity : helper.params.length = callee.params.length) :
    (execIRInternalFunctionWithInternals runtimeContract
        (sizeOf helper.body + extraFuel + 1 + 1) callerState helper args =
      internalHelperBodyIRExecResultAsCallResult callerState helper
        (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel))
    ∧
      summary.post helperFuel initialWorld args
        (internalHelperResultOfStmtResult initialWorld
          (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)).success
        (internalHelperResultOfStmtResult initialWorld
          (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)).returnValue
        (internalHelperResultOfStmtResult initialWorld
          (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)).world := by
  rcases internal_helper_body_exec_matches_entryBindings_and_projected_result_of_bindInternalArgs_and_generic
      (runtimeContract := runtimeContract) (spec := spec) (callee := callee)
      (helper := helper) (callerState := callerState)
      (initialWorld := initialWorld) (args := args)
      (sourceBindings := sourceBindings) (entryBindings := entryBindings)
      helperFuel extraFuel hfuelPos ctx with
    ⟨_hmatch, hinterp⟩
  constructor
  · have hsourceLen : callee.params.length = args.length :=
      bindInternalArgs_length_eq_of_some ctx.bindArgs
    have hlen : helper.params.length = args.length := harity.trans hsourceLen
    rw [execIRInternalFunctionWithInternals_succ_of_params_match
      runtimeContract (sizeOf helper.body + extraFuel + 1)
      callerState helper args hlen]
    rfl
  · have hpost := hsound helperFuel initialWorld args
    simpa [hinterp] using hpost

private theorem internalFunctionYulName_head (calleeName : String) :
    (CompilationModel.internalFunctionYulName calleeName).toList.head? = some 'i' := by
  simp [CompilationModel.internalFunctionYulName, CompilationModel.internalFunctionPrefix]
  decide

private theorem internalFunctionYulName_ne_of_head
    (calleeName builtinName : String)
    (hhead : builtinName.toList.head? ≠ some 'i') :
    CompilationModel.internalFunctionYulName calleeName ≠ builtinName := by
  intro hEq
  have hHead := congrArg (fun s : String => s.toList.head?) hEq
  change (CompilationModel.internalFunctionYulName calleeName).toList.head? =
    builtinName.toList.head? at hHead
  rw [internalFunctionYulName_head calleeName] at hHead
  exact hhead hHead.symm

private theorem internalFunctionYulName_isYulLogName_false (calleeName : String) :
    isYulLogName (CompilationModel.internalFunctionYulName calleeName) = false := by
  simp [isYulLogName,
    internalFunctionYulName_ne_of_head calleeName "log0" (by decide),
    internalFunctionYulName_ne_of_head calleeName "log1" (by decide),
    internalFunctionYulName_ne_of_head calleeName "log2" (by decide),
    internalFunctionYulName_ne_of_head calleeName "log3" (by decide),
    internalFunctionYulName_ne_of_head calleeName "log4" (by decide)]

noncomputable abbrev internalHelperCallFuel
    (helper : IRInternalFunctionDef) (extraFuel : Nat) : Nat :=
  sizeOf helper.body + extraFuel + 1 + 1

abbrev internalHelperSummaryPostAt
    (spec : CompilationModel) (callee : FunctionSpec)
    (initialWorld : Verity.ContractState)
    (entryBindings : List (String × Nat))
    (helperFuel : Nat) (args : List Nat)
    (summary : InternalHelperSummaryContract) : Prop :=
  summary.post helperFuel initialWorld args
    (internalHelperResultOfStmtResult initialWorld
      (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)).success
    (internalHelperResultOfStmtResult initialWorld
      (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)).returnValue
    (internalHelperResultOfStmtResult initialWorld
      (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)).world

abbrev internalHelperAssignCallResult
    (names : List String) (callerState : IRState) (helper : IRInternalFunctionDef)
    (bodyResult : IRExecResultWithInternals) : IRExecResultWithInternals :=
  match internalHelperBodyIRExecResultAsCallResult callerState helper bodyResult with
  | .values values state' =>
      if names.length = values.length then
        .continue (state'.setVars (names.zip values))
      else .revert state'
  | .stop state' => .stop state'
  | .return value state' => .return value state'
  | .revert state' => .revert state'

private theorem execIRStmtsWithInternals_singleton_expr_internalFunctionYulName_call_internal
    (runtimeContract : IRContract) (fuel : Nat) (state : IRState)
    (calleeName : String) (argExprs : List YulExpr)
    (helper : IRInternalFunctionDef) (args : List Nat) (callerState : IRState)
    (hargs : evalIRExprsWithInternals runtimeContract (fuel + 1) state argExprs =
      .values args callerState)
    (hfind : findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper) :
    execIRStmtsWithInternals runtimeContract (fuel + 3) state
      [YulStmt.exprStmt
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] =
      match execIRInternalFunctionWithInternals runtimeContract fuel
          callerState helper args with
      | .values _ state' => .continue state'
      | .stop state' => .stop state'
      | .return value state' => .return value state'
      | .revert state' => .revert state' := by
  exact execIRStmtsWithInternals_singleton_expr_call_internal
    runtimeContract fuel state
    (CompilationModel.internalFunctionYulName calleeName) argExprs helper args callerState
    hargs hfind
    (internalFunctionYulName_ne_of_head calleeName "stop" (by decide))
    (internalFunctionYulName_ne_of_head calleeName "sstore" (by decide))
    (internalFunctionYulName_ne_of_head calleeName "mstore" (by decide))
    (internalFunctionYulName_ne_of_head calleeName "tstore" (by decide))
    (internalFunctionYulName_ne_of_head calleeName "revert" (by decide))
    (internalFunctionYulName_ne_of_head calleeName "return" (by decide))
    (internalFunctionYulName_isYulLogName_false calleeName)

/-- N2/N3 assignment-call instantiation of the N1a helper-summary bridge.
This is the singleton `letMany (.call internal_helper ...)` wrapper around
`execIRInternalFunctionWithInternals_obeys_internal_helper_summary`. -/
theorem execIRStmtsWithInternals_internalCallAssign_obeys_internal_helper_summary
    {runtimeContract : IRContract} {spec : CompilationModel}
    {callee : FunctionSpec} {helper : IRInternalFunctionDef}
    {state callerState : IRState} {initialWorld : Verity.ContractState}
    {names : List String} {calleeName : String}
    {argExprs : List YulExpr} {args : List Nat}
    {sourceBindings entryBindings : List (String × Nat)}
    {summary : InternalHelperSummaryContract}
    (helperFuel extraFuel : Nat) (hfuelPos : 0 < helperFuel)
    (ctx : InternalHelperBodyExecContext runtimeContract spec callee helper
      callerState initialWorld args sourceBindings entryBindings helperFuel)
    (hsound : SourceSemantics.InternalHelperSummarySound spec callee summary)
    (harity : helper.params.length = callee.params.length)
    (hfind : findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper)
    (hargs : evalIRExprsWithInternals runtimeContract
      (internalHelperCallFuel helper extraFuel + 1) state argExprs =
        .values args callerState) :
    (execIRStmtsWithInternals runtimeContract
        (internalHelperCallFuel helper extraFuel + 3) state
        [YulStmt.letMany names
          (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] =
      internalHelperAssignCallResult names callerState helper
        (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel))
    ∧
      internalHelperSummaryPostAt spec callee initialWorld entryBindings
        helperFuel args summary := by
  have hsummary := execIRInternalFunctionWithInternals_obeys_internal_helper_summary
    (runtimeContract := runtimeContract) (spec := spec) (callee := callee) (helper := helper)
    (callerState := callerState) (initialWorld := initialWorld) (args := args)
    (sourceBindings := sourceBindings) (entryBindings := entryBindings) (summary := summary)
    helperFuel extraFuel hfuelPos ctx hsound harity
  constructor
  · rw [execIRStmtsWithInternals_singleton_letMany_call_internal
      runtimeContract (internalHelperCallFuel helper extraFuel) state names
      (CompilationModel.internalFunctionYulName calleeName) argExprs helper args
      callerState hargs hfind]
    rw [show internalHelperCallFuel helper extraFuel =
      sizeOf helper.body + extraFuel + 1 + 1 from rfl, hsummary.1]
    simp [internalHelperAssignCallResult]
    cases internalHelperBodyIRExecResultAsCallResult callerState helper
      (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel) <;> rfl
  · exact hsummary.2

/-- N2/N3 void-call instantiation of the N1a helper-summary bridge.  The normal
helper values are discarded by `exprStmt`, while stop/return/revert propagation
remains explicit. -/
theorem execIRStmtsWithInternals_internalCall_obeys_internal_helper_summary
    {runtimeContract : IRContract} {spec : CompilationModel}
    {callee : FunctionSpec} {helper : IRInternalFunctionDef}
    {state callerState : IRState} {initialWorld : Verity.ContractState}
    {calleeName : String} {argExprs : List YulExpr} {args : List Nat}
    {sourceBindings entryBindings : List (String × Nat)}
    {summary : InternalHelperSummaryContract}
    (helperFuel extraFuel : Nat) (hfuelPos : 0 < helperFuel)
    (ctx : InternalHelperBodyExecContext runtimeContract spec callee helper
      callerState initialWorld args sourceBindings entryBindings helperFuel)
    (hsound : SourceSemantics.InternalHelperSummarySound spec callee summary)
    (harity : helper.params.length = callee.params.length)
    (hfind : findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper)
    (hargs : evalIRExprsWithInternals runtimeContract
      (internalHelperCallFuel helper extraFuel + 1) state argExprs =
        .values args callerState) :
    (execIRStmtsWithInternals runtimeContract
        (internalHelperCallFuel helper extraFuel + 3) state
        [YulStmt.exprStmt
          (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] =
      match internalHelperBodyIRExecResultAsCallResult callerState helper
          (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel) with
      | .values _ state' => IRExecResultWithInternals.continue state'
      | .stop state' => IRExecResultWithInternals.stop state'
      | .return value state' => IRExecResultWithInternals.return value state'
      | .revert state' => IRExecResultWithInternals.revert state')
    ∧
      internalHelperSummaryPostAt spec callee initialWorld entryBindings
        helperFuel args summary := by
  have hsummary :=
    execIRInternalFunctionWithInternals_obeys_internal_helper_summary
      (runtimeContract := runtimeContract) (spec := spec) (callee := callee)
      (helper := helper) (callerState := callerState)
      (initialWorld := initialWorld) (args := args)
      (sourceBindings := sourceBindings) (entryBindings := entryBindings)
      (summary := summary) helperFuel extraFuel hfuelPos ctx hsound harity
  constructor
  · rw [execIRStmtsWithInternals_singleton_expr_internalFunctionYulName_call_internal
      runtimeContract (internalHelperCallFuel helper extraFuel) state
      calleeName argExprs helper args callerState hargs hfind]
    rw [show internalHelperCallFuel helper extraFuel =
      sizeOf helper.body + extraFuel + 1 + 1 from rfl]
    rw [hsummary.1]
  · exact hsummary.2

/-- Concrete regression for the rank-0 void-helper body-shape seam: an empty
helper body is unaffected by internal return targets. -/
theorem empty_void_helper_body_compile_shape_irrelevant_regression :
    CompilationModel.compileStmtListWithFork [] [] [] .calldata
      ([] : List String) true ([] : List String) []
      Verity.Core.Intrinsics.HardFork.cancun ([] : List Stmt) [] =
    CompilationModel.compileStmtListWithFork [] [] [] .calldata
      [] false [] [] Verity.Core.Intrinsics.HardFork.cancun ([] : List Stmt) [] := by
  exact
    compileStmtListWithFork_internal_shape_irrelevant_of_returnFree
      [] [] [] .calldata ([] : List String) true ([] : List String) []
      Verity.Core.Intrinsics.HardFork.cancun ([] : List Stmt) [] rfl

end Compiler.Proofs.IRGeneration
