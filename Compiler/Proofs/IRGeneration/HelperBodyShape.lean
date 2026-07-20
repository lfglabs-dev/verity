import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.GenericInduction.Helpers
import Compiler.Proofs.IRGeneration.SourceSemantics
import Compiler.CompilationModel.Compile
import Compiler.Proofs.IRGeneration.SupportedSpec

namespace Compiler.Proofs.IRGeneration

open Compiler.CompilationModel
open Compiler.Yul

/-- Successful internal-argument binding implies exact source arity. -/
theorem bindInternalArgs_length_eq_of_some
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

/-- Node-local classifier for expression-position helper calls. -/
def exprUsesInternalHelperCallNode : Expr → Bool
  | .internalCall _ _ => true
  | _ => false

/-- Does an expression contain an internal helper call? -/
def exprUsesInternalHelperCall (expr : Expr) : Bool :=
  expr.anyDeep exprUsesInternalHelperCallNode

/-- Node-local classifier for helper-body shapes that can halt the caller, or
whose stop behavior is not summarized at the N1a boundary. -/
def stmtUsesStopBoundaryNode : Stmt → Bool
  | .stop => true
  | .internalCall _ _ | .internalCallAssign _ _ _ => true
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true
  | stmt =>
      stmt.directMetadata.subexpressions.any exprUsesInternalHelperCall

/-- Sufficient syntactic exclusion for helper bodies that can halt the caller via
source-level `Stmt.stop`.  Internal helper calls are rejected here because this
boundary does not consume a transitive no-stop summary for callees. -/
def stmtUsesStop (stmt : Stmt) : Bool :=
  stmt.anyDeep stmtUsesStopBoundaryNode

/-- List form of `stmtUsesStop`. -/
def stmtListUsesStop (stmts : List Stmt) : Bool :=
  Stmt.anyDeepList stmtUsesStopBoundaryNode stmts

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
          (collectStmtBindNames stmt ++ inScopeNames) adtTypes targetFork rest
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
      compiledHelper.sourceWitness.summary.contract.post fuel 0 initialWorld args
        result.success result.returnValue result.world := by
  dsimp only
  rcases findInternalFunction?_external_body_of_witness_returnFree
      compiledHelper hreturnFree hunique with
    ⟨retNames, bodyStmts, hfind, hbodyCompile, _hshape⟩
  refine ⟨retNames, bodyStmts, hfind, hbodyCompile, hstopFree, ?_⟩
  exact hsound fuel initialWorld args

end InternalHelperSummaryBoundary
