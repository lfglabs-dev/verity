import Compiler.CompilationModel.Compile
import Compiler.Proofs.IRGeneration.SupportedSpec

namespace Compiler.Proofs.IRGeneration

open Compiler.CompilationModel
open Compiler.Yul

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
        (targetFork := targetFork) (internalFunctions := internalFunctions) =
          Except.ok stmt)
    (hreturnFree : stmtListUsesReturnFamily spec.body = false) :
    ∃ returns retNames bodyStmts,
      CompilationModel.functionReturns spec = Except.ok returns ∧
      CompilationModel.compileStmtListWithFork fields events errors .calldata
        [] false
        (CompilationModel.internalFunctionYulParamNames spec.params ++ retNames)
        adtTypes targetFork spec.body internalFunctions = Except.ok bodyStmts ∧
      stmt = YulStmt.funcDef
        (CompilationModel.internalFunctionYulName spec.name)
        (CompilationModel.internalFunctionYulParamNames spec.params)
        retNames
        bodyStmts := by
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
            compileStmtListWithFork_internal_shape_irrelevant_of_returnFree
              fields events errors .calldata retNames true (paramNames ++ retNames)
              adtTypes targetFork spec.body internalFunctions hreturnFree
          cases hbody :
              CompilationModel.compileStmtListWithFork fields events errors .calldata
                retNames true (paramNames ++ retNames) adtTypes targetFork
                spec.body internalFunctions with
          | error e =>
              rw [hbody] at hcompile
              cases hcompile
          | ok bodyStmts =>
              rw [hbody] at hcompile
              simp only [pure, Except.pure, Except.ok.injEq] at hcompile
              refine ⟨returns, retNames, bodyStmts, rfl, ?_, hcompile.symm⟩
              rw [← hirrel, hbody]

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
