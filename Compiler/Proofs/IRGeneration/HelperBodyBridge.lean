import Compiler.CompilationModel.Compile
import Compiler.Proofs.IRGeneration.SupportedSpec

namespace Compiler.Proofs.IRGeneration

open Compiler.CompilationModel

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

end Compiler.Proofs.IRGeneration
