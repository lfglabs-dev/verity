import Compiler.CompilationModel.Compile

/-! Exact generic model-to-Yul emission for value-zero creation. These equations
establish AST lowering and retained validation classifications, not native
Yul/world execution agreement or Solidity importer admission. -/
namespace Compiler.CompilationModel
open Compiler.Yul

theorem compileStmtWithFork_create2 (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (dynamicSource : DynamicDataSource)
    (internalRetNames : List String) (isInternal : Bool) (inScopeNames : List String)
    (adtTypes : List AdtTypeDef) (fork : Verity.Core.Intrinsics.HardFork)
    (destination : String) (offset size salt : Expr) (internalFunctions : List FunctionSpec) :
    compileStmtWithFork fields events errors dynamicSource internalRetNames isInternal inScopeNames
      adtTypes fork (.create2 destination offset size salt) internalFunctions = (do
        let args ← compileExprListWithInternals fields dynamicSource internalFunctions [offset,size,salt]
        pure [YulStmt.letMany [destination] (YulExpr.call "create2" (YulExpr.lit 0 :: args))]) := rfl

theorem create2_readsState (destination : String) (offset size salt : Expr) :
    stmtReadsStateOrEnvNode (.create2 destination offset size salt) = true := rfl

theorem create2_writesState (destination : String) (offset size salt : Expr) :
    stmtWritesStateNode (.create2 destination offset size salt) = true := rfl

theorem create2_persistentWrite (destination : String) (offset size salt : Expr) :
    stmtIsPersistentWriteNode (.create2 destination offset size salt) = true := rfl

theorem create2_containsExternalExecution (destination : String) (offset size salt : Expr) :
    stmtContainsExternalCallNode (.create2 destination offset size salt) = true := rfl

end Compiler.CompilationModel
