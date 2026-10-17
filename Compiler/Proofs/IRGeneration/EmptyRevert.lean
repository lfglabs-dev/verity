import Compiler.Proofs.IRGeneration.SourceSemantics
import Compiler.SolidityImport.Transactions

/-!
Direct empty-revert equations, independent of the contents of EIP-211's buffer.
The IR interpreter observes reverted status; Denote and the transaction frame
retain the exact zero-byte payload. These equations do not establish the
unfinished general byte-call SourceSemantics/Denote agreement.
-/
namespace Compiler.Proofs.IRGeneration.EmptyRevert

open Compiler Compiler.CompilationModel Compiler.Yul

/-- Every compilation context emits the same direct zero-byte revert. -/
theorem compile_exact (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (dynamicSource : DynamicDataSource)
    (internalRetNames inScopeNames : List String) (isInternal : Bool)
    (adtTypes : List AdtTypeDef) (internalFunctions : List FunctionSpec) :
    compileStmt fields events errors dynamicSource internalRetNames isInternal
      inScopeNames adtTypes .revertEmpty internalFunctions =
      .ok [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])] := rfl

/-- The proof-layer source status is reverted for every entry state. -/
theorem source_exact (fields : List Field) (state : SourceSemantics.RuntimeState) :
    SourceSemantics.execStmt fields state .revertEmpty = .revert := rfl

/-- Two interpreter steps suffice, regardless of available continuation fuel. -/
theorem ir_exact (state : IRState) (extraFuel : Nat) :
    execIRStmts (Nat.succ (Nat.succ extraFuel)) state
      [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])] =
      .revert state := rfl

/-- No memory, returndata or environmental premise is needed for exact bytes. -/
theorem denote_exact (oracle : Denote.DenoteOracle) (fields : List Field)
    (state : Denote.DenoteState) :
    Denote.execStmt oracle fields state .revertEmpty = .revertWithData [] := rfl

/-- Transaction failure restores all accounts and logs, retaining empty bytes. -/
theorem frame_exact (oracle : Denote.DenoteOracle) (fields : List Field)
    (initial : Verity.ContractState) (state : Denote.DenoteState) :
    SolidityImport.Transactions.finishFrame initial
      (Denote.execStmt oracle fields state .revertEmpty) =
      .ok { success := false, data := [], world := initial } := rfl

/-- The proof grammar admits the instruction without a no-call premise. -/
theorem supported (fields : List Field) (scope : List String) :
    SupportedStmtList fields scope [.revertEmpty] := .revertEmptySingle

end Compiler.Proofs.IRGeneration.EmptyRevert
