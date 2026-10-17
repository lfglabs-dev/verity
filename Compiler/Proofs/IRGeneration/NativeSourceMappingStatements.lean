import Compiler.Proofs.IRGeneration.NativeSourceMappingWrites
import Compiler.Proofs.IRGeneration.SourceTypedCompatibility

namespace Compiler.Proofs.IRGeneration.NativeSourceMappingStatements
open Compiler.CompilationModel Compiler.Proofs.IRGeneration SourceSemantics SourceExpressionOutcome

/-- Actual typed chain statements consume keys then value at their real operand poststates. -/
theorem chain_statement_operands (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (initial keyState final : RuntimeState) (name : String)
    (keys : List Expr) (value : Expr) (resolvedKeys : List Nat) (resolved : Nat)
    (field : Field) (slot : Nat)
    (keysEvaluated : SourceExpressionEvaluation.evalArgs
      (SourceStatementEvaluation.execStmtsFrame true spec fields fuel)
      spec fields fuel initial keys = .value resolvedKeys keyState)
    (valueEvaluated : SourceExpressionEvaluation.eval
      (SourceStatementEvaluation.execStmtsFrame true spec fields fuel)
      spec fields fuel keyState value = .value resolved final)
    (fieldFound : findFieldWithResolvedSlot fields name = some (field, slot)) :
    SourceStatementEvaluation.execStmt spec fields (fuel + 1) initial (.setMappingChain name keys value) =
      SourceSemantics.execStmtWithEvents fields spec.events final
        (.setMappingChain name (resolvedKeys.map Expr.literal) (.literal resolved)) := by
  simp only [SourceStatementEvaluation.execStmt, SourceStatementEvaluation.execStmtFrame,
    keysEvaluated, valueEvaluated, SourceStatementEvaluation.consume, fieldFound]

/-- Resolved literal keys retain the source evaluator's exact word normalization. -/
theorem literal_keys (fields : List Field) (state : RuntimeState) (keys : List Nat) :
    evalExprList fields state (keys.map Expr.literal) = some (keys.map wordNormalize) := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simp only [List.map_cons, evalExprList, evalExpr, ih, Bind.bind, Option.bind, Pure.pure]

/-- The resolved complete Source statement computes the same physical mapping update. -/
theorem resolved_chain_statement (fields : List Field) (events : List EventDef)
    (state : RuntimeState) (name : String) (keys : List Nat) (value base : Nat)
    (slots : findFieldWriteSlots fields name = some [base]) :
    execStmtWithEvents fields events state
      (.setMappingChain name (keys.map Expr.literal) (.literal value)) =
      .continue { state with world := (writeAddressKeyedMappingChainFieldSlots fields name state.world
          [base] (keys.map wordNormalize) (wordNormalize value)) } := by
  simp only [execStmtWithEvents, slots, literal_keys, evalExpr]

/-- The typed consumer's result retains every operand effect before the actual chain write. -/
theorem typed_chain_statement (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (initial keyState final : RuntimeState) (name : String)
    (keys : List Expr) (value : Expr) (resolvedKeys : List Nat) (resolved base : Nat)
    (field : Field)
    (keysEvaluated : SourceExpressionEvaluation.evalArgs
      (SourceStatementEvaluation.execStmtsFrame true spec fields fuel)
      spec fields fuel initial keys = .value resolvedKeys keyState)
    (valueEvaluated : SourceExpressionEvaluation.eval
      (SourceStatementEvaluation.execStmtsFrame true spec fields fuel)
      spec fields fuel keyState value = .value resolved final)
    (fieldFound : findFieldWithResolvedSlot fields name = some (field, base))
    (slots : findFieldWriteSlots fields name = some [base]) :
    SourceStatementEvaluation.execStmt spec fields (fuel + 1) initial (.setMappingChain name keys value) =
      .continue { final with world := (writeAddressKeyedMappingChainFieldSlots fields name final.world
          [base] (resolvedKeys.map wordNormalize) (wordNormalize resolved)) } := by
  rw [chain_statement_operands spec fields fuel initial keyState final name keys value resolvedKeys resolved
    field base keysEvaluated valueEvaluated fieldFound]
  exact resolved_chain_statement fields spec.events final name resolvedKeys resolved base slots

end Compiler.Proofs.IRGeneration.NativeSourceMappingStatements
