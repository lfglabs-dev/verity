import Compiler.Proofs.IRGeneration.DenoteAgreement

/-!
# Equivalence of the canonical denotation and source semantics

This module closes the semantic bridge promised by `Denote.lean`.  The theorem
`denote_eq_sourceSemantics` is deliberately stated at the existing
`SupportedFunction` boundary.  Consequently raw calls, ECM, `memoryArray*`,
dynamic-array accessors, unsafe Yul, internal calls, richer returns, and every
other constructor rejected by the feature-local supported-fragment predicates
are outside the theorem.  Adding a newly denoted constructor therefore only
requires extending the corresponding constructor lemma in
`DenoteAgreement`; the whole-function proof below does not change.
-/

namespace Compiler.Proofs.IRGeneration.DenoteEquivalence

open Compiler.CompilationModel
open Compiler.CompilationModel.Denote

abbrev sourceOracle := DenoteAgreement.sourceOracle
abbrev toRuntimeState := DenoteAgreement.toRuntimeState
abbrev toStmtResult := DenoteAgreement.toStmtResult

/-! Constructor families used by the compositional statement proof. -/

theorem arithmetic_constructor
    (fields : List Field) (state : DenoteState) (expr : Expr) :
    Denote.evalExpr sourceOracle fields state expr =
      SourceSemantics.evalExpr fields (toRuntimeState state) expr :=
  DenoteAgreement.denote_evalExpr_eq fields state expr

theorem storage_read_constructor
    (fields : List Field) (state : DenoteState) (expr : Expr) :
    Denote.evalExpr sourceOracle fields state expr =
      SourceSemantics.evalExpr fields (toRuntimeState state) expr :=
  DenoteAgreement.denote_evalExpr_eq fields state expr

theorem storage_write_constructor
    (fields : List Field) (state : DenoteState) (stmt : Stmt) :
    toStmtResult (Denote.execStmt sourceOracle fields state stmt) =
      SourceSemantics.execStmt fields (toRuntimeState state) stmt :=
  DenoteAgreement.execStmt_eq fields state stmt

theorem control_flow_constructor
    (fields : List Field) (state : DenoteState) (stmt : Stmt) :
    toStmtResult (Denote.execStmt sourceOracle fields state stmt) =
      SourceSemantics.execStmt fields (toRuntimeState state) stmt :=
  DenoteAgreement.execStmt_eq fields state stmt

theorem revert_constructor
    (fields : List Field) (state : DenoteState) (stmt : Stmt) :
    toStmtResult (Denote.execStmt sourceOracle fields state stmt) =
      SourceSemantics.execStmt fields (toRuntimeState state) stmt :=
  DenoteAgreement.execStmt_eq fields state stmt

theorem statement_list_composition
    (fields : List Field) (state : DenoteState) (stmts : List Stmt) :
    toStmtResult (Denote.execStmtList sourceOracle fields state stmts) =
      SourceSemantics.execStmtList fields (toRuntimeState state) stmts :=
  DenoteAgreement.execStmtList_eq fields state stmts

/-! Function-boundary conversions and observable-result agreement. -/

def toIRTransaction (tx : DenoteTransaction) : IRTransaction :=
  { sender := tx.sender
    msgValue := tx.msgValue
    thisAddress := tx.thisAddress
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId
    blobBaseFee := tx.blobBaseFee
    txOrigin := tx.txOrigin
    functionSelector := tx.functionSelector
    args := tx.args }

def toSourceResult (result : DenoteResult) : SourceSemantics.SourceContractResult :=
  { success := result.success
    returnValue := result.returnValue
    finalStorage := result.finalStorage
    events := result.events }

@[simp] theorem effectiveFields_eq (spec : CompilationModel) :
    Denote.effectiveFields spec = SourceSemantics.effectiveFields spec := rfl

theorem encodeStorage_eq (spec : CompilationModel) (world : Verity.ContractState) :
    Denote.encodeStorage sourceOracle spec world = SourceSemantics.encodeStorage spec world := by
  funext slot
  rfl

theorem revertedResult_eq (spec : CompilationModel) (world : Verity.ContractState) :
    toSourceResult (Denote.revertedResult sourceOracle spec world) =
      SourceSemantics.revertedResult spec world := by
  ext <;> simp [toSourceResult, Denote.revertedResult, SourceSemantics.revertedResult,
    encodeStorage_eq]

theorem successResult_eq (spec : CompilationModel) (world : Verity.ContractState)
    (ret : Option Nat) :
    toSourceResult (Denote.successResult sourceOracle spec world ret) =
      SourceSemantics.successResult spec world ret := by
  ext <;> simp [toSourceResult, Denote.successResult, SourceSemantics.successResult,
    encodeStorage_eq]

theorem withTransactionContext_eq (world : Verity.ContractState) (tx : DenoteTransaction) :
    Denote.withTransactionContext world tx =
      SourceSemantics.withTransactionContext world (toIRTransaction tx) := rfl

/-- Machine-checked equivalence on the currently supported denotation fragment.

`SupportedFunction` is the explicit exclusion boundary: its core/state/call/
effect interfaces reject raw calls, ECM, `memoryArray*`, dynamic calldata-array
operations, unsafe constructs, internal calls, richer returns, and all other
constructors not admitted by the current denoted fragment.  From the same
initial world and transaction environment, both semantics have identical
success/revert behavior, return value, final storage, and encoded event trace.
-/
theorem denote_eq_sourceSemantics
    (spec : CompilationModel) (fn : FunctionSpec)
    (tx : DenoteTransaction) (initialWorld : Verity.ContractState)
    (hsupported : SupportedFunction spec fn) :
    toSourceResult (Denote.denoteFunction sourceOracle spec fn tx initialWorld) =
      SourceSemantics.interpretFunction spec fn (toIRTransaction tx) initialWorld := by
  have hsurface : stmtListTouchesUnsupportedContractSurface fn.body = false :=
    stmtListTouchesUnsupportedContractSurface_eq_false_of_featureClosed fn.body
      hsupported.body.core.surfaceClosed
      hsupported.body.state.surfaceClosed
      hsupported.body.calls.surfaceClosed
      hsupported.body.effects.surfaceClosed
  simp only [Denote.denoteFunction, SourceSemantics.interpretFunction,
    withTransactionContext_eq, effectiveFields_eq]
  cases hbind : Denote.bindExternalParams tx.functionSelector fn.params tx.args with
  | none =>
      rw [revertedResult_eq]
      rfl
  | some bindings =>
      have hevents := SourceSemantics.execStmtListWithEvents_eq_execStmtList_of_contractSurfaceClosed
        (SourceSemantics.effectiveFields spec) spec.events fn.body hsurface
        { world := SourceSemantics.withTransactionContext initialWorld (toIRTransaction tx)
          bindings := bindings
          selector := tx.functionSelector }
      rw [hevents]
      have hagree := statement_list_composition (Denote.effectiveFields spec)
        { world := Denote.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector } fn.body
      cases hout : Denote.execStmtList sourceOracle (Denote.effectiveFields spec)
          { world := Denote.withTransactionContext initialWorld tx
            bindings := bindings
            selector := tx.functionSelector } fn.body <;>
        simp [hout, toStmtResult] at hagree <;>
        simp [hout, hagree, successResult_eq, revertedResult_eq]

end Compiler.Proofs.IRGeneration.DenoteEquivalence
