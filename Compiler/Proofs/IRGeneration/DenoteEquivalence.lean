import Compiler.Proofs.IRGeneration.DenoteFunctionAgreement

/-!
# Equivalence of the canonical denotation and source semantics

This module closes the semantic bridge promised by `Denote.lean`.  The theorem
`denote_eq_sourceSemantics` is deliberately stated at the existing
`SupportedFunction` boundary.  Consequently raw calls, ECM, `memoryArray*`,
dynamic-array accessors, unsupported Yul, internal calls, richer returns, and every
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

/-! Constructor families used by the compositional statement proof. Expression
agreement holds on frames without a raw byte-call return buffer; statement
agreement additionally excludes closed byte transports, which only `Denote`
executes. -/

theorem arithmetic_constructor
    (fields : List Field) (state : DenoteState) (expr : Expr)
    (hraw : state.rawReturndata = none) :
    Denote.evalExpr sourceOracle fields state expr =
      SourceSemantics.evalExpr fields (toRuntimeState state) expr :=
  DenoteAgreement.denote_evalExpr_eq fields state hraw expr

theorem storage_read_constructor
    (fields : List Field) (state : DenoteState) (expr : Expr)
    (hraw : state.rawReturndata = none) :
    Denote.evalExpr sourceOracle fields state expr =
      SourceSemantics.evalExpr fields (toRuntimeState state) expr :=
  DenoteAgreement.denote_evalExpr_eq fields state hraw expr

theorem storage_write_constructor
    (fields : List Field) (state : DenoteState) (stmt : Stmt)
    (hbyteFree : DenoteAgreement.stmtByteFree stmt = true)
    (hraw : state.rawReturndata = none) :
    toStmtResult (Denote.execStmt sourceOracle fields state stmt) =
      SourceSemantics.execStmt fields (toRuntimeState state) stmt :=
  DenoteAgreement.execStmt_eq fields state stmt hbyteFree hraw

theorem control_flow_constructor
    (fields : List Field) (state : DenoteState) (stmt : Stmt)
    (hbyteFree : DenoteAgreement.stmtByteFree stmt = true)
    (hraw : state.rawReturndata = none) :
    toStmtResult (Denote.execStmt sourceOracle fields state stmt) =
      SourceSemantics.execStmt fields (toRuntimeState state) stmt :=
  DenoteAgreement.execStmt_eq fields state stmt hbyteFree hraw

theorem revert_constructor
    (fields : List Field) (state : DenoteState) (stmt : Stmt)
    (hbyteFree : DenoteAgreement.stmtByteFree stmt = true)
    (hraw : state.rawReturndata = none) :
    toStmtResult (Denote.execStmt sourceOracle fields state stmt) =
      SourceSemantics.execStmt fields (toRuntimeState state) stmt :=
  DenoteAgreement.execStmt_eq fields state stmt hbyteFree hraw

theorem statement_list_composition
    (fields : List Field) (state : DenoteState) (stmts : List Stmt)
    (hbyteFree : DenoteAgreement.stmtListByteFree stmts = true)
    (hraw : state.rawReturndata = none) :
    toStmtResult (Denote.execStmtList sourceOracle fields state stmts) =
      SourceSemantics.execStmtList fields (toRuntimeState state) stmts :=
  DenoteAgreement.execStmtList_eq fields state stmts hbyteFree hraw

mutual

/-- The plain contract surface rejects every ECM, so supported bodies carry no
closed byte transport. -/
theorem stmtByteFree_of_contractSurfaceClosed :
    ∀ stmt : Stmt, stmtTouchesUnsupportedContractSurface stmt = false →
      DenoteAgreement.stmtByteFree stmt = true
  | .ite _ thenBranch elseBranch, h => by
      simp only [stmtTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at h
      simp only [DenoteAgreement.stmtByteFree, Bool.and_eq_true]
      exact ⟨stmtListByteFree_of_contractSurfaceClosed thenBranch h.1.2,
        stmtListByteFree_of_contractSurfaceClosed elseBranch h.2⟩
  | .forEach _ count body, h => by
      simp only [DenoteAgreement.stmtByteFree]
      cases count with
      | literal n =>
          cases n with
          | zero =>
              simp only [stmtTouchesUnsupportedContractSurface] at h
              exact stmtListByteFree_of_contractSurfaceClosed body h
          | succ n =>
              cases body with
              | nil => rfl
              | cons _ _ => simp [stmtTouchesUnsupportedContractSurface] at h
      | _ => simp [stmtTouchesUnsupportedContractSurface] at h
  | .ecm _ _, h | .forEachSetBit _ _ _, h | .unsafeBlock _ _, h | .matchAdt _ _ _, h => by
      simp [stmtTouchesUnsupportedContractSurface] at h
  | .letVar .., _ | .assignVar .., _ | .setStorage .., _ | .setStorageAddr .., _
  | .setImmutable .., _ | .setStorageWord .., _ | .setMapping .., _ | .setMappingWord .., _
  | .setMappingPackedWord .., _ | .setMapping2 .., _ | .setMapping2Word .., _
  | .setMappingUint .., _ | .setMappingChain .., _ | .setStructMember .., _
  | .setStructMember2 .., _ | .storageArrayPush .., _ | .storageArrayPop .., _
  | .setStorageArrayElement .., _ | .mstore .., _ | .tstore .., _ | .calldatacopy .., _
  | .returndataCopy .., _ | .require .., _ | .requireError .., _ | .revertError .., _
  | .panicCode .., _ | .panic .., _ | .return .., _ | .stop, _ | .emit .., _
  | .externalCallBind .., _ | .tryExternalCallBind .., _ | .returnValues .., _
  | .returnBytes .., _ | .returnArray .., _ | .returnStorageWords .., _
  | .returnCodeData .., _ | .revertEmpty, _ | .revertReturndata, _ | .internalCall .., _
  | .internalCallAssign .., _ | .rawLog .., _ | .unsafeYul .., _ => rfl

theorem stmtListByteFree_of_contractSurfaceClosed :
    ∀ stmts : List Stmt, stmtListTouchesUnsupportedContractSurface stmts = false →
      DenoteAgreement.stmtListByteFree stmts = true
  | [], _ => rfl
  | stmt :: rest, h => by
      simp only [stmtListTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at h
      simp only [DenoteAgreement.stmtListByteFree, Bool.and_eq_true]
      exact ⟨stmtByteFree_of_contractSurfaceClosed stmt h.1,
        stmtListByteFree_of_contractSurfaceClosed rest h.2⟩

end

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

@[simp] theorem toIRTransaction_functionSelector (tx : DenoteTransaction) :
    (toIRTransaction tx).functionSelector = tx.functionSelector := rfl

@[simp] theorem toIRTransaction_args (tx : DenoteTransaction) :
    (toIRTransaction tx).args = tx.args := rfl

abbrev toSourceResult := DenoteAgreement.toSourceResult

@[simp] theorem effectiveFields_eq (spec : CompilationModel) :
    Denote.effectiveFields spec = SourceSemantics.effectiveFields spec :=
  DenoteAgreement.effectiveFields_eq spec

theorem encodeStorage_eq (spec : CompilationModel) (world : Verity.ContractState) :
    Denote.encodeStorage sourceOracle spec world = SourceSemantics.encodeStorage spec world :=
  DenoteAgreement.encodeStorage_eq spec world

theorem revertedResult_eq (spec : CompilationModel) (world : Verity.ContractState) :
    toSourceResult (Denote.revertedResult sourceOracle spec world) =
      SourceSemantics.revertedResult spec world :=
  DenoteAgreement.toSourceResult_revertedResult spec world

theorem successResult_eq (spec : CompilationModel) (world : Verity.ContractState)
    (ret : Option Nat) :
    toSourceResult (Denote.successResult sourceOracle spec world ret) =
      SourceSemantics.successResult spec world ret :=
  DenoteAgreement.toSourceResult_successResult spec world ret []

theorem withTransactionContext_eq (world : Verity.ContractState) (tx : DenoteTransaction) :
    Denote.withTransactionContext world tx =
      SourceSemantics.withTransactionContext world (toIRTransaction tx) := rfl

/-- Machine-checked equivalence on the currently supported denotation fragment.

`SupportedFunction` is the explicit exclusion boundary: its core/state/call/
effect interfaces reject raw calls, ECM, `memoryArray*`, dynamic calldata-array
operations, unsupported constructs, internal calls, richer returns, and all other
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
      hsupported.body.core.surfaceClosed hsupported.body.state.surfaceClosed
      (SupportedBodyCallInterface.surfaceClosed (hBody := hsupported.body))
      hsupported.body.effects.surfaceClosed
  simp only [Denote.denoteFunction, SourceSemantics.interpretFunction,
    withTransactionContext_eq, effectiveFields_eq, Denote.bindExternalParams,
    SourceSemantics.bindExternalParams, toIRTransaction_functionSelector,
    toIRTransaction_args]
  cases hbind : DynamicAbi.bindExternalParams tx.functionSelector fn.bindingParams tx.args with
  | none =>
      simp only [revertedResult_eq]
  | some bindings =>
      simp only
      have hevents := SourceSemantics.execStmtListWithEvents_eq_execStmtList_of_contractSurfaceClosed
        (SourceSemantics.effectiveFields spec) spec.events fn.body hsurface
        { world := SourceSemantics.withTransactionContext initialWorld (toIRTransaction tx)
          bindings := bindings
          selector := tx.functionSelector }
      rw [hevents]
      have hagree :
          toStmtResult (Denote.execStmtList sourceOracle
            (SourceSemantics.effectiveFields spec)
            { world := SourceSemantics.withTransactionContext initialWorld (toIRTransaction tx)
              bindings := bindings
              selector := tx.functionSelector, errors := spec.errors } fn.body) =
            SourceSemantics.execStmtList (SourceSemantics.effectiveFields spec)
              { world := SourceSemantics.withTransactionContext initialWorld (toIRTransaction tx)
                bindings := bindings
                selector := tx.functionSelector } fn.body := by
        simpa only [DenoteAgreement.toRuntimeState] using
          statement_list_composition (SourceSemantics.effectiveFields spec)
            { world := SourceSemantics.withTransactionContext initialWorld (toIRTransaction tx)
              bindings := bindings
              selector := tx.functionSelector, errors := spec.errors } fn.body
            (stmtListByteFree_of_contractSurfaceClosed fn.body hsurface) rfl
      rw [← hagree]
      cases Denote.execStmtList sourceOracle (SourceSemantics.effectiveFields spec)
          { world := SourceSemantics.withTransactionContext initialWorld (toIRTransaction tx)
            bindings := bindings
            selector := tx.functionSelector, errors := spec.errors } fn.body <;>
        simp [DenoteAgreement.toStmtResult, DenoteAgreement.toRuntimeState,
          DenoteAgreement.toSourceResult_revertData]

end Compiler.Proofs.IRGeneration.DenoteEquivalence
