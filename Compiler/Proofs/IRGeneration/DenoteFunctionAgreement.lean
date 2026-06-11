import Compiler.Proofs.IRGeneration.DenoteAgreement

/-!
# Function-level agreement between `Denote.denoteFunction` and
`SourceSemantics.interpretFunction`

Extends the statement-level agreement of `DenoteAgreement` to the external
function boundary: parameter binding, transaction context, and observable
result encoding all coincide, so the compiler-free denotation of a function
equals the trusted source interpretation (on the event-free fragment).
-/

namespace Compiler.Proofs.IRGeneration

namespace DenoteAgreement

open Compiler.CompilationModel

/-- IR transaction → compiler-free denote transaction (field-for-field). -/
def ofIRTransaction (tx : IRTransaction) : Denote.DenoteTransaction :=
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

/-- Denote result → source result (the two structures coincide). -/
def toSourceResult (r : Denote.DenoteResult) : SourceSemantics.SourceContractResult :=
  { success := r.success
    returnValue := r.returnValue
    finalStorage := r.finalStorage
    events := r.events }

theorem dedupNatPreserve_go_eq :
    ∀ (xs seen : List Nat),
      Denote.dedupNatPreserve.go seen xs = dedupNatPreserve.go seen xs
  | [], _ => rfl
  | x :: rest, seen => by
      simp only [Denote.dedupNatPreserve.go, dedupNatPreserve.go]
      rw [dedupNatPreserve_go_eq rest seen, dedupNatPreserve_go_eq rest (x :: seen)]

@[simp] theorem dedupNatPreserve_eq (xs : List Nat) :
    Denote.dedupNatPreserve xs = dedupNatPreserve xs :=
  dedupNatPreserve_go_eq xs []

@[simp] theorem derivedAliasSlotsForSource_eq (sourceSlot : Nat)
    (ranges : List SlotAliasRange) :
    Denote.derivedAliasSlotsForSource sourceSlot ranges =
      derivedAliasSlotsForSource sourceSlot ranges := by
  unfold Denote.derivedAliasSlotsForSource derivedAliasSlotsForSource
  rw [dedupNatPreserve_eq]
  rfl

theorem applySlotAliasRanges_go_eq (ranges : List SlotAliasRange) :
    ∀ (remaining : List Field) (idx : Nat),
      Denote.applySlotAliasRanges.go ranges remaining idx =
        applySlotAliasRanges.go ranges remaining idx
  | [], _ => rfl
  | f :: rest, idx => by
      simp only [Denote.applySlotAliasRanges.go, applySlotAliasRanges.go,
        dedupNatPreserve_eq, derivedAliasSlotsForSource_eq]
      rw [applySlotAliasRanges_go_eq ranges rest (idx + 1)]

@[simp] theorem applySlotAliasRanges_eq (fields : List Field)
    (ranges : List SlotAliasRange) :
    Denote.applySlotAliasRanges fields ranges = applySlotAliasRanges fields ranges :=
  applySlotAliasRanges_go_eq ranges fields 0

@[simp] theorem effectiveFields_eq (spec : CompilationModel) :
    Denote.effectiveFields spec = SourceSemantics.effectiveFields spec :=
  applySlotAliasRanges_eq spec.fields spec.slotAliasRanges

@[simp] theorem encodeEvents_eq (events : List Verity.Event) :
    Denote.encodeEvents events = SourceSemantics.encodeEvents events := rfl

@[simp] theorem decodeSupportedParamWord_eq (ty : ParamType) (word : Nat) :
    Denote.decodeSupportedParamWord ty word =
      SourceSemantics.decodeSupportedParamWord ty word := by
  cases ty <;> rfl

theorem bindSupportedParams_eq :
    ∀ (params : List Param) (args : List Nat),
      Denote.bindSupportedParams params args =
        SourceSemantics.bindSupportedParams params args
  | [], _ => rfl
  | _ :: _, [] => rfl
  | param :: rest, arg :: restArgs => by
      simp only [Denote.bindSupportedParams, SourceSemantics.bindSupportedParams,
        decodeSupportedParamWord_eq, bindSupportedParams_eq rest restArgs]

@[simp] theorem ofIRTransaction_args (tx : IRTransaction) :
    (ofIRTransaction tx).args = tx.args := rfl

@[simp] theorem ofIRTransaction_functionSelector (tx : IRTransaction) :
    (ofIRTransaction tx).functionSelector = tx.functionSelector := rfl

@[simp] theorem withTransactionContext_eq
    (world : Verity.ContractState) (tx : IRTransaction) :
    Denote.withTransactionContext world (ofIRTransaction tx) =
      SourceSemantics.withTransactionContext world tx := rfl

theorem findResolvedFieldAtSlot_go_eq :
    ∀ (remaining : List Field) (slot idx : Nat),
      Denote.findResolvedFieldAtSlot.go slot remaining idx =
        SourceSemantics.findResolvedFieldAtSlot.go slot remaining idx
  | [], _, _ => rfl
  | field :: rest, slot, idx => by
      simp only [Denote.findResolvedFieldAtSlot.go, SourceSemantics.findResolvedFieldAtSlot.go]
      rw [findResolvedFieldAtSlot_go_eq rest slot (idx + 1)]
      rfl

@[simp] theorem findResolvedFieldAtSlot_eq (fields : List Field) (slot : Nat) :
    Denote.findResolvedFieldAtSlot fields slot =
      SourceSemantics.findResolvedFieldAtSlot fields slot :=
  findResolvedFieldAtSlot_go_eq fields slot 0

theorem findDynamicArrayElementAtSlot_scanElements_eq (targetSlot : Nat) :
    ∀ (baseSlot : Nat) (values : List Verity.Core.Uint256) (idx : Nat),
      Denote.findDynamicArrayElementAtSlot.scanElements sourceOracle targetSlot baseSlot
          values idx =
        SourceSemantics.findDynamicArrayElementAtSlot.scanElements targetSlot baseSlot
          values idx
  | _, [], _ => rfl
  | baseSlot, value :: rest, idx => by
      simp only [Denote.findDynamicArrayElementAtSlot.scanElements,
        SourceSemantics.findDynamicArrayElementAtSlot.scanElements,
        sourceOracle_mappingSlot, Compiler.Proofs.abstractMappingSlot_eq_solidity]
      rw [findDynamicArrayElementAtSlot_scanElements_eq targetSlot baseSlot rest (idx + 1)]
      rfl

theorem findDynamicArrayElementAtSlot_go_eq
    (world : Verity.ContractState) (targetSlot : Nat) :
    ∀ (remaining : List Field) (idx : Nat),
      Denote.findDynamicArrayElementAtSlot.go sourceOracle world targetSlot remaining idx =
        SourceSemantics.findDynamicArrayElementAtSlot.go world targetSlot remaining idx
  | [], _ => rfl
  | field :: rest, idx => by
      simp only [Denote.findDynamicArrayElementAtSlot.go,
        SourceSemantics.findDynamicArrayElementAtSlot.go,
        findDynamicArrayElementAtSlot_scanElements_eq, Verity.ContractState.readArray]
      rw [findDynamicArrayElementAtSlot_go_eq world targetSlot rest (idx + 1)]
      rfl

@[simp] theorem findDynamicArrayElementAtSlot_eq
    (fields : List Field) (world : Verity.ContractState) (targetSlot : Nat) :
    Denote.findDynamicArrayElementAtSlot sourceOracle fields world targetSlot =
      SourceSemantics.findDynamicArrayElementAtSlot fields world targetSlot :=
  findDynamicArrayElementAtSlot_go_eq world targetSlot fields 0

@[simp] theorem encodeStorageAt_eq
    (fields : List Field) (world : Verity.ContractState) (slot : Nat) :
    Denote.encodeStorageAt sourceOracle fields world slot =
      SourceSemantics.encodeStorageAt fields world slot := by
  simp only [Denote.encodeStorageAt, SourceSemantics.encodeStorageAt,
    findResolvedFieldAtSlot_eq, findDynamicArrayElementAtSlot_eq,
    Verity.ContractState.readSlot, Verity.ContractState.readAddrSlot,
    Verity.ContractState.readArray]
  rfl

@[simp] theorem encodeStorage_eq (spec : CompilationModel) (world : Verity.ContractState) :
    Denote.encodeStorage sourceOracle spec world = SourceSemantics.encodeStorage spec world := by
  funext slot
  simp only [Denote.encodeStorage, SourceSemantics.encodeStorage, effectiveFields_eq]
  exact encodeStorageAt_eq (SourceSemantics.effectiveFields spec) world slot

@[simp] theorem toSourceResult_revertedResult
    (spec : CompilationModel) (world : Verity.ContractState) :
    toSourceResult (Denote.revertedResult sourceOracle spec world) =
      SourceSemantics.revertedResult spec world := by
  simp [toSourceResult, Denote.revertedResult, SourceSemantics.revertedResult]

@[simp] theorem toSourceResult_successResult
    (spec : CompilationModel) (world : Verity.ContractState) (ret : Option Nat) :
    toSourceResult (Denote.successResult sourceOracle spec world ret) =
      SourceSemantics.successResult spec world ret := by
  simp [toSourceResult, Denote.successResult, SourceSemantics.successResult]

/-- Function-level agreement: on the event-free fragment, the compiler-free
denotation of an external function coincides with the trusted source
interpretation. -/
theorem denoteFunction_eq
    (spec : CompilationModel)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hnoEvents : spec.events = []) :
    toSourceResult
        (Denote.denoteFunction sourceOracle spec fn (ofIRTransaction tx) initialWorld) =
      SourceSemantics.interpretFunction spec fn tx initialWorld := by
  unfold Denote.denoteFunction SourceSemantics.interpretFunction
  simp only [hnoEvents, SourceSemantics.execStmtListWithEvents_nil_eq_execStmtList,
    withTransactionContext_eq, effectiveFields_eq, bindSupportedParams_eq,
    ofIRTransaction_args, ofIRTransaction_functionSelector]
  cases hbind : SourceSemantics.bindSupportedParams fn.params tx.args with
  | none => simp
  | some bindings =>
      have hexec := execStmtList_eq (SourceSemantics.effectiveFields spec)
        ⟨SourceSemantics.withTransactionContext initialWorld tx, bindings,
          tx.functionSelector⟩ fn.body
      simp only [toRuntimeState] at hexec
      dsimp only
      rw [← hexec]
      cases Denote.execStmtList sourceOracle (SourceSemantics.effectiveFields spec)
          ⟨SourceSemantics.withTransactionContext initialWorld tx, bindings,
            tx.functionSelector⟩ fn.body <;>
        simp [toStmtResult, toRuntimeState]

end DenoteAgreement

end Compiler.Proofs.IRGeneration
