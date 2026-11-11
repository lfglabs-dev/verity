import Compiler.Proofs.EndToEnd.SimpleStorage
import Verity.Specs.ObsAlgebra

/-!
# Cross-Layer `Obs` Projections and `ObsEquiv` End-to-End Bridge

Projects Layer 1 (`Denote.DenoteResult` / `SourceSemantics.SourceContractResult`),
Layer 2 (`IRResult`), and Layer 3 (`YulResult`) onto the canonical gas-free
observation type `Verity.Specs.ObsAlgebra.Obs`, and proves `ObsEquiv` across all
existing Layer 1 -> Layer 2 -> Layer 3 preservation theorems.
-/

namespace Compiler.Proofs.EndToEnd

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends
open Verity.Specs.ObsAlgebra

/-- Canonical 32-byte big-endian ABI encoding of a word as `List UInt8`. -/
def obsWordBytes (word : Nat) : List UInt8 :=
  (irWordToBytesBE (word % Compiler.Constants.evmModulus)).toList

/-- Project a word-encoded proof event (`topics ++ dataWords`) to `ObsLog`. -/
def obsLogOfEncodedEvent (emitter : Nat) (ev : List Nat) : ObsLog :=
  { emitter := emitter
    topics := ev.take 4
    data := (ev.drop 4).flatMap obsWordBytes }

/-- Project `ExecStatus` from a boolean success flag. -/
def obsExecStatus (ok : Bool) : ExecStatus :=
  if ok then .success else .revert

/-- Project optional word return value onto `returndata` bytes. -/
def obsReturndataOfWord (ret : Option Nat) : List UInt8 :=
  match ret with
  | some w => obsWordBytes w
  | none => []

/-- Project a `SourceContractResult` onto `Obs` over `observableSlots`. -/
def sourceResultToObs
    (emitter : Nat) (observableSlots : List Nat)
    (r : SourceSemantics.SourceContractResult) : Obs :=
  { status := obsExecStatus r.success
    returndata := obsReturndataOfWord r.returnValue
    logs := r.events.map (obsLogOfEncodedEvent emitter)
    storage := observableSlots.map fun slot =>
      ((IRStorageSlot.ofNat slot).toNat,
        (IRStorageWord.ofNat (r.finalStorage (IRStorageSlot.ofNat slot).toNat)).toNat)
    transient := [] }

/-- Project a compiler-free `DenoteResult` onto `Obs` over `observableSlots`. -/
def denoteResultToObs
    (emitter : Nat) (observableSlots : List Nat)
    (r : CompilationModel.Denote.DenoteResult) : Obs :=
  sourceResultToObs emitter observableSlots (DenoteAgreement.toSourceResult r)

/-- Project an `IRResult` onto `Obs` over `observableSlots`. -/
def irResultToObs
    (emitter : Nat) (observableSlots : List Nat)
    (r : IRResult) : Obs :=
  { status := obsExecStatus r.success
    returndata := obsReturndataOfWord r.returnValue
    logs := r.events.map (obsLogOfEncodedEvent emitter)
    storage := observableSlots.map fun slot =>
      ((IRStorageSlot.ofNat slot).toNat,
        (r.finalStorage (IRStorageSlot.ofNat slot)).toNat)
    transient := [] }

/-- Project a native `YulResult` onto `Obs` over `observableSlots`. -/
def yulResultToObs
    (emitter : Nat) (observableSlots : List Nat)
    (r : YulResult) : Obs :=
  { status := obsExecStatus r.success
    returndata := obsReturndataOfWord r.returnValue
    logs := r.events.map (obsLogOfEncodedEvent emitter)
    storage := observableSlots.map fun slot =>
      ((IRStorageSlot.ofNat slot).toNat,
        (r.finalStorage (IRStorageSlot.ofNat slot)).toNat)
    transient := [] }

/-- Native lowering + execution result satisfies `ObsEquiv` against an expected `Obs`. -/
def nativeResultObsEquiv
    (emitter : Nat) (observableSlots : List Nat) (expected : Obs)
    (native : Except NativeLoweringError YulResult) : Prop :=
  match native with
  | .ok yul => ObsEquiv expected (yulResultToObs emitter observableSlots yul)
  | .error _ => False

/-- `DenoteAgreement.denoteFunction_eq` lifts directly to exact `Obs` equality
and `ObsEquiv` on the event-free, byte-transport-free fragment. -/
theorem denoteResultToObs_eq_sourceResultToObs
    (emitter : Nat) (observableSlots : List Nat)
    (spec : CompilationModel.CompilationModel)
    (fn : CompilationModel.FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hnoEvents : spec.events = [])
    (hbyteFree : DenoteAgreement.stmtListByteFree fn.body = true) :
    denoteResultToObs emitter observableSlots
        (CompilationModel.Denote.denoteFunction DenoteAgreement.sourceOracle spec fn
          (DenoteAgreement.ofIRTransaction tx) initialWorld) =
      sourceResultToObs emitter observableSlots
        (SourceSemantics.interpretFunction spec fn tx initialWorld) := by
  unfold denoteResultToObs
  rw [DenoteAgreement.denoteFunction_eq spec fn tx initialWorld hnoEvents hbyteFree]

/-- Layer 1 (`Denote`) and `SourceSemantics` satisfy `ObsEquiv`. -/
theorem obsEquiv_denote_source
    (emitter : Nat) (observableSlots : List Nat)
    (spec : CompilationModel.CompilationModel)
    (fn : CompilationModel.FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hnoEvents : spec.events = [])
    (hbyteFree : DenoteAgreement.stmtListByteFree fn.body = true) :
    ObsEquiv
      (denoteResultToObs emitter observableSlots
        (CompilationModel.Denote.denoteFunction DenoteAgreement.sourceOracle spec fn
          (DenoteAgreement.ofIRTransaction tx) initialWorld))
      (sourceResultToObs emitter observableSlots
        (SourceSemantics.interpretFunction spec fn tx initialWorld)) := by
  rw [denoteResultToObs_eq_sourceResultToObs emitter observableSlots spec fn tx
    initialWorld hnoEvents hbyteFree]
  exact obsEquiv_refl _

/-- Layer 2 `sourceResultMatchesIRResult` implies exact `Obs` equality on any
`observableSlots` footprint. -/
theorem sourceResultToObs_eq_irResultToObs_of_matches
    (emitter : Nat) (observableSlots : List Nat)
    {source : SourceSemantics.SourceContractResult}
    {ir : IRResult}
    (hMatch : FunctionBody.sourceResultMatchesIRResult source ir) :
    sourceResultToObs emitter observableSlots source =
      irResultToObs emitter observableSlots ir := by
  rcases hMatch with ⟨hSuccess, hReturn, hStorage, hEvents⟩
  unfold sourceResultToObs irResultToObs
  rw [hSuccess, hReturn, hEvents, ← hStorage]

/-- Layer 2 `sourceResultMatchesIRResult` implies `ObsEquiv`. -/
theorem obsEquiv_source_ir_of_matches
    (emitter : Nat) (observableSlots : List Nat)
    {source : SourceSemantics.SourceContractResult}
    {ir : IRResult}
    (hMatch : FunctionBody.sourceResultMatchesIRResult source ir) :
    ObsEquiv
      (sourceResultToObs emitter observableSlots source)
      (irResultToObs emitter observableSlots ir) := by
  rw [sourceResultToObs_eq_irResultToObs_of_matches emitter observableSlots hMatch]
  exact obsEquiv_refl _

/-- Layer 3 `nativeResultsMatchOn` implies `nativeResultObsEquiv` against `irResultToObs`. -/
theorem nativeResultObsEquiv_ir_of_nativeResultsMatchOn
    (emitter : Nat) {observableSlots : List Nat}
    {ir : IRResult}
    {native : Except NativeLoweringError YulResult}
    (hMatch : nativeResultsMatchOn observableSlots ir native) :
    nativeResultObsEquiv emitter observableSlots
      (irResultToObs emitter observableSlots ir) native := by
  cases native with
  | error _ => cases hMatch
  | ok yul =>
      rcases hMatch with ⟨hSuccess, hReturn, hStorage, hEvents⟩
      have hMapEq :
          (observableSlots.map fun slot =>
            ((IRStorageSlot.ofNat slot).toNat,
              (ir.finalStorage (IRStorageSlot.ofNat slot)).toNat)) =
          (observableSlots.map fun slot =>
            ((IRStorageSlot.ofNat slot).toNat,
              (yul.finalStorage (IRStorageSlot.ofNat slot)).toNat)) := by
        apply List.map_congr_left
        intro slot hSlot
        rw [hStorage slot hSlot]
      have hEq : irResultToObs emitter observableSlots ir =
          yulResultToObs emitter observableSlots yul := by
        unfold irResultToObs yulResultToObs
        rw [hSuccess, hReturn, hEvents, hMapEq]
      unfold nativeResultObsEquiv
      rw [hEq]
      exact obsEquiv_refl _

/-- End-to-end `sourceResultMatchesNativeOn` implies `nativeResultObsEquiv`
against `sourceResultToObs`. -/
theorem nativeResultObsEquiv_source_of_sourceResultMatchesNativeOn
    (emitter : Nat) {observableSlots : List Nat}
    {source : SourceSemantics.SourceContractResult}
    {native : Except NativeLoweringError YulResult}
    (hMatch : sourceResultMatchesNativeOn observableSlots source native) :
    nativeResultObsEquiv emitter observableSlots
      (sourceResultToObs emitter observableSlots source) native := by
  cases native with
  | error _ => cases hMatch
  | ok yul =>
      rcases hMatch with ⟨hSuccess, hReturn, hStorage, hEvents⟩
      have hMapEq :
          (observableSlots.map fun slot =>
            ((IRStorageSlot.ofNat slot).toNat,
              (IRStorageWord.ofNat
                (source.finalStorage (IRStorageSlot.ofNat slot).toNat)).toNat)) =
          (observableSlots.map fun slot =>
            ((IRStorageSlot.ofNat slot).toNat,
              (yul.finalStorage (IRStorageSlot.ofNat slot)).toNat)) := by
        apply List.map_congr_left
        intro slot hSlot
        rw [hStorage slot hSlot]
      have hEq : sourceResultToObs emitter observableSlots source =
          yulResultToObs emitter observableSlots yul := by
        unfold sourceResultToObs yulResultToObs
        rw [hSuccess, hReturn, hEvents, hMapEq]
      unfold nativeResultObsEquiv
      rw [hEq]
      exact obsEquiv_refl _

/-- End-to-end `denoteResultMatchesNativeOn` implies `nativeResultObsEquiv`
against `denoteResultToObs`. -/
theorem nativeResultObsEquiv_denote_of_denoteResultMatchesNativeOn
    (emitter : Nat) {observableSlots : List Nat}
    {denote : CompilationModel.Denote.DenoteResult}
    {native : Except NativeLoweringError YulResult}
    (hMatch : denoteResultMatchesNativeOn observableSlots denote native) :
    nativeResultObsEquiv emitter observableSlots
      (denoteResultToObs emitter observableSlots denote) native :=
  nativeResultObsEquiv_source_of_sourceResultMatchesNativeOn emitter hMatch

/-- Composed Layer 2 + Layer 3 `ObsEquiv` preservation for any supported compiled
contract executed via `EvmYul.Yul.callDispatcher`. -/
theorem compile_preserves_obsEquiv_native_evmYulLean
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hUserBodyResult :
      NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx
        (FunctionBody.initialIRStateForTx spec tx initialWorld) observableSlots)
    (hEnv :
      Native.validateNativeRuntimeEnvironment
        (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) = .ok ()) :
    nativeResultObsEquiv tx.thisAddress observableSlots
      (sourceResultToObs tx.thisAddress observableSlots
        (supportedSourceContractSemantics spec selectors hSupported tx initialWorld))
      (Native.interpretIRRuntimeNative
        (Nat.succ (sizeOf (Compiler.emitYul irContract).runtimeCode))
        irContract tx (FunctionBody.initialIRStateForTx spec tx initialWorld)
        observableSlots) :=
  nativeResultObsEquiv_source_of_sourceResultMatchesNativeOn tx.thisAddress
    (compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher
      spec selectors hSupported irContract tx initialWorld observableSlots
      hcompile htxNormalized hcalldataSizeFits hSelectorRange hSelectorsRange
      hNoWrap hUserBodyResult hEnv)

end Compiler.Proofs.EndToEnd
