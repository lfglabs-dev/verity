/-
  Compiler.Proofs.EndToEnd: Composed Layers 2+3 Native End-to-End Theorem

  Composes the existing Layer 2 (CompilationModel -> IR) and native Layer 3
  preservation theorems into a single end-to-end result:

    For supported compiler output, native EVMYulLean runtime execution through
    `EvmYul.Yul.callDispatcher` matches the IR semantics on the observable
    result surface.

  This is the first step toward eliminating `interpretSpec` from the TCB
  (Issue #998). Once primitive-level EDSL ≡ compiled-Yul lemmas are proven,
  this end-to-end theorem provides the composition spine.

  **Architecture**:
  - Layer 2: `compile spec selectors = .ok irContract`
             `interpretIR irContract tx irState ≡ interpretSpec spec ...`
             (proven per-contract in Compiler/Proofs/IRGeneration/Expr.lean)
  - Native Layer 3: `interpretIR irContract tx irState` matches
             `interpretIRRuntimeNative fuel irContract tx irState observableSlots`
             through the native harness over `EvmYul.Yul.callDispatcher`.
  - This file: compose them into a single theorem statement.

  **EVMYulLean note (native transition)**: the active public native surface in
  this file is `nativeResultsMatchOn`, `sourceResultMatchesNativeOn`, and the
  concrete generated-dispatcher theorem family below them. The file-local
  runtime seams compare IR execution directly with native
  `EvmYul.Yul.callDispatcher` execution through
  `Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness`.

The removed backend-fuel transition target is not part of this public theorem
spine; this file composes only the native dispatcher result surface.

  Run: lake build Compiler.Proofs.EndToEnd
-/

import Compiler.Proofs.EndToEnd.DispatchConfig
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBodyClosure
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness
import Compiler.Proofs.YulGeneration.RuntimeTypes
import Compiler.Proofs.IRGeneration.Contract
import Compiler.Proofs.IRGeneration.ContractShape
import Compiler.Proofs.IRGeneration.FunctionShape
import Compiler.Proofs.IRGeneration.Expr
import Compiler.Proofs.IRGeneration.FunctionBody
import Compiler.Proofs.IRGeneration.DenoteFunctionAgreement
import Compiler.SimpleStorageNativeWitness

namespace Compiler.Proofs.EndToEnd

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends

/-! ## Native Runtime Result Surface -/

/-- Observable result comparison surface for native EVMYulLean execution. -/
abbrev nativeResultsMatchOn :=
  Compiler.Proofs.YulGeneration.Backends.Native.nativeResultsMatchOn

/-- Observable source-result comparison surface for native EVMYulLean execution.

This is the public composition target for source-level compiler correctness:
the storage comparison is intentionally projected to `observableSlots`, matching
the native harness' materialized-storage boundary. -/
def sourceResultMatchesNativeOn
    (observableSlots : List Nat)
    (source : SourceSemantics.SourceContractResult)
    (native : Except Compiler.Proofs.YulGeneration.Backends.NativeLoweringError YulResult) :
    Prop :=
  match native with
  | .ok yul =>
      source.success = yul.success ∧
      source.returnValue = yul.returnValue ∧
      (∀ slot, slot ∈ observableSlots →
        IRStorageWord.ofNat
            (source.finalStorage (IRStorageSlot.ofNat slot).toNat) =
          yul.finalStorage (IRStorageSlot.ofNat slot)) ∧
      source.events = yul.events
  | .error _ => False

/-- Compose Layer 2 source-to-IR correctness with native EVMYulLean runtime
correctness. -/
theorem sourceResultMatchesNativeOn_of_sourceResultMatchesIRResult_of_nativeResultsMatchOn
    {observableSlots : List Nat}
    {source : SourceSemantics.SourceContractResult}
    {ir : IRResult}
    {native : Except Compiler.Proofs.YulGeneration.Backends.NativeLoweringError YulResult}
    (hSourceIR :
      Compiler.Proofs.IRGeneration.FunctionBody.sourceResultMatchesIRResult
        source ir)
    (hNativeIR :
      nativeResultsMatchOn observableSlots ir native) :
    sourceResultMatchesNativeOn observableSlots source native := by
  cases native with
  | error err =>
      cases hNativeIR
  | ok yul =>
      rcases hSourceIR with ⟨hSourceSuccess, hSourceReturn, hSourceStorage, hSourceEvents⟩
      rcases hNativeIR with ⟨hNativeSuccess, hNativeReturn, hNativeStorage, hNativeEvents⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hSourceSuccess.trans hNativeSuccess
      · exact hSourceReturn.trans hNativeReturn
      · intro slot hslot
        have hStorageAt :=
          congrArg (fun f => f (IRStorageSlot.ofNat slot)) hSourceStorage
        exact hStorageAt.trans (hNativeStorage slot hslot)
      · exact hSourceEvents.trans hNativeEvents

/-- Layer II corollary specializing `evalParametricRuntimeDispatch_matches_ir`
to `FunctionBody.sourceResultMatchesIRResult` for any `cfg : DispatchConfig`. -/
theorem parametric_runtime_dispatch_matches_ir
    (cfg : DispatchConfig)
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {fallbackSpec receiveSpec : Option CompilationModel.FunctionSpec}
    {ir : IRContract} {tx : IRTransaction}
    {revertSrc : SourceSemantics.SourceContractResult} {revertIR : IRResult}
    {execFn execEp : CompilationModel.FunctionSpec → SourceSemantics.SourceContractResult}
    {execIRFn : IRFunction → IRResult} {execIREp : IREntrypoint → IRResult}
    (hAlign : ParametricDispatchAlignment FunctionBody.sourceResultMatchesIRResult
      spec selectors fallbackSpec receiveSpec ir tx
      revertSrc revertIR execFn execEp execIRFn execIREp) :
    FunctionBody.sourceResultMatchesIRResult
      (evalParametricRuntimeDispatch cfg spec selectors
        fallbackSpec receiveSpec tx revertSrc execFn execEp)
      (evalParametricIRRuntimeDispatch cfg ir tx
        revertIR execIRFn execIREp) :=
  evalParametricRuntimeDispatch_matches_ir cfg hAlign

/-- Qualified `DispatchConfig` alias for `evalParametricRuntimeDispatch_matches_ir`. -/
theorem DispatchConfig.evalParametricRuntimeDispatch_matches_ir
    (cfg : DispatchConfig)
    {SrcResult IRRes : Type} {R : SrcResult → IRRes → Prop}
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {fallbackSpec receiveSpec : Option CompilationModel.FunctionSpec}
    {ir : IRContract} {tx : IRTransaction}
    {revertSrc : SrcResult} {revertIR : IRRes}
    {execFn execEp : CompilationModel.FunctionSpec → SrcResult}
    {execIRFn : IRFunction → IRRes} {execIREp : IREntrypoint → IRRes}
    (hAlign : ParametricDispatchAlignment R spec selectors fallbackSpec receiveSpec
      ir tx revertSrc revertIR execFn execEp execIRFn execIREp) :
    R (evalParametricRuntimeDispatch cfg spec selectors
        fallbackSpec receiveSpec tx revertSrc execFn execEp)
      (evalParametricIRRuntimeDispatch cfg ir tx
        revertIR execIRFn execIREp) :=
  Compiler.Proofs.EndToEnd.evalParametricRuntimeDispatch_matches_ir cfg hAlign

/-- Qualified `DispatchConfig` alias for `parametric_runtime_dispatch_matches_ir`. -/
theorem DispatchConfig.parametric_runtime_dispatch_matches_ir
    (cfg : DispatchConfig)
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {fallbackSpec receiveSpec : Option CompilationModel.FunctionSpec}
    {ir : IRContract} {tx : IRTransaction}
    {revertSrc : SourceSemantics.SourceContractResult} {revertIR : IRResult}
    {execFn execEp : CompilationModel.FunctionSpec → SourceSemantics.SourceContractResult}
    {execIRFn : IRFunction → IRResult} {execIREp : IREntrypoint → IRResult}
    (hAlign : ParametricDispatchAlignment FunctionBody.sourceResultMatchesIRResult
      spec selectors fallbackSpec receiveSpec ir tx
      revertSrc revertIR execFn execEp execIRFn execIREp) :
    FunctionBody.sourceResultMatchesIRResult
      (evalParametricRuntimeDispatch cfg spec selectors
        fallbackSpec receiveSpec tx revertSrc execFn execEp)
      (evalParametricIRRuntimeDispatch cfg ir tx
        revertIR execIRFn execIREp) :=
  Compiler.Proofs.EndToEnd.parametric_runtime_dispatch_matches_ir cfg hAlign

/-- Layer II+III corollary composing `parametric_runtime_dispatch_matches_ir`
with `nativeResultsMatchOn` into `sourceResultMatchesNativeOn`. -/
theorem parametric_runtime_dispatch_matches_native
    (cfg : DispatchConfig)
    {observableSlots : List Nat}
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {fallbackSpec receiveSpec : Option CompilationModel.FunctionSpec}
    {ir : IRContract} {tx : IRTransaction}
    {revertSrc : SourceSemantics.SourceContractResult} {revertIR : IRResult}
    {execFn execEp : CompilationModel.FunctionSpec → SourceSemantics.SourceContractResult}
    {execIRFn : IRFunction → IRResult} {execIREp : IREntrypoint → IRResult}
    {native : Except Compiler.Proofs.YulGeneration.Backends.NativeLoweringError YulResult}
    (hAlign : ParametricDispatchAlignment FunctionBody.sourceResultMatchesIRResult
      spec selectors fallbackSpec receiveSpec ir tx
      revertSrc revertIR execFn execEp execIRFn execIREp)
    (hNative : nativeResultsMatchOn observableSlots
      (evalParametricIRRuntimeDispatch cfg ir tx revertIR execIRFn execIREp) native) :
    sourceResultMatchesNativeOn observableSlots
      (evalParametricRuntimeDispatch cfg spec selectors
        fallbackSpec receiveSpec tx revertSrc execFn execEp)
      native :=
  sourceResultMatchesNativeOn_of_sourceResultMatchesIRResult_of_nativeResultsMatchOn
    (parametric_runtime_dispatch_matches_ir cfg hAlign) hNative

/-- Observable denote-result comparison surface for native EVMYulLean
execution: the compiler-free denotation's observable result, compared on the
same projected-storage boundary as `sourceResultMatchesNativeOn`. -/
def denoteResultMatchesNativeOn
    (observableSlots : List Nat)
    (denote : CompilationModel.Denote.DenoteResult)
    (native : Except Compiler.Proofs.YulGeneration.Backends.NativeLoweringError YulResult) :
    Prop :=
  sourceResultMatchesNativeOn observableSlots
    (DenoteAgreement.toSourceResult denote) native

/-- Compose function-level denote/source agreement with source-to-native
correctness: on the event-free, byte-transport-free fragment, the compiler-free
denotation of a function matches native execution whenever the trusted source
interpretation does. -/
theorem denoteResultMatchesNativeOn_of_sourceResultMatchesNativeOn
    {observableSlots : List Nat}
    {spec : CompilationModel.CompilationModel}
    {fn : CompilationModel.FunctionSpec}
    {tx : IRTransaction}
    {initialWorld : Verity.ContractState}
    {native : Except Compiler.Proofs.YulGeneration.Backends.NativeLoweringError YulResult}
    (hnoEvents : spec.events = [])
    (hbyteFree : DenoteAgreement.stmtListByteFree fn.body = true)
    (hSource :
      sourceResultMatchesNativeOn observableSlots
        (SourceSemantics.interpretFunction spec fn tx initialWorld) native) :
    denoteResultMatchesNativeOn observableSlots
      (CompilationModel.Denote.denoteFunction DenoteAgreement.sourceOracle spec fn
        (DenoteAgreement.ofIRTransaction tx) initialWorld)
      native := by
  unfold denoteResultMatchesNativeOn
  rw [DenoteAgreement.denoteFunction_eq spec fn tx initialWorld hnoEvents hbyteFree]
  exact hSource

/-- Package the generated selector-hit success conditions into
`DispatchGuardsSafe`. -/
theorem DispatchGuardsSafe.of_value_safe_of_args_le_of_noWrap
    (fn : IRFunction) (tx : IRTransaction)
    (hValue : fn.payable = true ∨
      tx.msgValue % Compiler.Constants.evmModulus = 0)
    (hArgs : fn.params.length ≤ tx.args.length)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    DispatchGuardsSafe fn tx := by
  refine ⟨hValue, ?_⟩
  have hMul : fn.params.length * 32 ≤ tx.args.length * 32 :=
    Nat.mul_le_mul_right 32 hArgs
  have hAdd : 4 + fn.params.length * 32 ≤ 4 + tx.args.length * 32 :=
    Nat.add_le_add_left hMul 4
  exact lt_of_le_of_lt hAdd (by
    simpa [Compiler.Constants.evmModulus, EvmYul.UInt256.size] using hNoWrap)

/-- Package value-safety with the generated calldata-threshold bound into
`DispatchGuardsSafe`.

This is useful for generated guard-failure splits: the short-calldata branch
cannot derive the selected function's threshold from transaction calldata
length, but it also does not need any argument-availability fact. -/
theorem DispatchGuardsSafe.of_value_safe_of_threshold
    (fn : IRFunction) (tx : IRTransaction)
    (hValue : fn.payable = true ∨
      tx.msgValue % Compiler.Constants.evmModulus = 0)
    (hThreshold : 4 + fn.params.length * 32 < EvmYul.UInt256.size) :
    DispatchGuardsSafe fn tx :=
  ⟨hValue, by
    simpa [Compiler.Constants.evmModulus, EvmYul.UInt256.size] using
      hThreshold⟩

private theorem compiledFunctionCalldataThreshold_of_forall₂
    (spec : CompilationModel.CompilationModel)
    (tx : IRTransaction)
    (hSourceThreshold :
      ∀ fn, fn ∈ selectorDispatchedFunctions spec →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    {pairs : List (CompilationModel.FunctionSpec × Nat)}
    {irFns : List IRFunction}
    (hPairsMem :
      ∀ entry, entry ∈ pairs → entry.1 ∈ selectorDispatchedFunctions spec)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          CompilationModel.compileFunctionSpec spec.fields spec.events
            spec.errors [] entry.2 entry.1 = Except.ok irFn)
        pairs irFns)
    (irFn : IRFunction)
    (hFind :
      irFns.find? (fun fn => fn.selector == tx.functionSelector) =
        some irFn) :
    4 + irFn.params.length * 32 < EvmYul.UInt256.size := by
  induction hcompiled with
  | nil =>
      simp at hFind
  | @cons entry headIr tailPairs tailIr hhead htail ih =>
      by_cases hSelector : headIr.selector = tx.functionSelector
      · simp [hSelector] at hFind
        rcases hFind with rfl
        have hParams :
            headIr.params =
              entry.1.params.map CompilationModel.Param.toIRParam :=
          Compiler.Proofs.IRGeneration.Function.compileFunctionSpec_ok_params
            spec.fields spec.events spec.errors entry.2 entry.1 headIr hhead
        have hLen : headIr.params.length = entry.1.params.length := by
          simp [hParams]
        rw [hLen]
        exact hSourceThreshold entry.1 (hPairsMem entry (by simp))
      · have hFindTail :
            tailIr.find? (fun fn => fn.selector == tx.functionSelector) =
              some irFn := by
          simpa [hSelector] using hFind
        exact ih
          (fun entry' hMem =>
            hPairsMem entry' (by simp [hMem]))
          hFindTail

theorem generatedFunctionCalldataThreshold_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (irFn : IRFunction)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some irFn) :
    4 + irFn.params.length * 32 < EvmYul.UInt256.size := by
  have hcompiled :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions
      spec selectors hSupported irContract hcompile
  exact
    compiledFunctionCalldataThreshold_of_forall₂ spec tx
      (fun fn hfn => by
        simpa [Compiler.Constants.evmModulus, EvmYul.UInt256.size] using
          hSupported.selectorFunctionParamCalldataThreshold hfn)
      (pairs := SourceSemantics.selectorFunctionPairs spec selectors)
      (irFns := irContract.functions)
      (fun entry hMem =>
        by
          simpa [SourceSemantics.selectorFunctionPairs] using
            (List.of_mem_zip hMem).1)
      hcompiled irFn hFind

/-- Positive-fuel raw native dispatcher-exec target against IR directly. -/
def nativeDispatcherExecMatchesIRPositive
    (fuel' : Nat)
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract) :
    Prop :=
  let initial := Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
      (YulTransaction.ofIR tx) state.storage
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode contract) observableSlots)
  let nativeResult :=
    match
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        fuel' nativeContract initial with
    | .error err => .error err
    | .ok finalState =>
        let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
        .ok (restored, [])
  nativeResultsMatchOn observableSlots (interpretIR contract tx state)
    (.ok
      (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events nativeResult))

/-- File-local canonical generated-runtime dispatcher-exec target against IR.

This is retained as transition evidence for older internal wrappers. Public
source-level theorems should target the projected `callDispatcher` result or
the newer positive/projected dispatcher packages instead. -/
private def nativeGeneratedDispatcherExecMatchesIROn
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract) :
    Prop :=
  let fuel' := sizeOf (Compiler.emitYul contract).runtimeCode
  let initial := Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
      (YulTransaction.ofIR tx) state.storage
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode contract) observableSlots)
  let nativeResult :=
    match
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        fuel' nativeContract initial with
    | .error err => .error err
    | .ok finalState =>
        let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
        .ok (restored, [])
  nativeResultsMatchOn observableSlots (interpretIR contract tx state)
    (.ok
      (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events nativeResult))

/-- Public canonical generated-runtime `EvmYul.Yul.callDispatcher` result.

The lowered generated runtime is installed in an EVMYulLean state and run
through `callDispatcher` at canonical generated-runtime fuel, then projected
onto the proof-side observable Yul result surface. -/
noncomputable def nativeGeneratedCallDispatcherResultOf
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract) :
    Except Compiler.Proofs.YulGeneration.Backends.NativeLoweringError YulResult :=
  let fuel := Nat.succ (sizeOf (Compiler.emitYul contract).runtimeCode)
  let initial := Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
      (YulTransaction.ofIR tx) state.storage
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode contract) observableSlots)
  .ok
    (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      (YulTransaction.ofIR tx) state.storage state.events
      (EvmYul.Yul.callDispatcher fuel (some nativeContract) initial))

/-- File-local canonical generated-runtime `EvmYul.Yul.callDispatcher` target
against IR.

This is the direct native entrypoint-facing form of
`nativeGeneratedDispatcherExecMatchesIROn`: the lowered generated runtime is
installed in an EVMYulLean state and run through `callDispatcher` at canonical
generated-runtime fuel. -/
private def nativeGeneratedCallDispatcherMatchesIROn
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract) :
    Prop :=
  nativeResultsMatchOn observableSlots (interpretIR contract tx state)
    (nativeGeneratedCallDispatcherResultOf contract tx state observableSlots
      nativeContract)

private theorem nativeGeneratedCallDispatcherMatchesIROn_of_dispatcherExec
    {contract : IRContract} {tx : IRTransaction} {state : IRState}
    {observableSlots : List Nat} {nativeContract : EvmYul.Yul.Ast.YulContract}
    (hMatch :
      nativeGeneratedDispatcherExecMatchesIROn contract tx state
        observableSlots nativeContract) :
    nativeGeneratedCallDispatcherMatchesIROn contract tx state observableSlots
      nativeContract := by
  let initial :=
    Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
      (YulTransaction.ofIR tx) state.storage
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode contract) observableSlots)
  have hCall : EvmYul.Yul.callDispatcher
          (Nat.succ (sizeOf (Compiler.emitYul contract).runtimeCode)) (some nativeContract) initial =
        match
          Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
            (sizeOf (Compiler.emitYul contract).runtimeCode)
            nativeContract initial with
        | .error err => .error err
        | .ok finalState =>
            let restored :=
              finalState.reviveJump.overwrite? initial |>.setStore initial
            .ok (restored, []) := by
    rw [
      Compiler.Proofs.YulGeneration.Backends.Native.callDispatcher_succ_eq_callDispatcherBlockResult,
      show initial =
          Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
            (YulTransaction.ofIR tx) state.storage
            (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
              (Compiler.runtimeCode contract) observableSlots) by rfl,
      Compiler.Proofs.YulGeneration.Backends.Native.callDispatcherBlockResult_initialState_eq_contractDispatcherBlockResult,
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherBlockResult_eq_execResult]
    simp [EvmYul.Yul.Ast.FunctionDefinition.rets]
    rfl
  unfold nativeGeneratedCallDispatcherMatchesIROn
  simp only [nativeGeneratedCallDispatcherResultOf]
  change nativeResultsMatchOn observableSlots (interpretIR contract tx state)
    (.ok
      (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events
        (EvmYul.Yul.callDispatcher
          (Nat.succ (sizeOf (Compiler.emitYul contract).runtimeCode))
          (some nativeContract) initial)))
  rw [hCall]
  unfold nativeGeneratedDispatcherExecMatchesIROn at hMatch
  simpa [initial] using hMatch

/-- Re-target a native result match from the selected IR function body to the
top-level IR interpreter, once selector-hit success guards are known. -/
theorem nativeResultsMatchOn_interpretIR_of_execIRFunction_guards
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (fn : IRFunction)
    (native : Except Compiler.Proofs.YulGeneration.Backends.NativeLoweringError
      YulResult)
    (hFind :
      contract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn)
    (hValue :
      fn.payable = false →
        tx.msgValue % Compiler.Constants.evmModulus = 0)
    (hArgs : fn.params.length ≤ tx.args.length)
    (hMatch :
      nativeResultsMatchOn observableSlots
        (execIRFunction fn tx.args (applyIRTransactionContext tx state))
        native) :
    nativeResultsMatchOn observableSlots (interpretIR contract tx state)
      native := by
  rw [interpretIR_eq_execIRFunction_of_find?_some_guards
    contract tx state fn hFind hValue hArgs]
  exact hMatch

/-- `DispatchGuardsSafe`-flavored retargeting from selected function-body IR
semantics to the top-level IR interpreter. -/
theorem nativeResultsMatchOn_interpretIR_of_execIRFunction_dispatchGuards
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (fn : IRFunction)
    (native : Except Compiler.Proofs.YulGeneration.Backends.NativeLoweringError
      YulResult)
    (hFind :
      contract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn)
    (hguards : DispatchGuardsSafe fn tx)
    (hArgs : fn.params.length ≤ tx.args.length)
    (hMatch :
      nativeResultsMatchOn observableSlots
        (execIRFunction fn tx.args (applyIRTransactionContext tx state))
        native) :
    nativeResultsMatchOn observableSlots (interpretIR contract tx state)
      native :=
  nativeResultsMatchOn_interpretIR_of_execIRFunction_guards
    contract tx state observableSlots fn native hFind
    (fun hNonPayable =>
      Compiler.Proofs.YulGeneration.Backends.Native.DispatchGuardsSafe_msgValue_zero_mod_of_nonpayable
        fn tx hguards hNonPayable)
    hArgs hMatch

/-- Native observable match for the selected-function non-payable value guard
revert. This is the IR-side target needed by the generated native
`callvalue()` guard-failure branch. -/
theorem nativeResultsMatchOn_interpretIR_revert_of_nonpayable_nonzero
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (fn : IRFunction)
    (hFind :
      contract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn)
    (hNonPayable : fn.payable = false)
    (hNonzero : tx.msgValue % Compiler.Constants.evmModulus ≠ 0) :
    nativeResultsMatchOn observableSlots (interpretIR contract tx state)
      (.ok
        { success := false
          returnValue := none
          finalStorage := state.storage
          finalMappings := Compiler.Proofs.storageAsMappings state.storage
          events := state.events }) := by
  rw [interpretIR_eq_revert_of_find?_some_nonpayable_nonzero
    contract tx state fn hFind hNonPayable hNonzero]
  simp [nativeResultsMatchOn,
    Compiler.Proofs.YulGeneration.Backends.Native.nativeResultsMatchOn]

/-- Native observable match for the selected-function calldata arity guard
revert. This is the IR-side target needed by the generated native
`calldatasize()` guard-failure branch. -/
theorem nativeResultsMatchOn_interpretIR_revert_of_args_short
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (fn : IRFunction)
    (hFind :
      contract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn)
    (hValue :
      fn.payable = true ∨
        tx.msgValue % Compiler.Constants.evmModulus = 0)
    (hArgsShort : ¬ fn.params.length ≤ tx.args.length) :
    nativeResultsMatchOn observableSlots (interpretIR contract tx state)
      (.ok
        { success := false
          returnValue := none
          finalStorage := state.storage
          finalMappings := Compiler.Proofs.storageAsMappings state.storage
          events := state.events }) := by
  rw [interpretIR_eq_revert_of_find?_some_args_short
    contract tx state fn hFind hValue hArgsShort]
  simp [nativeResultsMatchOn,
    Compiler.Proofs.YulGeneration.Backends.Native.nativeResultsMatchOn]

/-- Projected native `Revert` result matches the selected-function non-payable
value guard failure in `interpretIR`. -/
theorem nativeResultsMatchOn_projectResult_revert_of_nonpayable_nonzero
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (fn : IRFunction)
    (hFind :
      contract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn)
    (hNonPayable : fn.payable = false)
    (hNonzero : tx.msgValue % Compiler.Constants.evmModulus ≠ 0) :
    nativeResultsMatchOn observableSlots (interpretIR contract tx state)
      (.ok
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events
          (.error EvmYul.Yul.Exception.Revert))) := by
  simpa using
    (nativeResultsMatchOn_interpretIR_revert_of_nonpayable_nonzero
      contract tx state observableSlots fn hFind hNonPayable hNonzero)

/-- Projected native `Revert` result matches the selected-function calldata
arity guard failure in `interpretIR`. -/
theorem nativeResultsMatchOn_projectResult_revert_of_args_short
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (fn : IRFunction)
    (hFind :
      contract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn)
    (hValue :
      fn.payable = true ∨
        tx.msgValue % Compiler.Constants.evmModulus = 0)
    (hArgsShort : ¬ fn.params.length ≤ tx.args.length) :
    nativeResultsMatchOn observableSlots (interpretIR contract tx state)
      (.ok
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events
          (.error EvmYul.Yul.Exception.Revert))) := by
  simpa using
    (nativeResultsMatchOn_interpretIR_revert_of_args_short
      contract tx state observableSlots fn hFind hValue hArgsShort)

/-- Public native contract shell produced by helper-free generated dispatcher
lowering. -/
def nativeGeneratedDispatcherContractOf
    (dispatcher : List EvmYul.Yul.Ast.Stmt) :
    EvmYul.Yul.Ast.YulContract :=
  { dispatcher := .Block dispatcher
    functions :=
      (∅ : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap) }

/-- Public native contract shell produced by generated dispatcher lowering
when the runtime includes the native `mappingSlot` helper. -/
def nativeGeneratedDispatcherContractWithMappingOf
    (dispatcher : List EvmYul.Yul.Ast.Stmt) :
    EvmYul.Yul.Ast.YulContract :=
  { dispatcher := .Block dispatcher
    functions :=
      ((∅ : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap).insert
        "mappingSlot"
        Compiler.Proofs.YulGeneration.Backends.Native.nativeMappingSlotFunctionDefinition) }

/-- Canonical native dispatcher fuel for the generated runtime surface. -/
private noncomputable abbrev nativeRuntimeDispatcherFuel (contract : IRContract) : Nat :=
  sizeOf (Compiler.emitYul contract).runtimeCode

private theorem sizeOf_list_ge_length {α : Type _} [SizeOf α] (xs : List α) :
    sizeOf xs ≥ xs.length + 1 := by
  induction xs with
  | nil =>
      simp
  | cons _ xs ih =>
      simp
      omega

/-- Mapping `dispatchBody` with `calldatasizeGuard` over `fns` matches `buildSwitchSourceCases`. -/
private theorem buildSwitch_cases_eq_buildSwitchSourceCases (fns : List IRFunction) :
    (fns.map (fun fn =>
      (fn.selector,
        Compiler.CodegenCommon.dispatchBody fn.payable s!"{fn.name}()"
          ([Compiler.CodegenCommon.calldatasizeGuard fn.params.length] ++
            fn.body)))) =
      Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases fns := by
  induction fns with
  | nil =>
      simp [Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases]
  | cons fn rest ih =>
      cases hpay : fn.payable <;>
        simp [Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases,
          Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody,
          Compiler.CodegenCommon.dispatchBody,
          Compiler.CodegenCommon.callvalueGuard,
          Compiler.CodegenCommon.calldatasizeGuard, hpay]

private theorem sizeOf_buildSwitch_noFallback_noReceive_ge_source_cases_length_plus24
    (fns : List IRFunction) :
    sizeOf [Compiler.CodegenCommon.buildSwitch fns none none] ≥
      (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
        fns).length + 24 := by
  unfold Compiler.CodegenCommon.buildSwitch
  simp only [ite_false, Bool.false_eq_true,
    Compiler.CodegenCommon.defaultDispatchCase]
  rw [buildSwitch_cases_eq_buildSwitchSourceCases fns]
  have hLen :=
    sizeOf_list_ge_length
      (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases fns)
  set cases :=
    Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases fns
  set defaultStmts : List Compiler.Yul.YulStmt :=
    [Compiler.Yul.YulStmt.exprStmt
      (Compiler.Yul.YulExpr.call "revert"
        [Compiler.Yul.YulExpr.lit 0, Compiler.Yul.YulExpr.lit 0])]
  set sw := Compiler.Yul.YulStmt.switch
    (Compiler.Yul.YulExpr.call "shr"
      [Compiler.Yul.YulExpr.lit Compiler.Constants.selectorShift,
       Compiler.Yul.YulExpr.call "calldataload" [Compiler.Yul.YulExpr.lit 0]])
    cases (some defaultStmts)
  set if2 := Compiler.Yul.YulStmt.if_
    (Compiler.Yul.YulExpr.ident "__has_selector") [sw]
  let block := Compiler.Yul.YulStmt.block
    [Compiler.Yul.YulStmt.let_ "__has_selector"
      (Compiler.Yul.YulExpr.call "iszero"
        [Compiler.Yul.YulExpr.call "lt"
          [Compiler.Yul.YulExpr.call "calldatasize" [],
           Compiler.Yul.YulExpr.lit 4]]),
     Compiler.Yul.YulStmt.if_
      (Compiler.Yul.YulExpr.call "iszero"
        [Compiler.Yul.YulExpr.ident "__has_selector"]) defaultStmts,
     if2]
  have hBlock : sizeOf block ≥ 23 + sizeOf cases := by
    simp [block, if2, sw]; omega
  have hBlockLen : cases.length + 24 ≤ sizeOf block := by omega
  have hList : sizeOf block ≤ sizeOf [block] := by simp; omega
  exact Nat.le_trans hBlockLen hList

private theorem sizeOf_emitYul_runtimeCode_noMapping_ge_lowered_cases_length_plus24
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    {reservedNames : List String} {n0 : Nat}
    {cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)} {midN : Nat}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hNoMapping : irContract.usesMapping = false)
    (hLowerCases :
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
        reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
          reservedNames n0 + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions) = .ok (cases', midN)) :
    cases'.length + 24 ≤
      sizeOf (Compiler.emitYul irContract).runtimeCode := by
  have hRuntime :
      (Compiler.emitYul irContract).runtimeCode =
        [Compiler.CodegenCommon.initFreeMemoryPointer,
          Compiler.CodegenCommon.buildSwitch irContract.functions none none] :=
    Compiler.Proofs.YulGeneration.Backends.Native.emitYul_runtimeCode_eq_single_dispatcher_of_noMapping_noInternals_noFallback_noReceive
      irContract hNoMapping
      (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_internalFunctions_nil
        (model := spec) (selectors := selectors) (hSupported := hSupported)
        (ir := irContract) (hcompile := hCompile))
      (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noFallbackEntrypoint
        spec selectors hSupported irContract hCompile)
      (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noReceiveEntrypoint
        spec selectors hSupported irContract hCompile)
  have hLen :
      cases'.length =
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions).length :=
    Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds_length_eq
      reservedNames
      (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
        reservedNames n0 + 1)
      midN
      (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
        irContract.functions) cases' hLowerCases
  have hSize :=
    sizeOf_buildSwitch_noFallback_noReceive_ge_source_cases_length_plus24
      irContract.functions
  rw [hRuntime, hLen]
  simp [Compiler.CodegenCommon.initFreeMemoryPointer] at hSize ⊢
  omega

private theorem sizeOf_emitYul_runtimeCode_noMapping_ge_lowered_cases_length_plus25
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    {reservedNames : List String} {n0 : Nat}
    {cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)} {midN : Nat}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hNoMapping : irContract.usesMapping = false)
    (hLowerCases :
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
        reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
          reservedNames n0 + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions) = .ok (cases', midN)) :
    cases'.length + 25 ≤
      sizeOf (Compiler.emitYul irContract).runtimeCode := by
  have hRuntime :
      (Compiler.emitYul irContract).runtimeCode =
        [Compiler.CodegenCommon.initFreeMemoryPointer,
          Compiler.CodegenCommon.buildSwitch irContract.functions none none] :=
    Compiler.Proofs.YulGeneration.Backends.Native.emitYul_runtimeCode_eq_single_dispatcher_of_noMapping_noInternals_noFallback_noReceive
      irContract hNoMapping
      (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_internalFunctions_nil
        (model := spec) (selectors := selectors) (hSupported := hSupported)
        (ir := irContract) (hcompile := hCompile))
      (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noFallbackEntrypoint
        spec selectors hSupported irContract hCompile)
      (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noReceiveEntrypoint
        spec selectors hSupported irContract hCompile)
  have hLen :
      cases'.length =
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions).length :=
    Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds_length_eq
      reservedNames
      (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
        reservedNames n0 + 1)
      midN
      (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
        irContract.functions) cases' hLowerCases
  have hSize :=
    sizeOf_buildSwitch_noFallback_noReceive_ge_source_cases_length_plus24
      irContract.functions
  rw [hRuntime, hLen]
  simp [Compiler.CodegenCommon.initFreeMemoryPointer] at hSize ⊢
  omega

/-- For mapping-enabled supported contracts, emitted runtime code consists of
`mappingSlotFuncAt 0`, `initFreeMemoryPointer`, and the generated selector switch. -/
private theorem emitYul_runtimeCode_mapping_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hMapping : irContract.usesMapping = true) :
    (Compiler.emitYul irContract).runtimeCode =
      [Compiler.CodegenCommon.mappingSlotFuncAt 0,
        Compiler.CodegenCommon.initFreeMemoryPointer,
        Compiler.CodegenCommon.buildSwitch irContract.functions none none] := by
  have hInternals : irContract.internalFunctions = [] :=
    Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_internalFunctions_nil
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  have hNoFallback : irContract.fallbackEntrypoint = none :=
    Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noFallbackEntrypoint
      spec selectors hSupported irContract hCompile
  have hNoReceive : irContract.receiveEntrypoint = none :=
    Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noReceiveEntrypoint
      spec selectors hSupported irContract hCompile
  unfold Compiler.emitYul Compiler.CodegenCommon.emitYul
    Compiler.CodegenCommon.runtimeCode
  simp [hMapping, hInternals, hNoFallback, hNoReceive]

private theorem sizeOf_emitYul_runtimeCode_mapping_ge_lowered_cases_length_plus24
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    {reservedNames : List String} {switchStart : Nat}
    {cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)} {midN : Nat}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hMapping : irContract.usesMapping = true)
    (hLowerCases :
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
        reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
          reservedNames switchStart + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions) = .ok (cases', midN)) :
    cases'.length + 24 ≤
      sizeOf (Compiler.emitYul irContract).runtimeCode := by
  have hRuntime :=
    emitYul_runtimeCode_mapping_of_compile_ok_supported hCompile hSupported hMapping
  have hLen :
      cases'.length =
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions).length :=
    Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds_length_eq
      reservedNames
      (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
        reservedNames switchStart + 1)
      midN
      (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
        irContract.functions) cases' hLowerCases
  have hSize :=
    sizeOf_buildSwitch_noFallback_noReceive_ge_source_cases_length_plus24
      irContract.functions
  rw [hRuntime, hLen]
  refine Nat.le_trans hSize ?_
  simp only [Compiler.CodegenCommon.mappingSlotFuncAt]
  simp [Compiler.CodegenCommon.initFreeMemoryPointer]
  omega

private theorem sizeOf_emitYul_runtimeCode_mapping_ge_lowered_cases_length_plus25
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    {reservedNames : List String} {switchStart : Nat}
    {cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)} {midN : Nat}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hMapping : irContract.usesMapping = true)
    (hLowerCases :
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
        reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
          reservedNames switchStart + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions) = .ok (cases', midN)) :
    cases'.length + 25 ≤
      sizeOf (Compiler.emitYul irContract).runtimeCode := by
  have hRuntime :=
    emitYul_runtimeCode_mapping_of_compile_ok_supported hCompile hSupported hMapping
  have hLen :
      cases'.length =
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions).length :=
    Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds_length_eq
      reservedNames
      (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
        reservedNames switchStart + 1)
      midN
      (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
        irContract.functions) cases' hLowerCases
  have hSize :=
    sizeOf_buildSwitch_noFallback_noReceive_ge_source_cases_length_plus24
      irContract.functions
  rw [hRuntime, hLen]
  simp only [Compiler.CodegenCommon.mappingSlotFuncAt]
  simp [Compiler.CodegenCommon.initFreeMemoryPointer] at hSize ⊢
  have hExtra : 1 ≤ sizeOf "mappingSlot" := by decide
  omega

/-- Projected native dispatcher-exec result equality used by the public native
EndToEnd theorems.

This is a result-shape obligation, not a dispatcher-vs-IR semantic premise: it
states that the native dispatcher execution at `fuel'`, after the standard
jump/store restoration and projection, yields the supplied `YulResult`. -/
abbrev nativeProjectedDispatcherResultEq
    (fuel' : Nat) (contract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract) (nativeYul : YulResult) :
    Prop :=
  let initial :=
    Compiler.Proofs.YulGeneration.Backends.Native.initialState
      nativeContract (YulTransaction.ofIR tx) state.storage
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode contract) observableSlots)
  let nativeResult :=
    match Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        fuel' nativeContract initial with
    | .error err => .error err
    | .ok finalState =>
        let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
        .ok (restored, [])
  Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      (YulTransaction.ofIR tx) state.storage state.events nativeResult =
    nativeYul

/-- Unfolded equality form of `nativeProjectedDispatcherResultEq` for rewriting
inside `nativeDispatcherExecMatchesIRPositive`. -/
private theorem nativeProjectedDispatcherResultEq_unfold
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract} {nativeYul : YulResult}
    (hProject : nativeProjectedDispatcherResultEq fuel' contract tx state
      observableSlots nativeContract nativeYul) :
    (let initial :=
      Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
        (YulTransaction.ofIR tx) state.storage
        (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
          (Compiler.runtimeCode contract) observableSlots)
    let nativeResult :=
      match
        Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          fuel' nativeContract initial with
      | .error err => .error err
      | .ok finalState =>
          let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
          .ok (restored, [])
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      (YulTransaction.ofIR tx) state.storage state.events nativeResult) =
      nativeYul := by
  simpa [nativeProjectedDispatcherResultEq] using hProject

theorem nativeDispatcherExecMatchesIRPositive_of_project_eq_match
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    {nativeYul : YulResult}
    (hProject : nativeProjectedDispatcherResultEq fuel' contract tx state
      observableSlots nativeContract nativeYul)
    (hMatch :
      nativeResultsMatchOn observableSlots (interpretIR contract tx state)
        (.ok nativeYul)) :
    nativeDispatcherExecMatchesIRPositive fuel' contract tx state
      observableSlots nativeContract := by
  have hProject' := nativeProjectedDispatcherResultEq_unfold hProject
  unfold nativeDispatcherExecMatchesIRPositive
  dsimp only at hProject' ⊢
  rw [hProject']
  exact hMatch

theorem nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_project_eq_match
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    {haltState : EvmYul.Yul.State} {haltValue : EvmYul.Yul.Ast.Literal}
    {nativeYul : YulResult}
    (hExec :
      let initial :=
        Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
          (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode contract) observableSlots)
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        fuel' nativeContract initial =
        .error (.YulHalt haltState haltValue))
    (hProject :
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events
        (.error (.YulHalt haltState haltValue)) =
        nativeYul)
    (hMatch :
      nativeResultsMatchOn observableSlots (interpretIR contract tx state)
        (.ok nativeYul)) :
    nativeDispatcherExecMatchesIRPositive fuel' contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecMatchesIRPositive
  simp [hExec]
  rw [← hProject] at hMatch
  simpa [Compiler.Proofs.YulGeneration.Backends.Native.projectResult] using hMatch

theorem nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    {err : EvmYul.Yul.Exception} {nativeYul : YulResult}
    (hExec :
      let initial :=
        Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
          (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode contract) observableSlots)
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        fuel' nativeContract initial =
        .error err)
    (hProject :
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events (.error err) =
        nativeYul)
    (hMatch :
      nativeResultsMatchOn observableSlots (interpretIR contract tx state)
        (.ok nativeYul)) :
    nativeDispatcherExecMatchesIRPositive fuel' contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecMatchesIRPositive
  simp [hExec]
  rw [← hProject] at hMatch
  simpa [Compiler.Proofs.YulGeneration.Backends.Native.projectResult] using hMatch

/-- Discharges `nativeDispatcherExecMatchesIRPositive` when the native dispatcher reverts on a selector miss. -/
private theorem nativeDispatcherExecMatchesIRPositive_of_selector_miss_revert
    {fuel' : Nat} {irContract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        none)
    (hExec :
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        fuel' nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          nativeContract (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode irContract) observableSlots)) =
        .error EvmYul.Yul.Exception.Revert) :
    nativeDispatcherExecMatchesIRPositive fuel' irContract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecMatchesIRPositive
  dsimp only at hExec ⊢
  rw [hExec]
  simp [Compiler.Proofs.YulGeneration.Backends.Native.projectResult,
    nativeResultsMatchOn,
    Compiler.Proofs.YulGeneration.Backends.Native.nativeResultsMatchOn,
    Compiler.Proofs.IRGeneration.interpretIR, hFind]

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_miss_noFallback_noReceive
    (fuel : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (hLower :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok [.Block inner])
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        none)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
          reservedNames
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
            reservedNames n0 + 1)
          (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
            irContract.functions) = .ok (cases', midN) ∧
      nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 19)
        irContract tx state observableSlots
        { dispatcher := .Block [.Block inner], functions := functions } := by
  rcases
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_none_projectResult_eq
      fuel tx.functionSelector irContract.functions inner functions
      (YulTransaction.ofIR tx) state.storage state.events
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots)
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨reservedNames, n0, cases', midN, hLowerCases, hExec, _⟩
  exact ⟨reservedNames, n0, cases', midN, hLowerCases,
    nativeDispatcherExecMatchesIRPositive_of_selector_miss_revert hFind hExec⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_miss_noFallback_noReceive_atFuel
    (fuel' : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (hLower :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok [.Block inner])
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        none)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (_hEnv :
      Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
        (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) =
          .ok ()) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
          reservedNames
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
            reservedNames n0 + 1)
          (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
            irContract.functions) = .ok (cases', midN) ∧
      (cases'.length + 19 ≤ fuel' →
        nativeDispatcherExecMatchesIRPositive fuel'
          irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_none_atFuel_projectResult_eq
      fuel' tx.functionSelector irContract.functions inner functions
      (YulTransaction.ofIR tx) state.storage state.events
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots)
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨reservedNames, n0, cases', midN, hLowerCases, hCont⟩
  exact ⟨reservedNames, n0, cases', midN, hLowerCases, fun hFuel =>
    nativeDispatcherExecMatchesIRPositive_of_selector_miss_revert hFind (hCont hFuel).1⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_miss_noFallback_noReceive_withSwitchIds
    (fuel : Nat) (reservedNames : List String) (n0 : Nat)
    (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (hLower :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames n0
          [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok ([.Block inner], next))
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        none)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (_hEnv : Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
      (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) =
        .ok ()) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
          reservedNames
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
            reservedNames switchStart + 1)
          (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
            irContract.functions) = .ok (cases', midN) ∧
      nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 19)
        irContract tx state observableSlots
        { dispatcher := .Block [.Block inner], functions := functions } := by
  rcases
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_none_withSwitchIds_projectResult_eq
      fuel tx.functionSelector reservedNames n0 irContract.functions inner next
      functions (YulTransaction.ofIR tx) state.storage state.events
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots)
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨switchStart, cases', midN, hLowerCases, hExec, _⟩
  exact ⟨switchStart, cases', midN, hLowerCases,
    nativeDispatcherExecMatchesIRPositive_of_selector_miss_revert hFind hExec⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_miss_noFallback_noReceive_withSwitchIds_atFuel
    (fuel' : Nat) (reservedNames : List String) (n0 : Nat)
    (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (hLower :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames n0
          [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok ([.Block inner], next))
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        none)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (_hEnv : Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
      (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) =
        .ok ()) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
          reservedNames
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
            reservedNames switchStart + 1)
          (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
            irContract.functions) = .ok (cases', midN) ∧
      (cases'.length + 19 ≤ fuel' →
        nativeDispatcherExecMatchesIRPositive fuel'
          irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_none_withSwitchIds_atFuel_projectResult_eq
      fuel' tx.functionSelector reservedNames n0 irContract.functions inner next
      functions (YulTransaction.ofIR tx) state.storage state.events
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots)
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨switchStart, cases', midN, hLowerCases, hCont⟩
  exact ⟨switchStart, cases', midN, hLowerCases, fun hFuel =>
    nativeDispatcherExecMatchesIRPositive_of_selector_miss_revert hFind (hCont hFuel).1⟩

/-- Canonical lowered inner statement list of a no-fallback/no-receive `buildSwitch` block. -/
private abbrev buildSwitchLoweredInner
    (reservedNames : List String) (switchStart : Nat)
    (body1 : List EvmYul.Yul.Ast.Stmt)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) :
    List EvmYul.Yul.Ast.Stmt :=
  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
      (some (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Yul.YulExpr.call "iszero"
          [Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))),
   EvmYul.Yul.Ast.Stmt.If
      (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident "__has_selector"])) body1,
   EvmYul.Yul.Ast.Stmt.If
      (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Yul.YulExpr.ident "__has_selector"))
      [Compiler.Proofs.YulGeneration.Backends.lowerNativeSwitchBlock
        (Yul.YulExpr.call "shr"
          [Yul.YulExpr.lit Compiler.Constants.selectorShift,
           Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
          reservedNames switchStart) cases'
        [Compiler.Proofs.YulGeneration.Backends.Native.nativeRevertZeroZeroStmt]]]

/-- Native contract whose dispatcher initializes the free-memory pointer before `inner`. -/
private abbrev initFreeMemoryPointerContract
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap) :
    EvmYul.Yul.Ast.YulContract :=
  { dispatcher := .Block
      [.ExprStmtCall
        (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
          (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
             Yul.YulExpr.lit 128])),
       .Block inner],
    functions := functions }

/-- Lowered switch-case tags from `buildSwitchSourceCases` inherit selector bounds. -/
private theorem lowerSwitchCasesNativeWithSwitchIds_buildSwitch_tags_range
    (reservedNames : List String) (startN midN : Nat)
    (funcs : List IRFunction)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hLowerCases :
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
          reservedNames startN
          (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
            funcs) = .ok (cases', midN))
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
  have hTagsEq :=
    Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq
      reservedNames startN midN
      (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases funcs)
      cases' hLowerCases
  intro tag body hmem
  have hTagMem : tag ∈ cases'.map (·.1) :=
    List.mem_map_of_mem (f := Prod.fst) hmem
  rw [hTagsEq] at hTagMem
  simp [Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases] at hTagMem
  rcases hTagMem with ⟨fn, hFn, hTag⟩
  subst hTag
  exact hFunctionSelectorsRange fn hFn

/-- Shared selector-miss execution match for an `mstore(0x40, 0x80)`-prefixed `buildSwitch` block. -/
private theorem initFreeMemoryPointer_buildSwitch_selector_miss_of_inner
    (fuel : Nat) (reservedNames : List String) (switchStart midN : Nat)
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (body1 inner : List EvmYul.Yul.Ast.Stmt)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (hInner : inner = buildSwitchLoweredInner reservedNames switchStart body1 cases')
    (hLowerCases : Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
      reservedNames (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames switchStart + 1)
      (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = none)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 20)
      irContract tx state observableSlots (initFreeMemoryPointerContract inner functions) := by
  let nativeContract := initFreeMemoryPointerContract inner functions
  let materializedSlots :=
    Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode irContract) observableSlots
  have hSelector : tx.functionSelector = tx.functionSelector % Compiler.Constants.selectorModulus :=
    (Nat.mod_eq_of_lt hSelectorRange).symm
  have hLowerFind :=
    Compiler.Proofs.YulGeneration.Backends.Native.lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_none_of_find_function
      reservedNames (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames switchStart + 1)
      midN tx.functionSelector irContract.functions cases' hLowerCases hFind
  have hTagsRange :=
    lowerSwitchCasesNativeWithSwitchIds_buildSwitch_tags_range reservedNames
      (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames switchStart + 1)
      midN irContract.functions cases' hLowerCases hFunctionSelectorsRange
  have hPeel :=
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_peel
      fuel reservedNames switchStart cases' body1 inner functions
      (YulTransaction.ofIR tx) state.storage materializedSlots hInner
      (by simpa [YulTransaction.ofIR] using hNoWrap)
  have hEndpoint :=
    Compiler.Proofs.YulGeneration.Backends.Native.exec_block_lowerNativeSwitchBlock_revert_default_postInitFreeMemory_hasSelectorState_projectResult_eq
      fuel tx.functionSelector
      (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames switchStart)
      cases' nativeContract (YulTransaction.ofIR tx) state.storage state.events
      materializedSlots (by simpa [YulTransaction.ofIR] using hSelector)
      hLowerFind (Nat.lt_trans hSelectorRange (by decide)) hTagsRange
  dsimp [nativeContract, materializedSlots] at hPeel hEndpoint
  exact nativeDispatcherExecMatchesIRPositive_of_selector_miss_revert hFind
    (hPeel.trans hEndpoint.1)

theorem nativeDispatcherExecMatchesIRPositive_of_initFreeMemoryPointer_buildSwitch_selector_miss_noFallback_noReceive_atFuel
    (fuel' : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (hLower :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok [.Block inner])
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        none)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (_hEnv : Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
      (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) = .ok ()) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
          reservedNames
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
            reservedNames n0 + 1)
          (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
            irContract.functions) = .ok (cases', midN) ∧
      (cases'.length + 20 ≤ fuel' →
        nativeDispatcherExecMatchesIRPositive fuel'
          irContract tx state observableSlots
          { dispatcher := .Block
              [.ExprStmtCall
                (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
                  (Yul.YulExpr.call "mstore"
                    [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
                     Yul.YulExpr.lit 128])),
               .Block inner],
            functions := functions }) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, hInner, hLowerCases⟩ :=
    Compiler.Proofs.YulGeneration.Backends.Native.buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered
      irContract.functions inner hLower
  refine ⟨reservedNames, n0, cases', midN, hLowerCases, fun hFuel => ?_⟩
  have hFuelShape : fuel' = (fuel' - (cases'.length + 20)) + cases'.length + 20 := by omega
  rw [hFuelShape]
  exact initFreeMemoryPointer_buildSwitch_selector_miss_of_inner
    (fuel' - (cases'.length + 20)) reservedNames n0 midN irContract tx state
    observableSlots body1 inner cases' functions hInner hLowerCases hFind
    hSelectorRange hNoWrap hFunctionSelectorsRange

theorem nativeDispatcherExecMatchesIRPositive_of_initFreeMemoryPointer_buildSwitch_selector_miss_noFallback_noReceive
    (fuel : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (hLower :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok [.Block inner])
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        none)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (_hEnv :
      Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
        (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) =
          .ok ()) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
          reservedNames
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
            reservedNames n0 + 1)
          (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
            irContract.functions) = .ok (cases', midN) ∧
      nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 20)
        irContract tx state observableSlots
        { dispatcher := .Block
            [.ExprStmtCall
              (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
                (Yul.YulExpr.call "mstore"
                  [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
                   Yul.YulExpr.lit 128])),
             .Block inner],
          functions := functions } := by
  obtain ⟨body1, reservedNames, n0, cases', midN, hInner, hLowerCases⟩ :=
    Compiler.Proofs.YulGeneration.Backends.Native.buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered
      irContract.functions inner hLower
  exact ⟨reservedNames, n0, cases', midN, hLowerCases,
    initFreeMemoryPointer_buildSwitch_selector_miss_of_inner
      fuel reservedNames n0 midN irContract tx state observableSlots body1 inner
      cases' functions hInner hLowerCases hFind hSelectorRange hNoWrap
      hFunctionSelectorsRange⟩

theorem nativeDispatcherExecMatchesIRPositive_of_initFreeMemoryPointer_buildSwitch_selector_miss_noFallback_noReceive_withSwitchIds_atFuel
    (fuel' : Nat) (reservedNames : List String) (n0 : Nat)
    (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (hLower :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames n0
          [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok ([.Block inner], next))
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        none)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
          reservedNames
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
            reservedNames switchStart + 1)
          (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
            irContract.functions) = .ok (cases', midN) ∧
      (cases'.length + 20 ≤ fuel' →
        nativeDispatcherExecMatchesIRPositive fuel'
          irContract tx state observableSlots
          { dispatcher := .Block
              [.ExprStmtCall
                (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
                  (Yul.YulExpr.call "mstore"
                    [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
                     Yul.YulExpr.lit 128])),
               .Block inner],
            functions := functions }) := by
  obtain ⟨body1, switchStart, cases', midN, hInner, hLowerCases⟩ :=
    Compiler.Proofs.YulGeneration.Backends.Native.buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered_withSwitchIds
      reservedNames n0 irContract.functions inner next hLower
  refine ⟨switchStart, cases', midN, hLowerCases, fun hFuel => ?_⟩
  have hFuelShape : fuel' = (fuel' - (cases'.length + 20)) + cases'.length + 20 := by
    omega
  rw [hFuelShape]
  exact initFreeMemoryPointer_buildSwitch_selector_miss_of_inner
    (fuel' - (cases'.length + 20)) reservedNames switchStart midN irContract tx
    state observableSlots body1 inner cases' functions hInner hLowerCases hFind
    hSelectorRange hNoWrap hFunctionSelectorsRange

theorem nativeDispatcherExecMatchesIRPositive_of_initFreeMemoryPointer_buildSwitch_selector_miss_noFallback_noReceive_withSwitchIds
    (fuel : Nat) (reservedNames : List String) (n0 : Nat)
    (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (hLower :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames n0
          [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok ([.Block inner], next))
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        none)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
          reservedNames
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
            reservedNames switchStart + 1)
          (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
            irContract.functions) = .ok (cases', midN) ∧
      nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 20)
        irContract tx state observableSlots
        { dispatcher := .Block
            [.ExprStmtCall
              (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
                (Yul.YulExpr.call "mstore"
                  [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
                   Yul.YulExpr.lit 128])),
             .Block inner],
          functions := functions } := by
  obtain ⟨body1, switchStart, cases', midN, hInner, hLowerCases⟩ :=
    Compiler.Proofs.YulGeneration.Backends.Native.buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered_withSwitchIds
      reservedNames n0 irContract.functions inner next hLower
  exact ⟨switchStart, cases', midN, hLowerCases,
    initFreeMemoryPointer_buildSwitch_selector_miss_of_inner
      fuel reservedNames switchStart midN irContract tx state observableSlots
      body1 inner cases' functions hInner hLowerCases hFind hSelectorRange
      hNoWrap hFunctionSelectorsRange⟩

/-- Helper for `nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_error_noFallback_noReceive`. -/
private theorem selector_hit_error_noFallback_noReceive_aux
    (fuel : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (fn : IRFunction) (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
      [Compiler.CodegenCommon.buildSwitch irContract.functions none none] = .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some {dispatcher := .Block [.Block inner], functions := functions})
            (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchStoreMarkedPrefixStateForId
              {dispatcher := .Block [.Block inner], functions := functions}
              (YulTransaction.ofIR tx) state.storage
              (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
                (Compiler.runtimeCode irContract) observableSlots)
              (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0)
              Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) = .error err) →
        Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events (.error err) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 19) irContract tx state
          observableSlots {dispatcher := .Block [.Block inner], functions := functions}) := by
  rcases
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_projectResult_eq
      fuel tx.functionSelector irContract.functions fn inner functions
      (YulTransaction.ofIR tx) state.storage state.events
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots)
      err nativeYul hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨reservedNames, n0, cases', body', bodyStart, bodyEnd, hCase, hBodyLower, hCont⟩
  exact ⟨reservedNames, n0, cases', body', bodyStart, bodyEnd, hCase, hBodyLower,
    fun hBody hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match
        (hCont hBody hProject).1 (hCont hBody hProject).2 hMatch⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_error_noFallback_noReceive
    (fuel : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (fn : IRFunction) (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
      [Compiler.CodegenCommon.buildSwitch irContract.functions none none] = .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some {dispatcher := .Block [.Block inner], functions := functions})
            (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchStoreMarkedPrefixStateForId
              {dispatcher := .Block [.Block inner], functions := functions}
              (YulTransaction.ofIR tx) state.storage
              (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
                (Compiler.runtimeCode irContract) observableSlots)
              (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0)
              Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) = .error err) →
        Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events (.error err) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 19) irContract tx state
          observableSlots {dispatcher := .Block [.Block inner], functions := functions}) :=
  selector_hit_error_noFallback_noReceive_aux fuel irContract tx state observableSlots
    inner functions fn err nativeYul hLower hFind hSelectorRange hNoWrap hFunctionSelectorsRange

/-- Helper for `nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_error_noFallback_noReceive_atFuel`. -/
private theorem selector_hit_error_noFallback_noReceive_atFuel_aux
    (fuel' : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (fn : IRFunction) (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
      [Compiler.CodegenCommon.buildSwitch irContract.functions none none] = .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0 + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases irContract.functions) =
          .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some {dispatcher := .Block [.Block inner], functions := functions})
            (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchStoreMarkedPrefixStateForId
              {dispatcher := .Block [.Block inner], functions := functions}
              (YulTransaction.ofIR tx) state.storage
              (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
                (Compiler.runtimeCode irContract) observableSlots)
              (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0)
              Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) = .error err) →
        Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events (.error err) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          {dispatcher := .Block [.Block inner], functions := functions}) := by
  rcases
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_atFuel_projectResult_eq
      fuel' tx.functionSelector irContract.functions fn inner functions
      (YulTransaction.ofIR tx) state.storage state.events
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots)
      err nativeYul hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower, hCont⟩
  exact ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower,
    fun hFuel hBody hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match
        (hCont hFuel hBody hProject).1 (hCont hFuel hBody hProject).2 hMatch⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_error_noFallback_noReceive_atFuel
    (fuel' : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (fn : IRFunction) (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
      [Compiler.CodegenCommon.buildSwitch irContract.functions none none] = .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0 + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases irContract.functions) =
          .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some {dispatcher := .Block [.Block inner], functions := functions})
            (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchStoreMarkedPrefixStateForId
              {dispatcher := .Block [.Block inner], functions := functions}
              (YulTransaction.ofIR tx) state.storage
              (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
                (Compiler.runtimeCode irContract) observableSlots)
              (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0)
              Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) = .error err) →
        Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events (.error err) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          {dispatcher := .Block [.Block inner], functions := functions}) :=
  selector_hit_error_noFallback_noReceive_atFuel_aux fuel' irContract tx state observableSlots
    inner functions fn err nativeYul hLower hFind hSelectorRange hNoWrap hFunctionSelectorsRange

/-- Helper for `nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_error_noFallback_noReceive_atFuel_artifact`. -/
private theorem selector_hit_error_noFallback_noReceive_atFuel_artifact_aux
    (fuel' : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap) (fn : IRFunction)
    (hLower : lowerStmtsNative [CodegenCommon.buildSwitch irContract.functions none none] =
      .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames n0 + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) =
        .ok (body', bodyEnd) ∧
      (∀ (err : EvmYul.Yul.Exception) (nativeYul : YulResult),
        cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some {dispatcher := .Block [.Block inner], functions := functions})
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              {dispatcher := .Block [.Block inner], functions := functions}
              (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames n0)
              Native.nativeSwitchHasSelectorStore) = .error err) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.error err) =
          nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          {dispatcher := .Block [.Block inner], functions := functions}) := by
  rcases
    Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_atFuel_artifact_projectResult_eq
      fuel' tx.functionSelector irContract.functions fn inner functions
      (YulTransaction.ofIR tx) state.storage state.events
      (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower, hCont⟩
  exact ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower,
    fun err nativeYul hFuel hBody hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match
        (hCont err nativeYul hFuel hBody hProject).1 (hCont err nativeYul hFuel hBody hProject).2 hMatch⟩

/-- Artifact-fixed selector-hit error dispatcher bridge for the no-reserved
generated dispatcher lowering path. -/
theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_error_noFallback_noReceive_atFuel_artifact
    (fuel' : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap) (fn : IRFunction)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
      [Compiler.CodegenCommon.buildSwitch irContract.functions none none] = .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0 + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases irContract.functions) =
          .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (∀ (err : EvmYul.Yul.Exception) (nativeYul : YulResult),
        cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some {dispatcher := .Block [.Block inner], functions := functions})
            (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchStoreMarkedPrefixStateForId
              {dispatcher := .Block [.Block inner], functions := functions}
              (YulTransaction.ofIR tx) state.storage
              (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
                (Compiler.runtimeCode irContract) observableSlots)
              (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0)
              Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) = .error err) →
        Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events (.error err) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          {dispatcher := .Block [.Block inner], functions := functions}) :=
  selector_hit_error_noFallback_noReceive_atFuel_artifact_aux fuel' irContract tx state
    observableSlots inner functions fn hLower hFind hSelectorRange hNoWrap hFunctionSelectorsRange

/-- Helper for `nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_error_noFallback_noReceive_withSwitchIds`. -/
private theorem selector_hit_error_noFallback_noReceive_withSwitchIds_aux
    (fuel : Nat) (reservedNames : List String) (n0 : Nat)
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (fn : IRFunction) (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
      [Compiler.CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some {dispatcher := .Block [.Block inner], functions := functions})
            (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchStoreMarkedPrefixStateForId
              {dispatcher := .Block [.Block inner], functions := functions}
              (YulTransaction.ofIR tx) state.storage
              (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
                (Compiler.runtimeCode irContract) observableSlots)
              (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames switchStart)
              Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) = .error err) →
        Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events (.error err) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 19) irContract tx state
          observableSlots {dispatcher := .Block [.Block inner], functions := functions}) := by
  rcases
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_withSwitchIds_projectResult_eq
      fuel tx.functionSelector reservedNames n0 irContract.functions fn inner next
      functions (YulTransaction.ofIR tx) state.storage state.events
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots)
      err nativeYul hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨switchStart, cases', body', bodyStart, bodyEnd, hCase, hBodyLower, hCont⟩
  exact ⟨switchStart, cases', body', bodyStart, bodyEnd, hCase, hBodyLower,
    fun hBody hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match
        (hCont hBody hProject).1 (hCont hBody hProject).2 hMatch⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_error_noFallback_noReceive_withSwitchIds
    (fuel : Nat) (reservedNames : List String) (n0 : Nat)
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (fn : IRFunction) (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
      [Compiler.CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some {dispatcher := .Block [.Block inner], functions := functions})
            (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchStoreMarkedPrefixStateForId
              {dispatcher := .Block [.Block inner], functions := functions}
              (YulTransaction.ofIR tx) state.storage
              (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
                (Compiler.runtimeCode irContract) observableSlots)
              (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames switchStart)
              Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) = .error err) →
        Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events (.error err) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 19) irContract tx state
          observableSlots {dispatcher := .Block [.Block inner], functions := functions}) :=
  selector_hit_error_noFallback_noReceive_withSwitchIds_aux fuel reservedNames n0 irContract
    tx state observableSlots inner next functions fn err nativeYul hLower hFind hSelectorRange
    hNoWrap hFunctionSelectorsRange

/-- Helper for `nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_error_noFallback_noReceive_withSwitchIds_atFuel`. -/
private theorem selector_hit_error_noFallback_noReceive_withSwitchIds_atFuel_aux
    (fuel' : Nat) (reservedNames : List String) (n0 : Nat)
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap) (fn : IRFunction) (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower : lowerStmtsNativeWithSwitchIds reservedNames n0
      [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames
        (freshNativeSwitchId reservedNames switchStart + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) =
        .ok (body', bodyEnd) ∧
      (cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some {dispatcher := .Block [.Block inner], functions := functions})
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              {dispatcher := .Block [.Block inner], functions := functions}
              (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames switchStart)
              Native.nativeSwitchHasSelectorStore) = .error err) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.error err) =
          nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          {dispatcher := .Block [.Block inner], functions := functions}) := by
  rcases
    Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_withSwitchIds_atFuel_projectResult_eq
      fuel' tx.functionSelector reservedNames n0 irContract.functions fn inner
      next functions (YulTransaction.ofIR tx) state.storage state.events
      (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      err nativeYul hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨switchStart, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower, hCont⟩
  exact ⟨switchStart, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower,
    fun hFuel hBody hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match
        (hCont hFuel hBody hProject).1 (hCont hFuel hBody hProject).2 hMatch⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_error_noFallback_noReceive_withSwitchIds_atFuel
    (fuel' : Nat) (reservedNames : List String) (n0 : Nat)
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (fn : IRFunction) (err : EvmYul.Yul.Exception) (nativeYul : YulResult)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
      [Compiler.CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases irContract.functions) =
          .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some {dispatcher := .Block [.Block inner], functions := functions})
            (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchStoreMarkedPrefixStateForId
              {dispatcher := .Block [.Block inner], functions := functions}
              (YulTransaction.ofIR tx) state.storage
              (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
                (Compiler.runtimeCode irContract) observableSlots)
              (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames switchStart)
              Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) = .error err) →
        Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events (.error err) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          {dispatcher := .Block [.Block inner], functions := functions}) :=
  selector_hit_error_noFallback_noReceive_withSwitchIds_atFuel_aux fuel' reservedNames n0
    irContract tx state observableSlots inner next functions fn err nativeYul hLower hFind
    hSelectorRange hNoWrap hFunctionSelectorsRange

/-- Helper for `nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_error_noFallback_noReceive_withSwitchIds_atFuel_artifact`. -/
private theorem selector_hit_error_noFallback_noReceive_withSwitchIds_atFuel_artifact_aux
    (fuel' : Nat) (reservedNames : List String) (n0 : Nat)
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap) (fn : IRFunction)
    (hLower : lowerStmtsNativeWithSwitchIds reservedNames n0
      [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames
        (freshNativeSwitchId reservedNames switchStart + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) =
        .ok (body', bodyEnd) ∧
      (∀ (err : EvmYul.Yul.Exception) (nativeYul : YulResult),
        cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some {dispatcher := .Block [.Block inner], functions := functions})
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              {dispatcher := .Block [.Block inner], functions := functions}
              (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames switchStart)
              Native.nativeSwitchHasSelectorStore) = .error err) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.error err) =
          nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          {dispatcher := .Block [.Block inner], functions := functions}) := by
  rcases
    Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_error_withSwitchIds_atFuel_artifact_projectResult_eq
      fuel' tx.functionSelector reservedNames n0 irContract.functions fn inner
      next functions (YulTransaction.ofIR tx) state.storage state.events
      (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨switchStart, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower, hCont⟩
  exact ⟨switchStart, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower,
    fun err nativeYul hFuel hBody hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match
        (hCont err nativeYul hFuel hBody hProject).1 (hCont err nativeYul hFuel hBody hProject).2 hMatch⟩

/-- Artifact-fixed reserved-context selector-hit error dispatcher bridge. -/
theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_error_noFallback_noReceive_withSwitchIds_atFuel_artifact
    (fuel' : Nat) (reservedNames : List String) (n0 : Nat)
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap) (fn : IRFunction)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
      [Compiler.CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases irContract.functions) =
          .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (∀ (err : EvmYul.Yul.Exception) (nativeYul : YulResult),
        cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some {dispatcher := .Block [.Block inner], functions := functions})
            (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchStoreMarkedPrefixStateForId
              {dispatcher := .Block [.Block inner], functions := functions}
              (YulTransaction.ofIR tx) state.storage
              (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
                (Compiler.runtimeCode irContract) observableSlots)
              (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames switchStart)
              Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) = .error err) →
        Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events (.error err) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          {dispatcher := .Block [.Block inner], functions := functions}) :=
  selector_hit_error_noFallback_noReceive_withSwitchIds_atFuel_artifact_aux fuel' reservedNames
    n0 irContract tx state observableSlots inner next functions fn hLower hFind hSelectorRange
    hNoWrap hFunctionSelectorsRange

/-- Discharges `nativeDispatcherExecMatchesIRPositive` from a successful dispatcher execution and projected result match. -/
private theorem nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    {final : EvmYul.Yul.State} {nativeYul : YulResult}
    (hExec :
      Native.contractDispatcherExecResult fuel' nativeContract
        (Native.initialState nativeContract (YulTransaction.ofIR tx) state.storage
          (Native.materializedStorageSlots (runtimeCode contract) observableSlots)) =
        .ok final)
    (hProject :
      Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
        (.ok (((final.reviveJump.overwrite?
          (Native.initialState nativeContract (YulTransaction.ofIR tx) state.storage
            (Native.materializedStorageSlots (runtimeCode contract) observableSlots))).setStore
          (Native.initialState nativeContract (YulTransaction.ofIR tx) state.storage
            (Native.materializedStorageSlots (runtimeCode contract) observableSlots))), [])) =
        nativeYul)
    (hMatch :
      nativeResultsMatchOn observableSlots (interpretIR contract tx state) (.ok nativeYul)) :
    nativeDispatcherExecMatchesIRPositive fuel' contract tx state observableSlots nativeContract := by
  refine nativeDispatcherExecMatchesIRPositive_of_project_eq_match ?_ hMatch
  simp [nativeProjectedDispatcherResultEq, hExec, hProject]

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive
    (fuel : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap) (fn : IRFunction) (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower : lowerStmtsNative [CodegenCommon.buildSwitch irContract.functions none none] = .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames n0) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) body' (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 19) irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases
    Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_projectResult_eq_preserved
      fuel tx.functionSelector irContract.functions fn inner functions (YulTransaction.ofIR tx)
      state.storage state.events (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      final (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨reservedNames, n0, cases', body', bodyStart, bodyEnd, hCase, hBodyLower, hCont⟩
  exact ⟨reservedNames, n0, cases', body', bodyStart, bodyEnd, hCase, hBodyLower,
    fun hBody hPreserves hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match
        (hCont hBody hPreserves rfl).1 hProject hMatch⟩

/-- Generated-prefix variant of
`nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive`
for payable functions. The selected-body execution and matched-flag
preservation premises are over the lowered user body `fn.body`, not the whole
generated selector case body. -/
theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_payable_generated_prefix
    (fuel : Nat) (irContract : IRContract) (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (inner : List EvmYul.Yul.Ast.Stmt) (functions : NativeFunctionMap) (fn : IRFunction) (final : EvmYul.Yul.State)
    (nativeYul : YulResult) (hLower : lowerStmtsNative [CodegenCommon.buildSwitch irContract.functions none none] = .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus) (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hPayable : fn.payable = true) (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames n0 + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      lowerStmtsNativeWithSwitchIds reservedNames userBodyStart fn.body = .ok (bodyNative, bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions } (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames n0) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) bodyNative (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 23) irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_payable_generated_prefix_projectResult_eq
      fuel tx.functionSelector irContract.functions fn inner functions tx state.storage state.events
      (Native.materializedStorageSlots (runtimeCode irContract) observableSlots) final
      (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap (Nat.lt_trans hSelectorRange (by decide))
      hFunctionSelectorsRange hPayable hguards hArgs with
    ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL, hCont⟩
  exact ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL,
    fun hBody hPres hProj hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match (hCont hBody hPres rfl).1 hProj hMatch⟩

/-- Generated-prefix variant of
`nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive`
for non-payable functions. The selected-body execution and matched-flag
preservation premises are over the lowered user body `fn.body`, not the whole
generated selector case body. -/
theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_nonpayable_generated_prefix
    (fuel : Nat) (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (functions : NativeFunctionMap)
    (fn : IRFunction) (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower : lowerStmtsNative [CodegenCommon.buildSwitch irContract.functions none none] = .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false) (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames n0 + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      lowerStmtsNativeWithSwitchIds reservedNames userBodyStart fn.body = .ok (bodyNative, bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions } (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames n0) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) bodyNative (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 24) irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_nonpayable_generated_prefix_projectResult_eq
      fuel tx.functionSelector irContract.functions fn inner functions tx state.storage state.events
      (Native.materializedStorageSlots (runtimeCode irContract) observableSlots) final
      (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange hNonPayable hguards hArgs with
    ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL, hCont⟩
  exact ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL,
    fun hBody hPres hProj hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match (hCont hBody hPres rfl).1 hProj hMatch⟩

/-- Exact-total-fuel generated-prefix variant for payable functions. The
selected-body execution and matched-flag preservation premises are over the
lowered user body `fn.body`, while the native dispatcher package is stated at
the externally supplied `fuel'`. -/
theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_payable_generated_prefix_atFuel
    (fuel' : Nat) (irContract : IRContract) (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (inner : List EvmYul.Yul.Ast.Stmt) (functions : NativeFunctionMap) (fn : IRFunction) (final : EvmYul.Yul.State)
    (nativeYul : YulResult) (hLower : lowerStmtsNative [CodegenCommon.buildSwitch irContract.functions none none] = .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus) (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hPayable : fn.payable = true) (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames n0 + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      lowerStmtsNativeWithSwitchIds reservedNames userBodyStart fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 23 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec ((fuel' - (cases'.length + 23)) + suffix.length + 10) (.Block bodyNative)
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions } (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames n0) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) bodyNative (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_payable_generated_prefix_atFuel_projectResult_eq
      fuel' tx.functionSelector irContract.functions fn inner functions tx state.storage state.events
      (Native.materializedStorageSlots (runtimeCode irContract) observableSlots) final
      (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap (Nat.lt_trans hSelectorRange (by decide))
      hFunctionSelectorsRange hPayable hguards hArgs with
    ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL, hCont⟩
  exact ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL,
    fun hFuel hBody hPres hProj hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match (hCont hFuel hBody hPres rfl).1 hProj hMatch⟩

/-- Exact-total-fuel generated-prefix variant for non-payable functions. The
selected-body execution and matched-flag preservation premises are over the
lowered user body `fn.body`, while the native dispatcher package is stated at
the externally supplied `fuel'`. -/
theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_nonpayable_generated_prefix_atFuel
    (fuel' : Nat) (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (functions : NativeFunctionMap)
    (fn : IRFunction) (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower : lowerStmtsNative [CodegenCommon.buildSwitch irContract.functions none none] = .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false) (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames n0 + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      lowerStmtsNativeWithSwitchIds reservedNames userBodyStart fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 24 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec ((fuel' - (cases'.length + 24)) + suffix.length + 10) (.Block bodyNative)
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions } (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames n0) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) bodyNative (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_nonpayable_generated_prefix_atFuel_projectResult_eq
      fuel' tx.functionSelector irContract.functions fn inner functions tx state.storage state.events
      (Native.materializedStorageSlots (runtimeCode irContract) observableSlots) final
      (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange hNonPayable hguards hArgs with
    ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL, hCont⟩
  exact ⟨reservedNames, n0, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL,
    fun hFuel hBody hPres hProj hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match (hCont hFuel hBody hPres rfl).1 hProj hMatch⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_atFuel
    (fuel' : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap) (fn : IRFunction) (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower : lowerStmtsNative [CodegenCommon.buildSwitch irContract.functions none none] = .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames n0 + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames n0) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) body' (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases
    Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_atFuel_projectResult_eq_preserved
      fuel' tx.functionSelector irContract.functions fn inner functions (YulTransaction.ofIR tx)
      state.storage state.events (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      final (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower, hCont⟩
  exact ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower,
    fun hFuel hBody hPreserves hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match
        (hCont hFuel hBody hPreserves rfl).1 hProject hMatch⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_atFuel_forall
    (fuel' : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap) (fn : IRFunction)
    (hLower : lowerStmtsNative [CodegenCommon.buildSwitch irContract.functions none none] = .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames n0 + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (∀ final nativeYul, cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames n0) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames n0))
            (EvmYul.UInt256.ofNat 1) body' (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases
    Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_atFuel_projectResult_eq_preserved_forall
      fuel' tx.functionSelector irContract.functions fn inner functions (YulTransaction.ofIR tx)
      state.storage state.events (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower, hCont⟩
  exact ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower,
    fun final nativeYul hFuel hBody hPreserves hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match
        (hCont final (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
          hFuel hBody hPreserves rfl).1 hProject hMatch⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_withSwitchIds
    (fuel : Nat) (reservedNames : List String) (n0 : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap) (fn : IRFunction) (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower : lowerStmtsNativeWithSwitchIds reservedNames n0
      [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body')
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames switchStart) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) body' (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 19) irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases
    Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_projectResult_eq_preserved
      fuel tx.functionSelector reservedNames n0 irContract.functions fn inner next functions
      (YulTransaction.ofIR tx) state.storage state.events
      (Native.materializedStorageSlots (runtimeCode irContract) observableSlots) final
      (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨switchStart, cases', body', bodyStart, bodyEnd, hCase, hBodyLower, hCont⟩
  exact ⟨switchStart, cases', body', bodyStart, bodyEnd, hCase, hBodyLower,
    fun hBody hPreserves hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match
        (hCont hBody hPreserves rfl).1 hProject hMatch⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_payable_withSwitchIds_generated_prefix
    (fuel : Nat) (reservedNames : List String) (n0 : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap) (fn : IRFunction) (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower : lowerStmtsNativeWithSwitchIds reservedNames n0 [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hPayable : fn.payable = true) (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames switchStart + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      lowerStmtsNativeWithSwitchIds reservedNames userBodyStart fn.body = .ok (bodyNative, bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions } (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames switchStart) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) bodyNative (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 23) irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_payable_withSwitchIds_generated_prefix_projectResult_eq
      fuel tx.functionSelector reservedNames n0 irContract.functions fn inner next functions tx
      state.storage state.events (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      final (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange hPayable hguards hArgs with
    ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL, hCont⟩
  exact ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL,
    fun hBody hPres hProj hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match (hCont hBody hPres rfl).1 hProj hMatch⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_nonpayable_withSwitchIds_generated_prefix
    (fuel : Nat) (reservedNames : List String) (n0 : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap) (fn : IRFunction) (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower : lowerStmtsNativeWithSwitchIds reservedNames n0 [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false) (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames switchStart + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      lowerStmtsNativeWithSwitchIds reservedNames userBodyStart fn.body = .ok (bodyNative, bodyEnd) ∧
      ((∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 10) (.Block bodyNative)
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions } (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames switchStart) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) bodyNative (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive (fuel + cases'.length + 24) irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_nonpayable_withSwitchIds_generated_prefix_projectResult_eq
      fuel tx.functionSelector reservedNames n0 irContract.functions fn inner next functions tx
      state.storage state.events (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      final (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange hNonPayable hguards hArgs with
    ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL, hCont⟩
  exact ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL,
    fun hBody hPres hProj hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match (hCont hBody hPres rfl).1 hProj hMatch⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_payable_withSwitchIds_generated_prefix_atFuel
    (fuel' : Nat) (reservedNames : List String) (n0 : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap) (fn : IRFunction) (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower : lowerStmtsNativeWithSwitchIds reservedNames n0 [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hPayable : fn.payable = true) (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames switchStart + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      lowerStmtsNativeWithSwitchIds reservedNames userBodyStart fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 23 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec ((fuel' - (cases'.length + 23)) + suffix.length + 10) (.Block bodyNative)
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions } (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames switchStart) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) bodyNative (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_payable_withSwitchIds_generated_prefix_atFuel_projectResult_eq
      fuel' tx.functionSelector reservedNames n0 irContract.functions fn inner next functions tx
      state.storage state.events (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      final (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange hPayable hguards hArgs with
    ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL, hCont⟩
  exact ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL,
    fun hFuel hBody hPres hProj hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match (hCont hFuel hBody hPres rfl).1 hProj hMatch⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_nonpayable_withSwitchIds_generated_prefix_atFuel
    (fuel' : Nat) (reservedNames : List String) (n0 : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap) (fn : IRFunction) (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower : lowerStmtsNativeWithSwitchIds reservedNames n0 [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false) (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames switchStart + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      lowerStmtsNativeWithSwitchIds reservedNames userBodyStart fn.body = .ok (bodyNative, bodyEnd) ∧
      (cases'.length + 24 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec ((fuel' - (cases'.length + 24)) + suffix.length + 10) (.Block bodyNative)
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions } (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames switchStart) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) bodyNative (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_nonpayable_withSwitchIds_generated_prefix_atFuel_projectResult_eq
      fuel' tx.functionSelector reservedNames n0 irContract.functions fn inner next functions tx
      state.storage state.events (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      final (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange hNonPayable hguards hArgs with
    ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL, hCont⟩
  exact ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart, hLC, hC, hBL, hUBL,
    fun hFuel hBody hPres hProj hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match (hCont hFuel hBody hPres rfl).1 hProj hMatch⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_withSwitchIds_atFuel
    (fuel' : Nat) (reservedNames : List String) (n0 : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap) (fn : IRFunction) (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (hLower : lowerStmtsNativeWithSwitchIds reservedNames n0
      [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames switchStart + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames switchStart) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) body' (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases
    Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_atFuel_projectResult_eq_preserved
      fuel' tx.functionSelector reservedNames n0 irContract.functions fn inner next functions
      (YulTransaction.ofIR tx) state.storage state.events
      (Native.materializedStorageSlots (runtimeCode irContract) observableSlots) final
      (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨switchStart, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower, hCont⟩
  exact ⟨switchStart, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower,
    fun hFuel hBody hPreserves hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match
        (hCont hFuel hBody hPreserves rfl).1 hProject hMatch⟩

theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_withSwitchIds_atFuel_forall
    (fuel' : Nat) (reservedNames : List String) (n0 : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap) (fn : IRFunction)
    (hLower : lowerStmtsNativeWithSwitchIds reservedNames n0 [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames switchStart + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (∀ final nativeYul, cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions } (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames switchStart) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          Native.NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames switchStart))
            (EvmYul.UInt256.ofNat 1) body' (some { dispatcher := .Block [.Block inner], functions := functions })) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_atFuel_projectResult_eq_preserved_forall
      fuel' tx.functionSelector reservedNames n0 irContract.functions fn inner next functions
      (YulTransaction.ofIR tx) state.storage state.events
      (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨switchStart, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower, hCont⟩
  exact ⟨switchStart, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower,
    fun final nativeYul hFuel hBody hPreserves hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match
        (hCont final (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
          hFuel hBody hPreserves rfl).1 hProject hMatch⟩

/-- Reserved selector-hit artifact continuation with a direct raw matched-flag endpoint fact. -/
theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_withSwitchIds_atFuel_forall_finalMatched
    (fuel' : Nat) (reservedNames : List String) (n0 : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (functions : NativeFunctionMap) (fn : IRFunction)
    (hLower : lowerStmtsNativeWithSwitchIds reservedNames n0 [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], next))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (switchStart : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames switchStart + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (∀ final nativeYul, cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions } (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames switchStart) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ matchedName : EvmYul.Identifier,
          matchedName = nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames switchStart) →
            final[matchedName]! = EvmYul.UInt256.ofNat 1) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_withSwitchIds_atFuel_projectResult_eq_finalMatched_forall
      fuel' tx.functionSelector reservedNames n0 irContract.functions fn inner next functions
      (YulTransaction.ofIR tx) state.storage state.events
      (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨switchStart, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower, hCont⟩
  exact ⟨switchStart, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower,
    fun final nativeYul hFuel hBody hFinalMatched hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match
        (hCont final (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
          hFuel hBody hFinalMatched rfl).1 hProject hMatch⟩

/-- Selector-hit artifact continuation with a direct raw matched-flag endpoint fact. -/
theorem nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_atFuel_forall_finalMatched
    (fuel' : Nat) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt)
    (functions : NativeFunctionMap) (fn : IRFunction)
    (hLower : lowerStmtsNative [CodegenCommon.buildSwitch irContract.functions none none] = .ok [.Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (midN : Nat) (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames n0 + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      (∀ final nativeYul, cases'.length + 19 ≤ fuel' →
        (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
          EvmYul.Yul.exec (((fuel' - (cases'.length + 19)) + 1) + suffix.length + 7) (.Block body')
            (some { dispatcher := .Block [.Block inner], functions := functions })
            (Native.nativeSwitchStoreMarkedPrefixStateForId
              { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage
              (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
              (freshNativeSwitchId reservedNames n0) Native.nativeSwitchHasSelectorStore) = .ok final) →
        (∀ matchedName : EvmYul.Identifier,
          matchedName = nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames n0) →
            final[matchedName]! = EvmYul.UInt256.ofNat 1) →
        Native.projectResult (YulTransaction.ofIR tx) state.storage state.events
          (.ok (((final.reviveJump.overwrite? (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
            (Native.initialState { dispatcher := .Block [.Block inner], functions := functions }
              (YulTransaction.ofIR tx) state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
        nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
        nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots
          { dispatcher := .Block [.Block inner], functions := functions }) := by
  rcases
    Native.contractDispatcherExecResult_buildSwitch_noFallback_noReceive_selector_find_some_ok_atFuel_projectResult_eq_finalMatched_forall
      fuel' tx.functionSelector irContract.functions fn inner functions (YulTransaction.ofIR tx)
      state.storage state.events (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      hLower (Nat.mod_eq_of_lt hSelectorRange).symm hFind hNoWrap
      (Nat.lt_trans hSelectorRange (by decide)) hFunctionSelectorsRange with
    ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower, hCont⟩
  exact ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower,
    fun final nativeYul hFuel hBody hFinalMatched hProject hMatch =>
      nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match
        (hCont final (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.ok (final, [])))
          hFuel hBody hFinalMatched rfl).1 hProject hMatch⟩

/-- Native contract value produced by helper-free dispatcher-only lowering. -/
private abbrev nativeContractOfDispatcher
    (dispatcher : List EvmYul.Yul.Ast.Stmt) :
    EvmYul.Yul.Ast.YulContract :=
  { dispatcher := .Block dispatcher
    functions :=
      (∅ : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap) }

/-- Native statement emitted by generated runtime initialization. -/
private abbrev nativeInitFreeMemoryPointerStmt : EvmYul.Yul.Ast.Stmt :=
  .ExprStmtCall
    (Backends.lowerExprNative
      (Yul.YulExpr.call "mstore"
        [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
         Yul.YulExpr.lit 128]))

/-- Helper-free generated-runtime contract with the init prefix followed by
the dispatcher lowering. -/
private abbrev nativeContractOfInitPrefixedDispatcher
    (dispatcher : List EvmYul.Yul.Ast.Stmt) :
    EvmYul.Yul.Ast.YulContract :=
  { dispatcher := .Block (nativeInitFreeMemoryPointerStmt :: dispatcher)
    functions :=
      (∅ : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap) }

/-- Native contract value produced by dispatcher lowering when the generated
runtime also includes the native `mappingSlot` helper. -/
private abbrev nativeContractOfDispatcherWithMapping
    (dispatcher : List EvmYul.Yul.Ast.Stmt) :
    EvmYul.Yul.Ast.YulContract :=
  { dispatcher := .Block dispatcher
    functions :=
      ((∅ : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap).insert
        "mappingSlot"
        Compiler.Proofs.YulGeneration.Backends.Native.nativeMappingSlotFunctionDefinition) }

/-- Mapping-helper generated-runtime contract with the init prefix followed by
the dispatcher lowering. -/
private abbrev nativeContractOfInitPrefixedDispatcherWithMapping
    (dispatcher : List EvmYul.Yul.Ast.Stmt) :
    EvmYul.Yul.Ast.YulContract :=
  { dispatcher := .Block (nativeInitFreeMemoryPointerStmt :: dispatcher)
    functions :=
      ((∅ : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap).insert
        "mappingSlot"
        Compiler.Proofs.YulGeneration.Backends.Native.nativeMappingSlotFunctionDefinition) }

/-- Function-level native-fragment body shape from static scalar parameter loads plus
a body-code shape witness. This isolates the shared append/prologue reasoning
needed before the public generated-native wrappers can derive their own
external-body witnesses from compiler output. -/
private theorem compileFunctionSpec_noFuncDefs_of_static_params_and_body
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef)
    (selector : Nat) (spec : CompilationModel.FunctionSpec)
    (irFn : IRFunction)
    (hStaticParams :
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams spec.params)
    (hBodyNoFuncDefs :
      ∀ bodyStmts,
        CompilationModel.compileStmtList fields events errors .calldata [] false
          (spec.bindingParams.map (·.name)) [] spec.body = Except.ok bodyStmts →
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
          bodyStmts = false)
    (hcompile :
      CompilationModel.compileFunctionSpec fields events errors [] selector spec =
        Except.ok irFn) :
    Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
      irFn.body = false := by
  rcases Compiler.Proofs.IRGeneration.FunctionShape.compileFunctionSpec_ok_components
      fields events errors selector spec irFn hcompile with
    ⟨returns, bodyStmts, _hvalidate, _hreturns, hbody, hirFn⟩
  subst irFn
  change
    Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
      (CompilationModel.genParamLoads spec.bindingParams ++ bodyStmts) = false
  simp [
    Compiler.Proofs.YulGeneration.Backends.genParamLoads_static_scalar_noFuncDefs
      spec.bindingParams (by
        cases h : spec.abiDecoding
        · simpa [CompilationModel.FunctionSpec.bindingParams, h] using hStaticParams
        · simp [CompilationModel.FunctionSpec.bindingParams, h,
            Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams]),
    hBodyNoFuncDefs bodyStmts hbody]

private theorem compileFunctionSpec_noFuncDefs_of_safe_static_params
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef)
    (selector : Nat) (spec : CompilationModel.FunctionSpec)
    (irFn : IRFunction)
    (hStaticParams :
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams spec.params)
    (hSafeBody :
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        fields errors .calldata [] false spec.body)
    (hcompile :
      CompilationModel.compileFunctionSpec fields events errors [] selector spec =
        Except.ok irFn) :
    Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
      irFn.body = false := by
  rcases Compiler.Proofs.IRGeneration.FunctionShape.compileFunctionSpec_ok_components
      fields events errors selector spec irFn hcompile with
    ⟨returns, bodyStmts, _hvalidate, _hreturns, hbody, hirFn⟩
  subst irFn
  change
    Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
      (CompilationModel.genParamLoads spec.bindingParams ++ bodyStmts) = false
  simp [
    Compiler.Proofs.YulGeneration.Backends.genParamLoads_static_scalar_noFuncDefs
      spec.bindingParams (by
        cases h : spec.abiDecoding
        · simpa [CompilationModel.FunctionSpec.bindingParams, h] using hStaticParams
        · simp [CompilationModel.FunctionSpec.bindingParams, h,
            Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams]),
    Compiler.Proofs.YulGeneration.Backends.compileStmtList_always_noFuncDefs
      fields events errors .calldata [] false spec.body
      (spec.bindingParams.map (·.name)) hSafeBody hbody]

/-- Convert the new source-level safe-body closure theorem into the low-level
`BridgedStmts fn.body` witness still consumed by the EVMYulLean runtime
retargeting theorem. This is the key local bridge from compiler-produced
`FunctionSpec` bodies to emitted IR function bodies: static scalar parameter
loads are bridged by the prologue theorem, and the compiled source body is
bridged by `compileStmtList_always_bridged`. -/
private theorem compileFunctionSpec_bridged_of_safe_static_params
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef)
    (selector : Nat) (spec : CompilationModel.FunctionSpec)
    (irFn : IRFunction)
    (hStaticParams :
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams spec.params)
    (hSafeBody :
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        fields errors .calldata [] false spec.body)
    (hcompile :
      CompilationModel.compileFunctionSpec fields events errors [] selector spec =
        Except.ok irFn) :
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts irFn.body := by
  rcases Compiler.Proofs.IRGeneration.FunctionShape.compileFunctionSpec_ok_components
      fields events errors selector spec irFn hcompile with
    ⟨returns, bodyStmts, _hvalidate, _hreturns, hbody, hirFn⟩
  subst irFn
  change
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts
      (CompilationModel.genParamLoads spec.bindingParams ++ bodyStmts)
  exact Compiler.Proofs.YulGeneration.Backends.BridgedStmts_append
    (Compiler.Proofs.YulGeneration.Backends.genParamLoads_static_scalar_bridged
      spec.bindingParams (by
        cases h : spec.abiDecoding
        · simpa [CompilationModel.FunctionSpec.bindingParams, h] using hStaticParams
        · simp [CompilationModel.FunctionSpec.bindingParams, h,
            Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams]))
    (Compiler.Proofs.YulGeneration.Backends.compileStmtList_always_bridged
      fields events errors .calldata [] false spec.body
      (spec.bindingParams.map (·.name)) hSafeBody hbody)

/-- Lift the one-function bridge closure theorem across the compiled external
function table. This keeps the public EndToEnd theorem from exposing raw
`BridgedStmts fn.body` obligations when callers already have source-level
safe-body/static-param witnesses for every selector-dispatched function. -/
private theorem compiledExternalFunctions_bridged_of_safe_static
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef) :
    ∀ {entries : List (CompilationModel.FunctionSpec × Nat)}
      {irFns : List IRFunction},
      List.Forall₂
        (fun entry irFn =>
          CompilationModel.compileFunctionSpec fields events errors
            [] entry.2 entry.1 = Except.ok irFn)
        entries irFns →
      (∀ entry, entry ∈ entries →
        Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams
          entry.1.params) →
      (∀ entry, entry ∈ entries →
        Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
          fields errors .calldata [] false entry.1.body) →
      ∀ irFn, irFn ∈ irFns →
        Compiler.Proofs.YulGeneration.Backends.BridgedStmts irFn.body := by
  intro entries irFns hcompiled hStatic hSafe
  induction hcompiled with
  | nil =>
      intro irFn hmem
      cases hmem
  | @cons entry irFn entries irFns hhead htail ih =>
      intro target hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmemTail
      · exact compileFunctionSpec_bridged_of_safe_static_params
          fields events errors entry.2 entry.1 target
          (hStatic entry (by simp))
          (hSafe entry (by simp))
          hhead
      · exact ih
          (fun next hnext => hStatic next (by simp [hnext]))
          (fun next hnext => hSafe next (by simp [hnext]))
          target hmemTail

/-- Lift function-level native-fragment body shape across the compiled external
function table. This is the no-`funcDef` analogue of
`compiledExternalFunctions_bridged_of_safe_static`, staged separately because
the body-shape source predicate is still being proved fragment by fragment. -/
private theorem compiledExternalFunctions_noFuncDefs_of_static_params_and_body
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef) :
    ∀ {entries : List (CompilationModel.FunctionSpec × Nat)}
      {irFns : List IRFunction},
      List.Forall₂
        (fun entry irFn =>
          CompilationModel.compileFunctionSpec fields events errors
            [] entry.2 entry.1 = Except.ok irFn)
        entries irFns →
      (∀ entry, entry ∈ entries →
        Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams
          entry.1.params) →
      (∀ entry, entry ∈ entries →
        ∀ bodyStmts,
          CompilationModel.compileStmtList fields events errors .calldata [] false
            (entry.1.bindingParams.map (·.name)) [] entry.1.body =
              Except.ok bodyStmts →
          Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
            bodyStmts = false) →
      ∀ irFn, irFn ∈ irFns →
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
          irFn.body = false := by
  intro entries irFns hcompiled hStatic hBody
  induction hcompiled with
  | nil =>
      intro irFn hmem
      cases hmem
  | @cons entry irFn entries irFns hhead htail ih =>
      intro target hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmemTail
      · exact compileFunctionSpec_noFuncDefs_of_static_params_and_body
          fields events errors entry.2 entry.1 target
          (hStatic entry (by simp))
          (hBody entry (by simp))
          hhead
      · exact ih
          (fun next hnext => hStatic next (by simp [hnext]))
          (fun next hnext => hBody next (by simp [hnext]))
          target hmemTail

private theorem compiledExternalFunctions_noFuncDefs_of_safe_static
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef) :
    ∀ {entries : List (CompilationModel.FunctionSpec × Nat)}
      {irFns : List IRFunction},
      List.Forall₂
        (fun entry irFn =>
          CompilationModel.compileFunctionSpec fields events errors
            [] entry.2 entry.1 = Except.ok irFn)
        entries irFns →
      (∀ entry, entry ∈ entries →
        Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams
          entry.1.params) →
      (∀ entry, entry ∈ entries →
        Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
          fields errors .calldata [] false entry.1.body) →
      ∀ irFn, irFn ∈ irFns →
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
          irFn.body = false := by
  intro entries irFns hcompiled hStatic hSafe
  induction hcompiled with
  | nil =>
      intro irFn hmem
      cases hmem
  | @cons entry irFn entries irFns hhead htail ih =>
      intro target hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmemTail
      · exact compileFunctionSpec_noFuncDefs_of_safe_static_params
          fields events errors entry.2 entry.1 target
          (hStatic entry (by simp))
          (hSafe entry (by simp))
          hhead
      · exact ih
          (fun next hnext => hStatic next (by simp [hnext]))
          (fun next hnext => hSafe next (by simp [hnext]))
          target hmemTail

/-! ## Layers 2+3 Composition -/

/-- Supported compiler output has a unique generated-runtime helper prefix.

`SupportedSpec` rules out emitted internal helper definitions, leaving only the
optional mapping-slot helper in the generated runtime prefix. -/
private theorem isStaticScalarParamType_of_supportedExternalParamType
    {ty : CompilationModel.ParamType}
    (hSupported : SupportedExternalScalarParamType ty) :
    Compiler.Proofs.YulGeneration.Backends.IsStaticScalarParamType ty := by
  cases ty <;> simp [SupportedExternalScalarParamType] at hSupported
  all_goals
    exact Compiler.Proofs.YulGeneration.Backends.IsStaticScalarParamType.scalar
      (by trivial)

private theorem allStaticScalarParams_of_supportedExternalParams
    {params : List CompilationModel.Param}
    (hSupported :
      ∀ param ∈ params, SupportedExternalScalarParamType param.ty) :
    Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams params := by
  intro param hmem
  exact isStaticScalarParamType_of_supportedExternalParamType
    (hSupported param hmem)

private theorem generatedRuntimeStaticScalarParams_of_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams
        entry.1.params := by
  intro entry hentry
  have hfn : entry.1 ∈ selectorDispatchedFunctions spec := by
    simpa [SourceSemantics.selectorFunctionPairs] using
      (List.of_mem_zip hentry).1
  exact allStaticScalarParams_of_supportedExternalParams
    (hSupported.selectorFunctionParamsSupported hfn)

private theorem generatedRuntimeStaticScalarParams_of_supported_except_mapping_writes
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams
        entry.1.params := by
  intro entry hentry
  have hfn : entry.1 ∈ selectorDispatchedFunctions spec := by
    simpa [SourceSemantics.selectorFunctionPairs] using
      (List.of_mem_zip hentry).1
  exact allStaticScalarParams_of_supportedExternalParams
    (hSupported.selectorFunctionParamsSupported hfn)

private theorem exists_left_of_forall₂_mem_right
    {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (hrel : List.Forall₂ R xs ys) :
    ∀ {y}, y ∈ ys → ∃ x, x ∈ xs ∧ R x y := by
  intro y hy
  induction hrel with
  | nil =>
      simp at hy
  | @cons headX headY tailX tailY hhead htail ih =>
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hyTail
      · exact ⟨headX, by simp, hhead⟩
      · rcases ih hyTail with ⟨x, hx, hRx⟩
        exact ⟨x, by simp [hx], hRx⟩

private theorem snd_mem_of_mem_zip
    {α β : Type} {xs : List α} {ys : List β} {x : α} {y : β}
    (hmem : (x, y) ∈ xs.zip ys) :
    y ∈ ys := by
  induction xs generalizing ys with
  | nil =>
      simp at hmem
  | cons head tail ih =>
      cases ys with
      | nil =>
          simp at hmem
      | cons yHead yTail =>
          simp only [List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · cases hhead
            simp
          · exact List.mem_cons_of_mem yHead (ih htail)

private theorem selectorModulus_lt_uint256 :
    Compiler.Constants.selectorModulus < EvmYul.UInt256.size := by
  norm_num [Compiler.Constants.selectorModulus, EvmYul.UInt256.size]

theorem generatedRuntimeFunctionSelectorsRange_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus) :
    ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size := by
  intro fn hmem
  have hCompiled :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions
      spec selectors hSupported irContract hCompile
  rcases exists_left_of_forall₂_mem_right hCompiled hmem with
    ⟨entry, hentryMem, hCompileFn⟩
  have hSelectorEq :
      fn.selector = entry.2 :=
    Compiler.Proofs.IRGeneration.Function.compileFunctionSpec_ok_selector
      spec.fields spec.events spec.errors entry.2 entry.1 fn hCompileFn
  have hSelectorMem : entry.2 ∈ selectors := by
    simpa [SourceSemantics.selectorFunctionPairs] using
      (snd_mem_of_mem_zip hentryMem)
  rw [hSelectorEq]
  exact Nat.lt_trans (hSelectorsRange entry.2 hSelectorMem)
    selectorModulus_lt_uint256

theorem generatedRuntimeFunctionSelectorsSelectorRange_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus) :
    ∀ fn, fn ∈ irContract.functions →
      fn.selector < Compiler.Constants.selectorModulus := by
  intro fn hmem
  have hCompiled :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions
      spec selectors hSupported irContract hCompile
  rcases exists_left_of_forall₂_mem_right hCompiled hmem with
    ⟨entry, hentryMem, hCompileFn⟩
  have hSelectorEq :
      fn.selector = entry.2 :=
    Compiler.Proofs.IRGeneration.Function.compileFunctionSpec_ok_selector
      spec.fields spec.events spec.errors entry.2 entry.1 fn hCompileFn
  have hSelectorMem : entry.2 ∈ selectors := by
    simpa [SourceSemantics.selectorFunctionPairs] using
      (snd_mem_of_mem_zip hentryMem)
  rw [hSelectorEq]
  exact hSelectorsRange entry.2 hSelectorMem

theorem generatedRuntimeFunctionSelectorsRange_of_compile_ok_supported_except_mapping_writes
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus) :
    ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size := by
  intro fn hmem
  have hCompiled :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions_except_mapping_writes
      spec selectors hSupported irContract hCompile
  rcases exists_left_of_forall₂_mem_right hCompiled hmem with
    ⟨entry, hentryMem, hCompileFn⟩
  have hSelectorEq :
      fn.selector = entry.2 :=
    Compiler.Proofs.IRGeneration.Function.compileFunctionSpec_ok_selector
      spec.fields spec.events spec.errors entry.2 entry.1 fn hCompileFn
  have hSelectorMem : entry.2 ∈ selectors := by
    simpa [SourceSemantics.selectorFunctionPairs] using
      (snd_mem_of_mem_zip hentryMem)
  rw [hSelectorEq]
  exact Nat.lt_trans (hSelectorsRange entry.2 hSelectorMem)
    selectorModulus_lt_uint256

theorem generatedRuntimeFunctionSelectorsSelectorRange_of_compile_ok_supported_except_mapping_writes
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus) :
    ∀ fn, fn ∈ irContract.functions →
      fn.selector < Compiler.Constants.selectorModulus := by
  intro fn hmem
  have hCompiled :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions_except_mapping_writes
      spec selectors hSupported irContract hCompile
  rcases exists_left_of_forall₂_mem_right hCompiled hmem with
    ⟨entry, hentryMem, hCompileFn⟩
  have hSelectorEq :
      fn.selector = entry.2 :=
    Compiler.Proofs.IRGeneration.Function.compileFunctionSpec_ok_selector
      spec.fields spec.events spec.errors entry.2 entry.1 fn hCompileFn
  have hSelectorMem : entry.2 ∈ selectors := by
    simpa [SourceSemantics.selectorFunctionPairs] using
      (snd_mem_of_mem_zip hentryMem)
  rw [hSelectorEq]
  exact hSelectorsRange entry.2 hSelectorMem

private theorem selector_eq_of_find_function_by_selector
    {functions : List IRFunction} {selector : Nat} {fn : IRFunction}
    (hFind : functions.find? (fun fn => fn.selector == selector) = some fn) :
    fn.selector = selector := by
  induction functions with
  | nil =>
      simp at hFind
  | cons head tail ih =>
      by_cases hHead : head.selector = selector
      · simp [hHead] at hFind
        exact hFind ▸ hHead
      · simp [hHead] at hFind
        exact ih hFind

theorem selectedGeneratedFunctionSelectorRange_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {tx : IRTransaction} {fn : IRFunction}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn) :
    tx.functionSelector < Compiler.Constants.selectorModulus := by
  have hFnRange :=
    generatedRuntimeFunctionSelectorsSelectorRange_of_compile_ok_supported
      hCompile hSupported hSelectorsRange fn (List.mem_of_find?_eq_some hFind)
  have hEq := selector_eq_of_find_function_by_selector hFind
  simpa [hEq] using hFnRange

theorem selectedGeneratedFunctionSelectorRange_of_compile_ok_supported_except_mapping_writes
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {tx : IRTransaction} {fn : IRFunction}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn) :
    tx.functionSelector < Compiler.Constants.selectorModulus := by
  have hFnRange :=
    generatedRuntimeFunctionSelectorsSelectorRange_of_compile_ok_supported_except_mapping_writes
      hCompile hSupported hSelectorsRange fn (List.mem_of_find?_eq_some hFind)
  have hEq := selector_eq_of_find_function_by_selector hFind
  simpa [hEq] using hFnRange

/-- Selector-dispatched source functions in a `SupportedSpec` expose their
body-level `SupportedStmtList` witness directly.

This is the source-side entry point for the generated-runtime closure proofs:
the witness is pulled from
`hSupported.supportedFunctionOfSelectorDispatched ... .body.stmtList` for each
function paired with a selector. -/
theorem generatedRuntimeSupportedStmtList_of_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      SupportedStmtList spec.fields (entry.1.params.map (·.name))
        entry.1.body := by
  intro entry hentry
  have hfn : entry.1 ∈ selectorDispatchedFunctions spec := by
    simpa [SourceSemantics.selectorFunctionPairs] using
      (List.of_mem_zip hentry).1
  exact (hSupported.supportedFunctionOfSelectorDispatched hfn).body.stmtList

/-- Direct source-function form of the supported body statement-list witness.

This is the raw `SupportedSpec.functions ... body.stmtList` entry point; the
selector-pair theorem above is the generated-runtime specialization. -/
theorem supportedFunctionSupportedStmtList_of_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ fn, fn ∈ spec.functions →
      SupportedStmtList spec.fields (fn.params.map (·.name)) fn.body := by
  intro fn hmem
  exact (hSupported.functions fn hmem).body.stmtList

private theorem stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites_append
    (pfx sfx : List CompilationModel.Stmt) :
    stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites (pfx ++ sfx) =
      (stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites pfx ||
        stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites sfx) := by
  induction pfx with
  | nil =>
      simp [stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites, ih,
        Bool.or_assoc]

private theorem stmtTouchesUnsupportedStateSurface_eq_false_of_mem
    {stmt : CompilationModel.Stmt} {stmts : List CompilationModel.Stmt}
    (hState : stmtListTouchesUnsupportedStateSurface stmts = false)
    (hmem : stmt ∈ stmts) :
    stmtTouchesUnsupportedStateSurface stmt = false := by
  induction stmts with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      simp only [stmtListTouchesUnsupportedStateSurface, Bool.or_eq_false_iff] at hState
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hState.1
      · exact ih hState.2 hmem

private theorem stmtMappingWriteSlotSafe_of_stateSurfaceClosed
    {fields : List CompilationModel.Field} {stmt : CompilationModel.Stmt}
    (hState : stmtTouchesUnsupportedStateSurface stmt = false) :
    StmtMappingWriteSlotSafe fields stmt := by
  cases stmt <;>
    simp [StmtMappingWriteSlotSafe, stmtTouchesUnsupportedStateSurface] at hState ⊢

private theorem stmtMappingWriteSlotSafe_of_supported_stateClosed
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      ∀ stmt, stmt ∈ entry.1.body →
        StmtMappingWriteSlotSafe spec.fields stmt := by
  intro entry hentry stmt hmem
  have hfn : entry.1 ∈ selectorDispatchedFunctions spec := by
    simpa [SourceSemantics.selectorFunctionPairs] using
      (List.of_mem_zip hentry).1
  exact stmtMappingWriteSlotSafe_of_stateSurfaceClosed
    (stmtTouchesUnsupportedStateSurface_eq_false_of_mem
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body.state.surfaceClosed
      hmem)

private theorem stmtListTouchesUnsupportedEffectSurface_append
    (pfx sfx : List CompilationModel.Stmt) :
    stmtListTouchesUnsupportedEffectSurface (pfx ++ sfx) =
      (stmtListTouchesUnsupportedEffectSurface pfx ||
        stmtListTouchesUnsupportedEffectSurface sfx) := by
  induction pfx with
  | nil =>
      simp [stmtListTouchesUnsupportedEffectSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedEffectSurface, ih, Bool.or_assoc]

private theorem stmtListTouchesUnsupportedCallSurface_append
    (pfx sfx : List CompilationModel.Stmt) :
    stmtListTouchesUnsupportedCallSurface (pfx ++ sfx) =
      (stmtListTouchesUnsupportedCallSurface pfx ||
        stmtListTouchesUnsupportedCallSurface sfx) := by
  induction pfx with
  | nil =>
      simp [stmtListTouchesUnsupportedCallSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedCallSurface, ih, Bool.or_assoc]

/-- Helper for `setMappingUintSingle` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_setMappingUintSingle_of_safety
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {fieldName : String}
    {key value : CompilationModel.Expr}
    (hKey : FunctionBody.ExprCompileCore key) (hValue : FunctionBody.ExprCompileCore value)
    (hSafety : ∀ stmt ∈ [CompilationModel.Stmt.setMappingUint fieldName key value],
      StmtMappingWriteSlotSafe fields stmt) :
    BridgedSafeStmts fields errors dynamicSource [] false
      [.setMappingUint fieldName key value] := by
  rcases hSafety (.setMappingUint fieldName key value) (by simp) with
    ⟨safeSlot, _hFind, hMapping, hSlots, _hSlotSafety⟩
  exact bridgedSafeStmts_setMappingUintSingleSlot (slot := safeSlot)
    (bridgedSourceExpr_of_exprCompileCore hKey)
    (bridgedSourceExpr_of_exprCompileCore hValue) hMapping hSlots

/-- Helper for `setMappingChainSingle` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_setMappingChainSingle_of_safety
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {fieldName : String}
    {keys : List CompilationModel.Expr} {value : CompilationModel.Expr}
    (hKeys : ∀ key ∈ keys, FunctionBody.ExprCompileCore key)
    (hValue : FunctionBody.ExprCompileCore value)
    (hSafety : ∀ stmt ∈ [CompilationModel.Stmt.setMappingChain fieldName keys value],
      StmtMappingWriteSlotSafe fields stmt) :
    BridgedSafeStmts fields errors dynamicSource [] false
      [.setMappingChain fieldName keys value] := by
  rcases hSafety (.setMappingChain fieldName keys value) (by simp) with
    ⟨safeSlot, _hFind, hMapping, hSlots, _hSlotSafety⟩
  exact bridgedSafeStmts_setMappingChainSingleSlot (slot := safeSlot)
    (fun key hMem => bridgedSourceExpr_of_exprCompileCore (hKeys key hMem))
    (bridgedSourceExpr_of_exprCompileCore hValue) hMapping hSlots

/-- Helper for `setMappingSingle` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_setMappingSingle_of_safety
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {fieldName : String}
    {key value : CompilationModel.Expr}
    (hKey : FunctionBody.ExprCompileCore key) (hValue : FunctionBody.ExprCompileCore value)
    (hSafety : ∀ stmt ∈ [CompilationModel.Stmt.setMapping fieldName key value],
      StmtMappingWriteSlotSafe fields stmt) :
    BridgedSafeStmts fields errors dynamicSource [] false
      [.setMapping fieldName key value] := by
  rcases hSafety (.setMapping fieldName key value) (by simp) with
    ⟨safeSlot, _hFind, hMapping, hSlots, _hSlotSafety⟩
  exact bridgedSafeStmts_setMappingSingleSlot (slot := safeSlot)
    (bridgedSourceExpr_of_exprCompileCore hKey)
    (bridgedSourceExpr_of_exprCompileCore hValue) hMapping hSlots

/-- Helper for `setMappingWordSingle` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_setMappingWordSingle_of_safety
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {fieldName : String}
    {key value : CompilationModel.Expr} {wordOffset : Nat}
    (hKey : FunctionBody.ExprCompileCore key) (hValue : FunctionBody.ExprCompileCore value)
    (hSafety : ∀ stmt ∈ [CompilationModel.Stmt.setMappingWord fieldName key wordOffset value],
      StmtMappingWriteSlotSafe fields stmt) :
    BridgedSafeStmts fields errors dynamicSource [] false
      [.setMappingWord fieldName key wordOffset value] := by
  rcases hSafety (.setMappingWord fieldName key wordOffset value) (by simp) with
    ⟨safeSlot, _hFind, hMapping, hSlots, _hSlotSafety⟩
  by_cases hZero : wordOffset = 0
  · exact bridgedSafeStmts_setMappingWordSingleSlot (slot := safeSlot)
      (bridgedSourceExpr_of_exprCompileCore hKey)
      (bridgedSourceExpr_of_exprCompileCore hValue) hMapping hSlots hZero
  · exact bridgedSafeStmts_setMappingWordSingleSlotNonzero (slot := safeSlot)
      (bridgedSourceExpr_of_exprCompileCore hKey)
      (bridgedSourceExpr_of_exprCompileCore hValue) hMapping hSlots hZero

/-- Helper for `setMappingPackedWordSingle` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_setMappingPackedWordSingle_of_safety
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {fieldName : String}
    {key value : CompilationModel.Expr} {wordOffset : Nat}
    {packed : CompilationModel.PackedBits}
    (hKey : FunctionBody.ExprCompileCore key) (hValue : FunctionBody.ExprCompileCore value)
    (hPacked : CompilationModel.packedBitsValid packed = true)
    (hSafety : ∀ stmt ∈ [CompilationModel.Stmt.setMappingPackedWord fieldName key wordOffset packed value],
      StmtMappingWriteSlotSafe fields stmt) :
    BridgedSafeStmts fields errors dynamicSource [] false
      [.setMappingPackedWord fieldName key wordOffset packed value] := by
  rcases hSafety (.setMappingPackedWord fieldName key wordOffset packed value) (by simp) with
    ⟨safeSlot, _hFind, hMapping, hSlots, _hSlotSafety⟩
  by_cases hZero : wordOffset = 0
  · exact bridgedSafeStmts_setMappingPackedWordSingleSlot (slot := safeSlot)
      (bridgedSourceExpr_of_exprCompileCore hKey)
      (bridgedSourceExpr_of_exprCompileCore hValue) hMapping hSlots hZero hPacked
  · exact BridgedSafeStmts.mappingPackedWordNonzero (by
      intro stmt hMem
      simp only [List.mem_singleton] at hMem
      subst stmt
      exact BridgedSourceMappingPackedWordNonzeroStmt.setMappingPackedWord fieldName packed
        (bridgedSourceExpr_of_exprCompileCore hKey)
        (bridgedSourceExpr_of_exprCompileCore hValue) hMapping hSlots hZero hPacked)

/-- Helper for `setStructMemberSingle` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_setStructMemberSingle_of_safety
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {fieldName memberName : String}
    {key value : CompilationModel.Expr}
    (hKey : FunctionBody.ExprCompileCore key) (hValue : FunctionBody.ExprCompileCore value)
    (hSafety : ∀ stmt ∈ [CompilationModel.Stmt.setStructMember fieldName key memberName value],
      StmtMappingWriteSlotSafe fields stmt) :
    BridgedSafeStmts fields errors dynamicSource [] false
      [.setStructMember fieldName key memberName value] := by
  rcases hSafety (.setStructMember fieldName key memberName value) (by simp) with
    ⟨safeSlot, safeWordOffset, safeMembers, _hFind, hMembers,
      hFindMember, hMapping, hNotMapping2, hSlots, _hSlotSafety⟩
  by_cases hZero : safeWordOffset = 0
  · exact bridgedSafeStmts_setStructMemberSingleSlot (slot := safeSlot)
      (members := safeMembers)
      (member := { name := memberName, wordOffset := safeWordOffset, packed := none })
      (bridgedSourceExpr_of_exprCompileCore hKey)
      (bridgedSourceExpr_of_exprCompileCore hValue)
      hNotMapping2 hMembers hFindMember rfl hZero hMapping hSlots
  · exact bridgedSafeStmts_setStructMemberSingleSlotNonzero (slot := safeSlot)
      (members := safeMembers)
      (member := { name := memberName, wordOffset := safeWordOffset, packed := none })
      (bridgedSourceExpr_of_exprCompileCore hKey)
      (bridgedSourceExpr_of_exprCompileCore hValue)
      hNotMapping2 hMembers hFindMember rfl hZero hMapping hSlots

/-- Helper for `setMapping2Single` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_setMapping2Single_of_safety
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {fieldName : String}
    {key1 key2 value : CompilationModel.Expr}
    (hKey1 : FunctionBody.ExprCompileCore key1) (hKey2 : FunctionBody.ExprCompileCore key2)
    (hValue : FunctionBody.ExprCompileCore value)
    (hSafety : ∀ stmt ∈ [CompilationModel.Stmt.setMapping2 fieldName key1 key2 value],
      StmtMappingWriteSlotSafe fields stmt) :
    BridgedSafeStmts fields errors dynamicSource [] false
      [.setMapping2 fieldName key1 key2 value] := by
  rcases hSafety (.setMapping2 fieldName key1 key2 value) (by simp) with
    ⟨safeSlot, _hFind, hMapping2, hSlots, _hSlotSafety⟩
  exact bridgedSafeStmts_setMapping2SingleSlot (slot := safeSlot)
    (bridgedSourceExpr_of_exprCompileCore hKey1)
    (bridgedSourceExpr_of_exprCompileCore hKey2)
    (bridgedSourceExpr_of_exprCompileCore hValue) hMapping2 hSlots

/-- Helper for `setMapping2WordSingle` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_setMapping2WordSingle_of_safety
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {fieldName : String}
    {key1 key2 value : CompilationModel.Expr} {wordOffset : Nat}
    (hKey1 : FunctionBody.ExprCompileCore key1) (hKey2 : FunctionBody.ExprCompileCore key2)
    (hValue : FunctionBody.ExprCompileCore value)
    (hSafety : ∀ stmt ∈ [CompilationModel.Stmt.setMapping2Word fieldName key1 key2 wordOffset value],
      StmtMappingWriteSlotSafe fields stmt) :
    BridgedSafeStmts fields errors dynamicSource [] false
      [.setMapping2Word fieldName key1 key2 wordOffset value] := by
  rcases hSafety (.setMapping2Word fieldName key1 key2 wordOffset value) (by simp) with
    ⟨safeSlot, _hFind, hMapping2, hSlots, _hSlotSafety⟩
  by_cases hZero : wordOffset = 0
  · exact bridgedSafeStmts_setMapping2WordSingleSlot (slot := safeSlot)
      (bridgedSourceExpr_of_exprCompileCore hKey1)
      (bridgedSourceExpr_of_exprCompileCore hKey2)
      (bridgedSourceExpr_of_exprCompileCore hValue) hMapping2 hSlots hZero
  · exact bridgedSafeStmts_setMapping2WordSingleSlotNonzero (slot := safeSlot)
      (bridgedSourceExpr_of_exprCompileCore hKey1)
      (bridgedSourceExpr_of_exprCompileCore hKey2)
      (bridgedSourceExpr_of_exprCompileCore hValue) hMapping2 hSlots hZero

/-- Helper for `setStructMember2Single` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_setStructMember2Single_of_safety
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {fieldName memberName : String}
    {key1 key2 value : CompilationModel.Expr}
    (hKey1 : FunctionBody.ExprCompileCore key1) (hKey2 : FunctionBody.ExprCompileCore key2)
    (hValue : FunctionBody.ExprCompileCore value)
    (hSafety : ∀ stmt ∈ [CompilationModel.Stmt.setStructMember2 fieldName key1 key2 memberName value],
      StmtMappingWriteSlotSafe fields stmt) :
    BridgedSafeStmts fields errors dynamicSource [] false
      [.setStructMember2 fieldName key1 key2 memberName value] := by
  rcases hSafety (.setStructMember2 fieldName key1 key2 memberName value) (by simp) with
    ⟨safeSlot, safeWordOffset, safeMembers, _hFind, hMembers,
      hFindMember, hMapping2, hSlots, _hSlotSafety⟩
  by_cases hZero : safeWordOffset = 0
  · exact bridgedSafeStmts_setStructMember2SingleSlot (slot := safeSlot)
      (members := safeMembers)
      (member := { name := memberName, wordOffset := safeWordOffset, packed := none })
      (bridgedSourceExpr_of_exprCompileCore hKey1)
      (bridgedSourceExpr_of_exprCompileCore hKey2)
      (bridgedSourceExpr_of_exprCompileCore hValue)
      hMapping2 hMembers hFindMember rfl hZero hSlots
  · exact bridgedSafeStmts_setStructMember2SingleSlotNonzero (slot := safeSlot)
      (members := safeMembers)
      (member := { name := memberName, wordOffset := safeWordOffset, packed := none })
      (bridgedSourceExpr_of_exprCompileCore hKey1)
      (bridgedSourceExpr_of_exprCompileCore hKey2)
      (bridgedSourceExpr_of_exprCompileCore hValue)
      hMapping2 hMembers hFindMember rfl hZero hSlots

/-- Helper for empty literal `forEach` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_forEachLiteralEmpty_single
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {varName : String} {n : Nat} :
    BridgedSafeStmts fields errors dynamicSource [] false
      [.forEach varName (.literal n) []] := by
  exact BridgedSafeStmts.externalRecursiveRawLog
    (.cons (.forEach _ _ _ (.literal _) .nil) .nil)

/-- Helper for `forEachLiteralBounded` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_forEachLiteralBounded_of_except_mapping_writes
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {varName : String}
    (body : List CompilationModel.Stmt)
    (hState : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites
      [.forEach varName (.literal 0) body] = false) :
    BridgedSafeStmts fields errors dynamicSource [] false
      [.forEach varName (.literal 0) body] := by
  cases body with
  | nil => exact bridgedSafeStmts_forEachLiteralEmpty_single
  | cons _ _ =>
      simp [stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites,
        stmtTouchesUnsupportedStateSurfaceExceptMappingWrites,
        stmtTouchesUnsupportedStateSurface] at hState

/-- Helper for literal `forEach` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_forEachLiteralCore_single
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {scope : List String}
    {varName : String} {n : Nat} {body : List CompilationModel.Stmt}
    (hBody : FunctionBody.StmtListCompileCore (varName :: scope) body) :
    BridgedSafeStmts fields errors dynamicSource [] false
      [.forEach varName (.literal n) body] :=
  BridgedSafeStmts.externalRecursiveRawLog
    (.cons (.forEach _ _ _ (.literal _)
      (bridgedSourceExternalRecursiveBodyWithRawLogStmts_of_stmtListCompileCore hBody)) .nil)

/-- Helper for `ite` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_iteCore_single
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {scope : List String}
    {cond : CompilationModel.Expr} {thenBranch elseBranch : List CompilationModel.Stmt}
    (hCond : FunctionBody.ExprCompileCore cond)
    (hThen : FunctionBody.StmtListCompileCore scope thenBranch)
    (hElse : FunctionBody.StmtListCompileCore scope elseBranch) :
    BridgedSafeStmts fields errors dynamicSource [] false
      [.ite cond thenBranch elseBranch] :=
  BridgedSafeStmts.externalRecursiveRawLog
    (.cons (.ite _ _ _ (bridgedSourceExpr_of_exprCompileCore hCond)
      (bridgedSourceExternalRecursiveBodyWithRawLogStmts_of_stmtListCompileCore hThen)
      (bridgedSourceExternalRecursiveBodyWithRawLogStmts_of_stmtListCompileCore hElse)) .nil)

/-- Helper for `requireClause` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_requireClause_of_except_mapping_writes
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource}
    {clause : Verity.Core.Free.RequireLiteralGuardFamilyClause}
    {rest : List CompilationModel.Stmt}
    (hSafety : ∀ stmt ∈ clause.toStmt :: rest, StmtMappingWriteSlotSafe fields stmt)
    (hState : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites (clause.toStmt :: rest) = false)
    (hCall : stmtListTouchesUnsupportedCallSurface (clause.toStmt :: rest) = false)
    (hEffects : stmtListTouchesUnsupportedEffectSurface (clause.toStmt :: rest) = false)
    (ih : (∀ stmt ∈ rest, StmtMappingWriteSlotSafe fields stmt) →
      stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites rest = false →
      stmtListTouchesUnsupportedCallSurface rest = false →
      stmtListTouchesUnsupportedEffectSurface rest = false →
      BridgedSafeStmts fields errors dynamicSource [] false rest) :
    BridgedSafeStmts fields errors dynamicSource [] false (clause.toStmt :: rest) := by
  simpa using BridgedSafeStmts.append
    (bridgedSafeStmts_requireGuardFamilyClause clause)
    (ih (fun stmt hMem => hSafety stmt (by simp [hMem]))
      (by
        simpa [stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites,
          stmtTouchesUnsupportedStateSurfaceExceptMappingWrites,
          Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
          stmtTouchesUnsupportedStateSurface, exprTouchesUnsupportedStateSurface] using
          (Bool.or_eq_false_iff.mp hState).2)
      (by
        simpa [stmtListTouchesUnsupportedCallSurface, stmtTouchesUnsupportedCallSurface,
          Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
          exprTouchesUnsupportedCallSurface] using (Bool.or_eq_false_iff.mp hCall).2)
      (by
        simpa [stmtListTouchesUnsupportedEffectSurface, stmtTouchesUnsupportedEffectSurface,
          Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
          (Bool.or_eq_false_iff.mp hEffects).2))

/-- Helper for `append` in `supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety`. -/
private theorem bridgedSafeStmts_append_of_except_mapping_writes
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource}
    {pfx sfx : List CompilationModel.Stmt}
    (hSafety : ∀ stmt ∈ pfx ++ sfx, StmtMappingWriteSlotSafe fields stmt)
    (hState : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites (pfx ++ sfx) = false)
    (hCall : stmtListTouchesUnsupportedCallSurface (pfx ++ sfx) = false)
    (hEffects : stmtListTouchesUnsupportedEffectSurface (pfx ++ sfx) = false)
    (ihPfx : (∀ stmt ∈ pfx, StmtMappingWriteSlotSafe fields stmt) →
      stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites pfx = false →
      stmtListTouchesUnsupportedCallSurface pfx = false →
      stmtListTouchesUnsupportedEffectSurface pfx = false →
      BridgedSafeStmts fields errors dynamicSource [] false pfx)
    (ihSfx : (∀ stmt ∈ sfx, StmtMappingWriteSlotSafe fields stmt) →
      stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites sfx = false →
      stmtListTouchesUnsupportedCallSurface sfx = false →
      stmtListTouchesUnsupportedEffectSurface sfx = false →
      BridgedSafeStmts fields errors dynamicSource [] false sfx) :
    BridgedSafeStmts fields errors dynamicSource [] false (pfx ++ sfx) := by
  rw [stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites_append] at hState
  rw [stmtListTouchesUnsupportedCallSurface_append] at hCall
  rw [stmtListTouchesUnsupportedEffectSurface_append] at hEffects
  exact BridgedSafeStmts.append
    (ihPfx (fun stmt hMem => hSafety stmt (by simp [hMem]))
      (Bool.or_eq_false_iff.mp hState).1 (Bool.or_eq_false_iff.mp hCall).1
      (Bool.or_eq_false_iff.mp hEffects).1)
    (ihSfx (fun stmt hMem => hSafety stmt (by simp [hMem]))
      (Bool.or_eq_false_iff.mp hState).2 (Bool.or_eq_false_iff.mp hCall).2
      (Bool.or_eq_false_iff.mp hEffects).2)

/-- Generic source-body closure from `SupportedStmtList` to `BridgedSafeStmts`
when mapping writes are allowed by the state-surface gate and supplied with the
body-local slot-safety witness used by the Tier 2 mapping-write theorem.

This is the constructor-facing companion to
`supportedStmtList_safe_of_state_effect_closed`: it does not pretend the
surface predicate itself proves mapping layout facts, but consumes exactly the
extra per-statement facts needed for the mapping-write constructors. -/
theorem supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety
    {fields : List CompilationModel.Field} {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource} {scope : List String}
    {stmts : List CompilationModel.Stmt} (hSupported : SupportedStmtList fields scope stmts)
    (hSafety : ∀ stmt ∈ stmts, StmtMappingWriteSlotSafe fields stmt)
    (hState : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites stmts = false)
    (hCall : stmtListTouchesUnsupportedCallSurface stmts = false)
    (hEffects : stmtListTouchesUnsupportedEffectSurface stmts = false) :
    BridgedSafeStmts fields errors dynamicSource [] false stmts := by
  induction hSupported
  case compileCore hCore => exact bridgedSafeStmts_externalCompileCore hCore
  case terminalCore hCore => exact bridgedSafeStmts_externalTerminalCore hCore
  case setStorageSingleSlot hValue _ hFind => exact bridgedSafeStmts_setStorageSingleSlot_of_exprCompileCore hValue hFind
  case setStorageAddrSingleSlot hValue _ hFind => exact bridgedSafeStmts_setStorageAddrSingleSlot_of_exprCompileCore hValue hFind
  case calldatacopySingle hDest _ hSource _ hSize _ => exact bridgedSafeStmts_calldatacopySingle_of_exprCompileCore hDest hSource hSize
  case returndataCopyEmptySingle hDest _ => exact bridgedSafeStmts_returndataCopyEmptySingle_of_exprCompileCore hDest
  case revertEmptySingle => exact bridgedSafeStmts_revertEmptySingle
  case revertReturndataEmptySingle => exact bridgedSafeStmts_revertReturndataEmptySingle
  case setMappingUintSingle hKey _ hValue _ _ => exact bridgedSafeStmts_setMappingUintSingle_of_safety hKey hValue hSafety
  case setMappingChainSingle hKeys _ hValue _ _ => exact bridgedSafeStmts_setMappingChainSingle_of_safety hKeys hValue hSafety
  case setMappingSingle hKey _ hValue _ _ => exact bridgedSafeStmts_setMappingSingle_of_safety hKey hValue hSafety
  case setMappingWordSingle hKey _ hValue _ _ => exact bridgedSafeStmts_setMappingWordSingle_of_safety hKey hValue hSafety
  case setMappingPackedWordSingle hKey _ hValue _ _ _ _ _ hPacked _ => exact bridgedSafeStmts_setMappingPackedWordSingle_of_safety hKey hValue hPacked hSafety
  case setStructMemberSingle hKey _ hValue _ _ _ _ => exact bridgedSafeStmts_setStructMemberSingle_of_safety hKey hValue hSafety
  case setMapping2Single hKey1 _ hKey2 _ hValue _ _ => exact bridgedSafeStmts_setMapping2Single_of_safety hKey1 hKey2 hValue hSafety
  case setMapping2WordSingle hKey1 _ hKey2 _ hValue _ _ => exact bridgedSafeStmts_setMapping2WordSingle_of_safety hKey1 hKey2 hValue hSafety
  case setStructMember2Single hKey1 _ hKey2 _ hValue _ _ _ _ => exact bridgedSafeStmts_setStructMember2Single_of_safety hKey1 hKey2 hValue hSafety
  case forEachLiteralBounded _ _ body _ _ _ => exact bridgedSafeStmts_forEachLiteralBounded_of_except_mapping_writes body hState
  case forEachLiteralCore _ hBody _ => exact bridgedSafeStmts_forEachLiteralCore_single hBody
  case requireClause _ _ _ ih => exact bridgedSafeStmts_requireClause_of_except_mapping_writes hSafety hState hCall hEffects ih
  case ite hCond _ hThen hElse _ _ => exact bridgedSafeStmts_iteCore_single hCond hThen hElse
  case iteTerminal hCond hBound hThen hElse => exact bridgedSafeStmts_externalTerminalCore (.ite hCond hBound hThen hElse .nil)
  case append _ _ _ _ ihPfx ihSfx => exact bridgedSafeStmts_append_of_except_mapping_writes hSafety hState hCall hEffects ihPfx ihSfx
  all_goals
    simp [stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites,
      stmtTouchesUnsupportedStateSurfaceExceptMappingWrites,
      stmtTouchesUnsupportedStateSurface, exprTouchesUnsupportedStateSurface,
      stmtListTouchesUnsupportedEffectSurface, stmtTouchesUnsupportedEffectSurface,
      stmtListTouchesUnsupportedCallSurface, stmtTouchesUnsupportedCallSurface] at hState hEffects hCall

/-- State-surface closure implies the mapping-write-relaxed state-surface closure. -/
private theorem stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites_of_stateSurfaceClosed
    {stmts : List CompilationModel.Stmt}
    (hState : stmtListTouchesUnsupportedStateSurface stmts = false) :
    stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites stmts = false :=
  stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites_eq_false_of_stateSurface hState

/-- Generic source-body closure from `SupportedStmtList` to
`BridgedSafeStmts` on the helper-free external-call surface.

The state/effect surface-closure premises are the exact negative witnesses
needed to rule out the `SupportedStmtList` constructors that are still outside
the current EVMYulLean bridged-safe fragment. -/
theorem supportedStmtList_safe_of_state_effect_closed
    {fields : List CompilationModel.Field}
    {errors : List CompilationModel.ErrorDef}
    {dynamicSource : CompilationModel.DynamicDataSource}
    {scope : List String} {stmts : List CompilationModel.Stmt}
    (hSupported : SupportedStmtList fields scope stmts)
    (hState : stmtListTouchesUnsupportedStateSurface stmts = false)
    (hCall : stmtListTouchesUnsupportedCallSurface stmts = false)
    (hEffects : stmtListTouchesUnsupportedEffectSurface stmts = false) :
    BridgedSafeStmts fields errors dynamicSource [] false stmts := by
  exact supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety hSupported
    (fun _ hmem => stmtMappingWriteSlotSafe_of_stateSurfaceClosed
      (stmtTouchesUnsupportedStateSurface_eq_false_of_mem hState hmem))
    (stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites_of_stateSurfaceClosed hState)
    hCall hEffects

/-- Every selector-dispatched source function in a `SupportedSpec` has a
`BridgedSafeStmts` body witness.

This composes the body `SupportedStmtList` witness from `SupportedSpec` with
the body-level state/effect closure witnesses stored alongside it. -/
theorem generatedRuntimeSafeBodies_of_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false entry.1.body := by
  intro entry hentry
  have hfn : entry.1 ∈ selectorDispatchedFunctions spec := by
    simpa [SourceSemantics.selectorFunctionPairs] using
      (List.of_mem_zip hentry).1
  exact supportedStmtList_safe_of_state_effect_closed
    (hSupported.supportedFunctionOfSelectorDispatched hfn).body.stmtList
    (hSupported.supportedFunctionOfSelectorDispatched hfn).body.state.surfaceClosed
    (SupportedBodyCallInterface.surfaceClosed
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body)
    (hSupported.supportedFunctionOfSelectorDispatched hfn).body.effects.surfaceClosed

/-- Direct source-function closure from `SupportedSpec.functions` to
`BridgedSafeStmts`.

This theorem is the generic body-level bridge requested by the native proof
pipeline: each source function accepted by `SupportedSpec` has a body admitted
by the `BridgedSafeStmts` whitelist before any compilation/lowering shape is
considered. -/
theorem supportedFunctionBody_safe_of_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ fn, fn ∈ spec.functions →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false fn.body := by
  intro fn hmem
  exact supportedStmtList_safe_of_state_effect_closed
    (supportedFunctionSupportedStmtList_of_supported hSupported fn hmem)
    (hSupported.functions fn hmem).body.state.surfaceClosed
    (SupportedBodyCallInterface.surfaceClosed (hSupported.functions fn hmem).body)
    (hSupported.functions fn hmem).body.effects.surfaceClosed

/-- Direct source-function closure for the weaker mapping-write-supported
surface. Actual mapping-write statements must still carry the local slot-safety
witness consumed by the Tier 2 body bridge. -/
theorem supportedFunctionBody_safe_of_supported_except_mapping_writes_stmt_safety
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ fn, fn ∈ spec.functions →
      (∀ stmt, stmt ∈ fn.body → StmtMappingWriteSlotSafe spec.fields stmt) →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false fn.body := by
  intro fn hmem hSafety
  exact supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety
    (hSupported.functions fn hmem).body.stmtList
    hSafety
    (hSupported.functions fn hmem).body.state.surfaceClosed
    (SupportedBodyCallInterface.surfaceClosed_exceptMappingWrites
      (hSupported.functions fn hmem).body)
    (hSupported.functions fn hmem).body.effects.surfaceClosed

/-- Selector-dispatched source functions in the weaker mapping-write-supported
spec surface have `BridgedSafeStmts` body witnesses when each actual body
mapping-write statement supplies its slot-safety evidence. -/
theorem generatedRuntimeSafeBodies_of_supported_except_mapping_writes_stmt_safety
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (hSafety :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        ∀ stmt, stmt ∈ entry.1.body →
          StmtMappingWriteSlotSafe spec.fields stmt) :
    ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false entry.1.body := by
  intro entry hentry
  have hfn : entry.1 ∈ selectorDispatchedFunctions spec := by
    simpa [SourceSemantics.selectorFunctionPairs] using
      (List.of_mem_zip hentry).1
  exact supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety
    (hSupported.supportedFunctionOfSelectorDispatched hfn).body.stmtList
    (hSafety entry hentry)
    (hSupported.supportedFunctionOfSelectorDispatched hfn).body.state.surfaceClosed
    (SupportedBodyCallInterface.surfaceClosed_exceptMappingWrites
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body)
    (hSupported.supportedFunctionOfSelectorDispatched hfn).body.effects.surfaceClosed

/-- A supported constructor exposes the same source statement-list witness as
ordinary function bodies, scoped by decoded constructor argument aliases and
parameter names. -/
theorem generatedConstructorSupportedStmtList_of_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ ctor, spec.constructor = some ctor →
      SupportedStmtList spec.fields (CompilationModel.constructorBodyScope ctor.params) ctor.body := by
  intro ctor hctor
  exact (hSupported.constructor ctor hctor).stmtList_ctorBody

/-- Constructor user bodies compile under the memory dynamic-data source. When
their body also satisfies the full state/effect closure surface, the same
generic safe-body bridge used by runtime functions applies. This theorem covers
the user-written constructor body; the initcode argument-copy wrapper remains
outside `BridgedStmts` until the initcode-only builtins are added to the bridge
predicate. -/
theorem generatedConstructorSafeBody_of_supported_state_closed
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ ctor, spec.constructor = some ctor →
      stmtListTouchesUnsupportedStateSurface ctor.body = false →
      stmtListTouchesUnsupportedEffectSurface ctor.body = false →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .memory [] false ctor.body := by
  intro ctor hctor hState hEffects
  exact supportedStmtList_safe_of_state_effect_closed
    (dynamicSource := .memory)
    (generatedConstructorSupportedStmtList_of_supported hSupported ctor hctor)
    hState
    (SupportedBodyCallInterface.surfaceClosed_exceptMappingWrites
      (hSupported.constructor ctor hctor).body)
    hEffects

/-- Supported constructors already carry the effect-surface closure witness in
their `SupportedConstructor` body interface. The only remaining explicit
premise here is the stronger state-surface closure, because constructor support
currently stores the weaker except-mapping-writes state interface. -/
theorem generatedConstructorSafeBody_of_supported_state_closed'
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ ctor, spec.constructor = some ctor →
      stmtListTouchesUnsupportedStateSurface ctor.body = false →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .memory [] false ctor.body := by
  intro ctor hctor hState
  exact generatedConstructorSafeBody_of_supported_state_closed
    hSupported ctor hctor hState
    (hSupported.constructor ctor hctor).body.effects.surfaceClosed

/-- Supported constructor bodies compile under the memory dynamic-data source.
For constructors whose supported interface uses the weaker mapping-write state
surface, a per-statement slot-safety witness is enough to obtain the native
safe-body package without requiring the stronger full state-surface premise. -/
theorem generatedConstructorSafeBody_of_supported_stmt_safety
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ ctor, spec.constructor = some ctor →
      (∀ stmt, stmt ∈ ctor.body → StmtMappingWriteSlotSafe spec.fields stmt) →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .memory [] false ctor.body := by
  intro ctor hctor hSafety
  exact supportedStmtList_safe_of_state_except_mapping_writes_stmt_safety
    (dynamicSource := .memory)
    (generatedConstructorSupportedStmtList_of_supported hSupported ctor hctor)
    hSafety
    (hSupported.constructor ctor hctor).body.state.surfaceClosed
    (SupportedBodyCallInterface.surfaceClosed_exceptMappingWrites
      (hSupported.constructor ctor hctor).body)
    (hSupported.constructor ctor hctor).body.effects.surfaceClosed

/-- If a constructor body has a `BridgedSafeStmts` witness, the Yul statements
produced for the user-written constructor body are bridged. This intentionally
talks about the compiled body chunk, not `genConstructorArgLoads`, whose
initcode-only builtins are tracked separately. -/
theorem compileConstructorBody_bridged_of_safe
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef)
    (ctor : CompilationModel.ConstructorSpec)
    (bodyStmts : List Yul.YulStmt)
    (hSafe :
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        fields errors .memory [] false ctor.body)
    (hBody :
      CompilationModel.compileStmtList fields events errors .memory [] false
        (CompilationModel.constructorBodyScope ctor.params) [] ctor.body = .ok bodyStmts) :
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts bodyStmts := by
  exact Compiler.Proofs.YulGeneration.Backends.compileStmtList_always_bridged
    fields events errors .memory [] false ctor.body
    (CompilationModel.constructorBodyScope ctor.params)
    hSafe hBody

/-- Supported constructor user bodies compile to `BridgedStmts` once the
stronger constructor state-surface closure is available. The effect closure is
pulled from `SupportedSpec`; this still excludes the initcode-only argument
copy wrapper. -/
theorem compileConstructorBody_bridged_of_supported_state_closed
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (ctor : CompilationModel.ConstructorSpec)
    (bodyStmts : List Yul.YulStmt)
    (hctor : spec.constructor = some ctor)
    (hState : stmtListTouchesUnsupportedStateSurface ctor.body = false)
    (hBody :
      CompilationModel.compileStmtList spec.fields spec.events spec.errors
        .memory [] false (CompilationModel.constructorBodyScope ctor.params) [] ctor.body =
          .ok bodyStmts) :
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts bodyStmts := by
  exact compileConstructorBody_bridged_of_safe spec.fields spec.events
    spec.errors ctor bodyStmts
    (generatedConstructorSafeBody_of_supported_state_closed'
      hSupported ctor hctor hState)
    hBody

/-- Supported constructor user bodies compile to `BridgedStmts` under the
weaker mapping-write state surface when the body-local mapping-write
slot-safety witness is supplied. -/
theorem compileConstructorBody_bridged_of_supported_stmt_safety
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (ctor : CompilationModel.ConstructorSpec)
    (bodyStmts : List Yul.YulStmt)
    (hctor : spec.constructor = some ctor)
    (hSafety :
      ∀ stmt, stmt ∈ ctor.body → StmtMappingWriteSlotSafe spec.fields stmt)
    (hBody :
      CompilationModel.compileStmtList spec.fields spec.events spec.errors
        .memory [] false (CompilationModel.constructorBodyScope ctor.params) [] ctor.body =
          .ok bodyStmts) :
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts bodyStmts := by
  exact compileConstructorBody_bridged_of_safe spec.fields spec.events
    spec.errors ctor bodyStmts
    (generatedConstructorSafeBody_of_supported_stmt_safety
      hSupported ctor hctor hSafety)
    hBody

/-- Under `SupportedSpec`, successful compilation records the deploy field as
the output of `compileConstructor`. -/
theorem generatedDeploy_compileConstructor_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    CompilationModel.compileConstructor spec.fields spec.events spec.errors []
      spec.constructor = .ok irContract.deploy :=
  Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_deploy_compileConstructor
    spec selectors hSupported irContract hCompile

private theorem generatedRuntimePrefixFunctionNamesUnique_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeFunctionNamesUnique
      ((if irContract.usesMapping then [Compiler.mappingSlotFuncAt 0] else []) ++
        irContract.internalFunctions) = true := by
  have hInternalNil : irContract.internalFunctions = [] :=
    Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_internalFunctions_nil
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  rw [hInternalNil]
  by_cases hUsesMapping : irContract.usesMapping
  · simp [hUsesMapping,
      Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeFunctionNamesUnique,
      Compiler.Proofs.YulGeneration.Backends.Native.stringListHasDuplicate,
      Compiler.mappingSlotFuncAt, Compiler.CodegenCommon.mappingSlotFuncAt]
  · simp [hUsesMapping,
      Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeFunctionNamesUnique,
      Compiler.Proofs.YulGeneration.Backends.Native.stringListHasDuplicate]

private theorem generatedRuntimePrefixFunctionNamesUnique_of_compile_ok_supported_except_mapping_writes
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeFunctionNamesUnique
      ((if irContract.usesMapping then [Compiler.mappingSlotFuncAt 0] else []) ++
        irContract.internalFunctions) = true := by
  have hInternalNil : irContract.internalFunctions = [] :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_internalFunctions_nil_except_mapping_writes
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  rw [hInternalNil]
  by_cases hUsesMapping : irContract.usesMapping
  · simp [hUsesMapping,
      Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeFunctionNamesUnique,
      Compiler.Proofs.YulGeneration.Backends.Native.stringListHasDuplicate,
      Compiler.mappingSlotFuncAt, Compiler.CodegenCommon.mappingSlotFuncAt]
  · simp [hUsesMapping,
      Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeFunctionNamesUnique,
      Compiler.Proofs.YulGeneration.Backends.Native.stringListHasDuplicate]

/-- Supported compiler output has no emitted internal helper statements. This
discharges the generated-runtime fragment's internal-function-shape witness. -/
private theorem generatedRuntimeInternalsAreFuncDefs_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    ∀ stmt, stmt ∈ irContract.internalFunctions →
      ∃ name params rets body, stmt = Yul.YulStmt.funcDef name params rets body := by
  intro stmt hmem
  have hInternalNil : irContract.internalFunctions = [] :=
    Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_internalFunctions_nil
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  rw [hInternalNil] at hmem
  simp at hmem

private theorem generatedRuntimeInternalsAreFuncDefs_of_compile_ok_supported_except_mapping_writes
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ stmt, stmt ∈ irContract.internalFunctions →
      ∃ name params rets body, stmt = Yul.YulStmt.funcDef name params rets body := by
  intro stmt hmem
  have hInternalNil : irContract.internalFunctions = [] :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_internalFunctions_nil_except_mapping_writes
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  rw [hInternalNil] at hmem
  simp at hmem

/-- Every emitted external function body in supported compiler output is in the
native bridgeable Yul subset. -/
theorem generatedRuntimeExternalBodiesBridged_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body :=
  compiledExternalFunctions_bridged_of_safe_static
    spec.fields spec.events spec.errors
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_compiled_functions
      spec selectors hSupported irContract hCompile)
    (generatedRuntimeStaticScalarParams_of_supported hSupported)
    (generatedRuntimeSafeBodies_of_supported hSupported)

/-- Every emitted external function body in the weaker mapping-write-supported
compiler output is in the native bridgeable Yul subset once each actual
mapping-write statement carries slot-safety evidence. -/
theorem generatedRuntimeExternalBodiesBridged_of_compile_ok_supported_except_mapping_writes_stmt_safety
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (hSafety :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        ∀ stmt, stmt ∈ entry.1.body →
          StmtMappingWriteSlotSafe spec.fields stmt) :
    ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body :=
  compiledExternalFunctions_bridged_of_safe_static
    spec.fields spec.events spec.errors
    (Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions_except_mapping_writes
      spec selectors hSupported irContract hCompile)
    (generatedRuntimeStaticScalarParams_of_supported_except_mapping_writes
      hSupported)
    (generatedRuntimeSafeBodies_of_supported_except_mapping_writes_stmt_safety
      hSupported hSafety)

/-- Supported compiler output currently emits no fallback entrypoint, so the
fallback-body bridge obligation consumed by the generic runtime-code bridge is
vacuously discharged. Keeping this as a named theorem makes the
fallback/receive branch of `emitYul` explicit at the end-to-end layer. -/
theorem generatedRuntimeFallbackBodyBridged_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    ∀ fb, irContract.fallbackEntrypoint = some fb →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts fb.body := by
  intro fb hfb
  have hNoFallback :
      irContract.fallbackEntrypoint = none :=
    Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noFallbackEntrypoint
      spec selectors hSupported irContract hCompile
  rw [hNoFallback] at hfb
  simp at hfb

/-- Supported compiler output currently emits no receive entrypoint, so the
receive-body bridge obligation consumed by the generic runtime-code bridge is
vacuously discharged. -/
theorem generatedRuntimeReceiveBodyBridged_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    ∀ rc, irContract.receiveEntrypoint = some rc →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts rc.body := by
  intro rc hrc
  have hNoReceive :
      irContract.receiveEntrypoint = none :=
    Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noReceiveEntrypoint
      spec selectors hSupported irContract hCompile
  rw [hNoReceive] at hrc
  simp at hrc

/-- The weaker mapping-write-supported compiler output also emits no fallback
entrypoint, so the fallback-body bridge obligation is vacuous there too. -/
theorem generatedRuntimeFallbackBodyBridged_of_compile_ok_supported_except_mapping_writes
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ fb, irContract.fallbackEntrypoint = some fb →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts fb.body := by
  intro fb hfb
  have hNoFallback :
      irContract.fallbackEntrypoint = none :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_noFallbackEntrypoint_except_mapping_writes
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  rw [hNoFallback] at hfb
  simp at hfb

/-- The weaker mapping-write-supported compiler output also emits no receive
entrypoint, so the receive-body bridge obligation is vacuous there too. -/
theorem generatedRuntimeReceiveBodyBridged_of_compile_ok_supported_except_mapping_writes
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ rc, irContract.receiveEntrypoint = some rc →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts rc.body := by
  intro rc hrc
  have hNoReceive :
      irContract.receiveEntrypoint = none :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_noReceiveEntrypoint_except_mapping_writes
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  rw [hNoReceive] at hrc
  simp at hrc

private theorem bridgedExpr_dispatch_callvalue :
    BridgedExpr (Compiler.Yul.YulExpr.call "callvalue" []) := by
  exact BridgedExpr.call "callvalue" [] (Or.inl (by simp [bridgedBuiltins]))
    (by intro arg hMem; cases hMem)

private theorem bridgedExpr_dispatch_calldatasize :
    BridgedExpr (Compiler.Yul.YulExpr.call "calldatasize" []) := by
  exact BridgedExpr.call "calldatasize" [] (Or.inl (by simp [bridgedBuiltins]))
    (by intro arg hMem; cases hMem)

private theorem bridgedExpr_dispatch_selector :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "shr"
        [Compiler.Yul.YulExpr.lit Compiler.Constants.selectorShift,
          Compiler.Yul.YulExpr.call "calldataload" [Compiler.Yul.YulExpr.lit 0]]) := by
  refine BridgedExpr.call "shr" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · exact BridgedExpr.lit Compiler.Constants.selectorShift
  · refine BridgedExpr.call "calldataload" _ (Or.inl (by simp [bridgedBuiltins])) ?_
    intro inner hInner
    simp only [List.mem_singleton] at hInner
    subst hInner
    exact BridgedExpr.lit 0

private theorem bridgedExpr_dispatch_calldatasize_lt (n : Nat) :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "lt"
        [Compiler.Yul.YulExpr.call "calldatasize" [],
          Compiler.Yul.YulExpr.lit n]) := by
  refine BridgedExpr.call "lt" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · exact bridgedExpr_dispatch_calldatasize
  · exact BridgedExpr.lit n

private theorem bridgedExpr_dispatch_has_selector :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "iszero"
        [Compiler.Yul.YulExpr.call "lt"
          [Compiler.Yul.YulExpr.call "calldatasize" [],
            Compiler.Yul.YulExpr.lit 4]]) := by
  refine BridgedExpr.call "iszero" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst hMem
  exact bridgedExpr_dispatch_calldatasize_lt 4

private theorem bridgedExpr_dispatch_empty_calldata :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "eq"
        [Compiler.Yul.YulExpr.call "calldatasize" [],
          Compiler.Yul.YulExpr.lit 0]) := by
  refine BridgedExpr.call "eq" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · exact bridgedExpr_dispatch_calldatasize
  · exact BridgedExpr.lit 0

private theorem bridgedExpr_dispatch_iszero_ident (name : String) :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "iszero" [Compiler.Yul.YulExpr.ident name]) := by
  refine BridgedExpr.call "iszero" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst hMem
  exact BridgedExpr.ident name

private theorem callvalueGuard_bridged_local :
    BridgedStmt Compiler.CodegenCommon.callvalueGuard := by
  unfold Compiler.CodegenCommon.callvalueGuard
  exact bridgedStmt_if_of_bridgedStmts bridgedExpr_dispatch_callvalue
    BridgedStmts_singleton_revert_zero

private theorem calldatasizeGuard_bridged_local (numParams : Nat) :
    BridgedStmt (Compiler.CodegenCommon.calldatasizeGuard numParams) := by
  unfold Compiler.CodegenCommon.calldatasizeGuard
  exact bridgedStmt_if_of_bridgedStmts
    (bridgedExpr_dispatch_calldatasize_lt (4 + numParams * 32))
    BridgedStmts_singleton_revert_zero

private theorem dispatchBody_bridged_local (payable : Bool) (label : String)
    (body : List Compiler.Yul.YulStmt) (hBody : BridgedStmts body) :
    BridgedStmts (Compiler.CodegenCommon.dispatchBody payable label body) := by
  unfold Compiler.CodegenCommon.dispatchBody
  cases payable <;>
    simp only [Bool.false_eq_true, ite_false, ite_true,
      List.singleton_append]
  · exact BridgedStmts_cons_comment label
      (BridgedStmts_cons callvalueGuard_bridged_local hBody)
  · exact BridgedStmts_cons_comment label hBody

private theorem defaultDispatchCase_bridged_local
    (fallback receive : Option Compiler.IREntrypoint)
    (hFallback : ∀ fb, fallback = some fb → BridgedStmts fb.body)
    (hReceive : ∀ rc, receive = some rc → BridgedStmts rc.body) :
    BridgedStmts
      (Compiler.CodegenCommon.defaultDispatchCase fallback receive) := by
  cases receive with
  | none =>
      cases fallback with
      | none =>
          unfold Compiler.CodegenCommon.defaultDispatchCase
          exact BridgedStmts_singleton_revert_zero
      | some fb =>
          unfold Compiler.CodegenCommon.defaultDispatchCase
          exact dispatchBody_bridged_local fb.payable "fallback()" fb.body
            (hFallback fb rfl)
  | some rc =>
      cases fallback with
      | none =>
          unfold Compiler.CodegenCommon.defaultDispatchCase
          refine BridgedStmts_singleton_block ?_
          exact BridgedStmts_cons_let "__is_empty_calldata" _
            bridgedExpr_dispatch_empty_calldata
            (BridgedStmts_cons_if
              (BridgedExpr.ident "__is_empty_calldata")
              (dispatchBody_bridged_local rc.payable "receive()" rc.body
                (hReceive rc rfl))
              (BridgedStmts_cons_if
                (bridgedExpr_dispatch_iszero_ident "__is_empty_calldata")
                BridgedStmts_singleton_revert_zero
                BridgedStmts_nil))
      | some fb =>
          unfold Compiler.CodegenCommon.defaultDispatchCase
          refine BridgedStmts_singleton_block ?_
          exact BridgedStmts_cons_let "__is_empty_calldata" _
            bridgedExpr_dispatch_empty_calldata
            (BridgedStmts_cons_if
              (BridgedExpr.ident "__is_empty_calldata")
              (dispatchBody_bridged_local rc.payable "receive()" rc.body
                (hReceive rc rfl))
              (BridgedStmts_cons_if
                (bridgedExpr_dispatch_iszero_ident "__is_empty_calldata")
                (dispatchBody_bridged_local fb.payable "fallback()" fb.body
                  (hFallback fb rfl))
                BridgedStmts_nil))

private theorem switchCases_bridged_local
    (funcs : List Compiler.IRFunction)
    (hFunctions : ∀ fn, fn ∈ funcs → BridgedStmts fn.body) :
    ∀ scrutinee value body,
      (funcs.map (fun fn =>
        (fn.selector,
          Compiler.CodegenCommon.dispatchBody fn.payable s!"{fn.name}()"
            ([Compiler.CodegenCommon.calldatasizeGuard fn.params.length] ++
              fn.body)))).find?
            (fun x => decide (x.fst = scrutinee)) =
          some (value, body) →
      BridgedStmts body := by
  intro scrutinee value body hFind
  have hMem :
      (value, body) ∈ funcs.map (fun fn =>
        (fn.selector,
          Compiler.CodegenCommon.dispatchBody fn.payable s!"{fn.name}()"
            ([Compiler.CodegenCommon.calldatasizeGuard fn.params.length] ++
              fn.body))) :=
    List.mem_of_find?_eq_some hFind
  rcases List.mem_map.mp hMem with ⟨fn, hFn, hEq⟩
  cases hEq
  exact dispatchBody_bridged_local fn.payable s!"{fn.name}()"
    ([Compiler.CodegenCommon.calldatasizeGuard fn.params.length] ++ fn.body)
    (BridgedStmts_cons (calldatasizeGuard_bridged_local fn.params.length)
      (hFunctions fn hFn))

private theorem buildSwitch_bridged_local
    (funcs : List Compiler.IRFunction)
    (fallback receive : Option Compiler.IREntrypoint)
    (hFunctions : ∀ fn, fn ∈ funcs → BridgedStmts fn.body)
    (hFallback : ∀ fb, fallback = some fb → BridgedStmts fb.body)
    (hReceive : ∀ rc, receive = some rc → BridgedStmts rc.body) :
    BridgedStmt
      (Compiler.CodegenCommon.buildSwitch funcs fallback receive false) := by
  unfold Compiler.CodegenCommon.buildSwitch
  exact bridgedStmt_block_of_bridgedStmts
    (BridgedStmts_cons_let "__has_selector" _
      bridgedExpr_dispatch_has_selector
      (BridgedStmts_cons_if
        (bridgedExpr_dispatch_iszero_ident "__has_selector")
        (defaultDispatchCase_bridged_local fallback receive hFallback hReceive)
        (BridgedStmts_cons_if
          (BridgedExpr.ident "__has_selector")
          (BridgedStmts_singleton_switch
            bridgedExpr_dispatch_selector
            (switchCases_bridged_local funcs hFunctions)
            (by
              intro body hBody
              cases hBody
              exact defaultDispatchCase_bridged_local fallback receive
                hFallback hReceive))
          BridgedStmts_nil)))

private theorem mappingSlotFuncAt_bridged_local (scratchBase : Nat) :
    BridgedStmt (Compiler.CodegenCommon.mappingSlotFuncAt scratchBase) := by
  unfold Compiler.CodegenCommon.mappingSlotFuncAt
  exact bridgedStmt_funcDef "mappingSlot" ["baseSlot", "key"] ["slot"] _

private theorem initFreeMemoryPointer_bridged_local :
    BridgedStmt Compiler.CodegenCommon.initFreeMemoryPointer := by
  unfold Compiler.CodegenCommon.initFreeMemoryPointer
  exact bridgedStmt_mstore_of_bridged_args _ _
    (BridgedExpr.lit Compiler.Constants.freeMemoryPointer)
    (BridgedExpr.lit 128)

private theorem runtimeCode_bridged_local
    (contract : Compiler.IRContract)
    (hFunctions : ∀ fn, fn ∈ contract.functions → BridgedStmts fn.body)
    (hFallback :
      ∀ fb, contract.fallbackEntrypoint = some fb → BridgedStmts fb.body)
    (hReceive :
      ∀ rc, contract.receiveEntrypoint = some rc → BridgedStmts rc.body)
    (hInternals : BridgedStmts contract.internalFunctions) :
    BridgedStmts (Compiler.CodegenCommon.runtimeCode contract) := by
  unfold Compiler.CodegenCommon.runtimeCode
  cases contract.usesMapping
  · simpa [List.append_assoc] using
      BridgedStmts_snoc
        (BridgedStmts_snoc hInternals initFreeMemoryPointer_bridged_local)
        (buildSwitch_bridged_local contract.functions
          contract.fallbackEntrypoint contract.receiveEntrypoint hFunctions
          hFallback hReceive)
  · simp only [ite_true]
    exact BridgedStmts_cons (mappingSlotFuncAt_bridged_local 0)
      (by
        simpa [List.append_assoc] using
          BridgedStmts_snoc
            (BridgedStmts_snoc hInternals initFreeMemoryPointer_bridged_local)
            (buildSwitch_bridged_local contract.functions
              contract.fallbackEntrypoint contract.receiveEntrypoint hFunctions
              hFallback hReceive))

/-- The selected native-harness switch case for a compiled external function is
bridged whenever the compiled function body is bridged. This packages the
generated dispatch guards (`callvalue`/`calldatasize`) around the body in the
same shape consumed by selector-hit native dispatcher lemmas. -/
theorem switchCaseBody_bridged_of_body
    (fn : IRFunction)
    (hBody : Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body) :
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts
      (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) := by
  have hCase :=
    switchCases_bridged_local
      [fn]
      (by
        intro fn' hmem
        simp only [List.mem_singleton] at hmem
        subst fn'
        exact hBody)
      fn.selector fn.selector
      (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn)
      (by
        simp [Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody])
  simpa using hCase

/-- Supported compiler output gives a bridged selected switch-case body for
every emitted external function. -/
theorem generatedRuntimeSwitchCaseBodiesBridged_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) := by
  intro fn hmem
  exact switchCaseBody_bridged_of_body fn
    (generatedRuntimeExternalBodiesBridged_of_compile_ok_supported
      hCompile hSupported fn hmem)

/-- The weaker mapping-write-supported compiler output gives a bridged selected
switch-case body for every emitted external function once mapping-write
slot-safety is supplied. -/
theorem generatedRuntimeSwitchCaseBodiesBridged_of_compile_ok_supported_except_mapping_writes_stmt_safety
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (hSafety :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        ∀ stmt, stmt ∈ entry.1.body →
          StmtMappingWriteSlotSafe spec.fields stmt) :
    ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) := by
  intro fn hmem
  exact switchCaseBody_bridged_of_body fn
    (generatedRuntimeExternalBodiesBridged_of_compile_ok_supported_except_mapping_writes_stmt_safety
      hCompile hSupported hSafety fn hmem)

theorem generatedRuntimeSelectedSwitchCaseBodyBridged_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {tx : IRTransaction} {fn : IRFunction}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn) :
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts
      (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) :=
  generatedRuntimeSwitchCaseBodiesBridged_of_compile_ok_supported
    hCompile hSupported fn (List.mem_of_find?_eq_some hFind)

/-- Supported compiler output gives a bridged selected direct user function
body. This is the source-fragment witness paired with
`lowerStmtsNativeWithSwitchIds_selectedFunctionBody_exists_of_compile_ok_supported`
for the remaining native function-body semantics bridge. -/
theorem generatedRuntimeSelectedFunctionBodyBridged_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {tx : IRTransaction} {fn : IRFunction}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn) :
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body :=
  generatedRuntimeExternalBodiesBridged_of_compile_ok_supported
    hCompile hSupported fn (List.mem_of_find?_eq_some hFind)

theorem generatedRuntimeSelectedSwitchCaseBodyBridged_of_compile_ok_supported_except_mapping_writes_stmt_safety
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {tx : IRTransaction} {fn : IRFunction}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (hSafety :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        ∀ stmt, stmt ∈ entry.1.body →
          StmtMappingWriteSlotSafe spec.fields stmt)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn) :
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts
      (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) :=
  generatedRuntimeSwitchCaseBodiesBridged_of_compile_ok_supported_except_mapping_writes_stmt_safety
    hCompile hSupported hSafety fn (List.mem_of_find?_eq_some hFind)

/-- The selected native-harness switch case contains no nested function
definitions whenever the compiled function body contains none. -/
theorem switchCaseBody_noFuncDefs_of_body
    (fn : IRFunction)
    (hBody :
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
        fn.body = false) :
    Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
      (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
        false := by
  unfold Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody
  exact Compiler.Proofs.YulGeneration.Backends.Native.dispatchBody_noFuncDefs
    fn.payable s!"{fn.name}()"
    ([Compiler.CodegenCommon.calldatasizeGuard fn.params.length] ++ fn.body)
    (by
      simp [Compiler.CodegenCommon.calldatasizeGuard,
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtContainsFuncDef,
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef,
        hBody])

/-- Supported compiler output emits no internal helper bodies; this is the
bridgeable-body analogue of the generated-runtime internal no-func-def witness. -/
theorem generatedRuntimeInternalBodiesBridged_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    ∀ name params rets body,
      Yul.YulStmt.funcDef name params rets body ∈ irContract.internalFunctions →
        Compiler.Proofs.YulGeneration.Backends.BridgedStmts body := by
  intro name params rets body hmem
  have hInternalNil : irContract.internalFunctions = [] :=
    Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_internalFunctions_nil
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  rw [hInternalNil] at hmem
  simp at hmem

/-- The weaker mapping-write-supported fragment emits no internal helper bodies,
so internal body bridgeability is immediate. -/
theorem generatedRuntimeInternalBodiesBridged_of_compile_ok_supported_except_mapping_writes
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ name params rets body,
      Yul.YulStmt.funcDef name params rets body ∈ irContract.internalFunctions →
        Compiler.Proofs.YulGeneration.Backends.BridgedStmts body := by
  intro name params rets body hmem
  have hInternalNil : irContract.internalFunctions = [] :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_internalFunctions_nil_except_mapping_writes
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  rw [hInternalNil] at hmem
  simp at hmem

/-- `SupportedSpec` discharges all body witnesses required by the retargeting
bridge theorem for the `emitYul` runtime. -/
theorem emitYul_runtimeCode_bridged_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts
      (Compiler.emitYul irContract).runtimeCode := by
  simpa [Compiler.emitYul, Compiler.CodegenCommon.emitYul] using
    runtimeCode_bridged_local
    irContract
    (generatedRuntimeExternalBodiesBridged_of_compile_ok_supported
      hCompile hSupported)
    (generatedRuntimeFallbackBodyBridged_of_compile_ok_supported
      hCompile hSupported)
    (generatedRuntimeReceiveBodyBridged_of_compile_ok_supported
      hCompile hSupported)
    (by
      have hInternalNil : irContract.internalFunctions = [] :=
        Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_internalFunctions_nil
          (model := spec) (selectors := selectors) (hSupported := hSupported)
          (ir := irContract) (hcompile := hCompile)
      rw [hInternalNil]
      exact Compiler.Proofs.YulGeneration.Backends.BridgedStmts_nil)

/-- The weaker mapping-write-supported fragment discharges the retargeting
bridge theorem for the `emitYul` runtime when actual mapping writes are
slot-safe. -/
theorem emitYul_runtimeCode_bridged_of_compile_ok_supported_except_mapping_writes_stmt_safety
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (hSafety :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        ∀ stmt, stmt ∈ entry.1.body →
          StmtMappingWriteSlotSafe spec.fields stmt) :
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts
      (Compiler.emitYul irContract).runtimeCode := by
  simpa [Compiler.emitYul, Compiler.CodegenCommon.emitYul] using
    runtimeCode_bridged_local
    irContract
    (generatedRuntimeExternalBodiesBridged_of_compile_ok_supported_except_mapping_writes_stmt_safety
      hCompile hSupported hSafety)
    (generatedRuntimeFallbackBodyBridged_of_compile_ok_supported_except_mapping_writes
      hCompile hSupported)
    (generatedRuntimeReceiveBodyBridged_of_compile_ok_supported_except_mapping_writes
      hCompile hSupported)
    (by
      have hInternalNil : irContract.internalFunctions = [] :=
        Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_internalFunctions_nil_except_mapping_writes
          (model := spec) (selectors := selectors) (hSupported := hSupported)
          (ir := irContract) (hcompile := hCompile)
      rw [hInternalNil]
      exact Compiler.Proofs.YulGeneration.Backends.BridgedStmts_nil)

/-- Supported compiler output has no internal helper bodies that can contain
nested function definitions. -/
theorem generatedRuntimeInternalBodiesHaveNoFuncDefs_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    ∀ name params rets body,
      Yul.YulStmt.funcDef name params rets body ∈ irContract.internalFunctions →
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef body = false := by
  intro name params rets body hmem
  have hInternalNil : irContract.internalFunctions = [] :=
    Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_internalFunctions_nil
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  rw [hInternalNil] at hmem
  simp at hmem

/-- The weaker mapping-write-supported compiler output has no internal helper
bodies that can contain nested function definitions. -/
theorem generatedRuntimeInternalBodiesHaveNoFuncDefs_of_compile_ok_supported_except_mapping_writes
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ name params rets body,
      Yul.YulStmt.funcDef name params rets body ∈ irContract.internalFunctions →
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef body = false := by
  intro name params rets body hmem
  have hInternalNil : irContract.internalFunctions = [] :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_internalFunctions_nil_except_mapping_writes
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  rw [hInternalNil] at hmem
  simp at hmem

/-- Source-level body closure discharges the generated runtime fragment's
external-function-body shape witness for supported compiler output. -/
theorem generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hStaticParams : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams entry.1.params)
    (hBodyNoFuncDefs :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        ∀ bodyStmts,
          CompilationModel.compileStmtList spec.fields spec.events spec.errors
            .calldata [] false (entry.1.params.map (·.name)) [] entry.1.body =
              Except.ok bodyStmts →
          Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
            bodyStmts = false) :
    ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
        fn.body = false :=
  compiledExternalFunctions_noFuncDefs_of_static_params_and_body
    spec.fields spec.events spec.errors
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_compiled_functions
      spec selectors hSupported irContract hCompile)
    hStaticParams (by
      intro entry hentry bodyStmts hbody
      have hfn : entry.1 ∈ selectorDispatchedFunctions spec := by
        simpa [SourceSemantics.selectorFunctionPairs] using (List.of_mem_zip hentry).1
      have habi := (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi
      exact hBodyNoFuncDefs entry hentry bodyStmts (by
        simpa [CompilationModel.FunctionSpec.bindingParams, habi] using hbody))

theorem generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_safe
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hStaticParams : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams entry.1.params)
    (hSafeBodies : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false entry.1.body) :
    ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
        fn.body = false :=
  compiledExternalFunctions_noFuncDefs_of_safe_static
    spec.fields spec.events spec.errors
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_compiled_functions
      spec selectors hSupported irContract hCompile)
    hStaticParams hSafeBodies

/-- The weaker mapping-write-supported compiler output emits external bodies
without nested function definitions once body-local mapping-write slot-safety
evidence is supplied. -/
theorem generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_supported_except_mapping_writes_stmt_safety
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (hSafety :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        ∀ stmt, stmt ∈ entry.1.body →
          StmtMappingWriteSlotSafe spec.fields stmt) :
    ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
        fn.body = false :=
  compiledExternalFunctions_noFuncDefs_of_safe_static
    spec.fields spec.events spec.errors
    (Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions_except_mapping_writes
      spec selectors hSupported irContract hCompile)
    (generatedRuntimeStaticScalarParams_of_supported_except_mapping_writes
      hSupported)
    (generatedRuntimeSafeBodies_of_supported_except_mapping_writes_stmt_safety
      hSupported hSafety)

/-- Supported compiler output gives selected switch-case bodies without nested
function definitions for every emitted external function. -/
theorem generatedRuntimeSwitchCaseBodiesHaveNoFuncDefs_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hStaticParams : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams entry.1.params)
    (hSafeBodies : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false entry.1.body) :
    ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
          false := by
  intro fn hmem
  exact switchCaseBody_noFuncDefs_of_body fn
    (generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_safe
      hCompile hSupported hStaticParams hSafeBodies fn hmem)

/-- The weaker mapping-write-supported compiler output gives selected
switch-case bodies without nested function definitions once mapping-write
slot-safety is supplied. -/
theorem generatedRuntimeSwitchCaseBodiesHaveNoFuncDefs_of_compile_ok_supported_except_mapping_writes_stmt_safety
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (hSafety :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        ∀ stmt, stmt ∈ entry.1.body →
          StmtMappingWriteSlotSafe spec.fields stmt) :
    ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
          false := by
  intro fn hmem
  exact switchCaseBody_noFuncDefs_of_body fn
    (generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_supported_except_mapping_writes_stmt_safety
      hCompile hSupported hSafety fn hmem)

theorem generatedRuntimeSelectedSwitchCaseBodyHasNoFuncDefs_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {tx : IRTransaction} {fn : IRFunction}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hStaticParams : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams entry.1.params)
    (hSafeBodies : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false entry.1.body)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn) :
    Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
      (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
        false :=
  generatedRuntimeSwitchCaseBodiesHaveNoFuncDefs_of_compile_ok_supported
    hCompile hSupported hStaticParams hSafeBodies fn
    (List.mem_of_find?_eq_some hFind)

theorem generatedRuntimeSelectedSwitchCaseBodyHasNoFuncDefs_of_compile_ok_supported_safe
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {tx : IRTransaction} {fn : IRFunction}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn) :
    Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
      (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
        false :=
  generatedRuntimeSelectedSwitchCaseBodyHasNoFuncDefs_of_compile_ok_supported
    hCompile hSupported (generatedRuntimeStaticScalarParams_of_supported hSupported)
    (generatedRuntimeSafeBodies_of_supported hSupported) hFind

theorem generatedRuntimeSelectedSwitchCaseBodyHasNoFuncDefs_of_compile_ok_supported_except_mapping_writes_stmt_safety
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {tx : IRTransaction} {fn : IRFunction}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (hSafety :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        ∀ stmt, stmt ∈ entry.1.body →
          StmtMappingWriteSlotSafe spec.fields stmt)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn) :
    Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
      (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
        false :=
  generatedRuntimeSwitchCaseBodiesHaveNoFuncDefs_of_compile_ok_supported_except_mapping_writes_stmt_safety
    hCompile hSupported hSafety fn (List.mem_of_find?_eq_some hFind)

/-- Supported compiler output satisfies the native generated-runtime fragment
validator's executable predicate. -/
theorem generatedRuntimeNativeFragment_of_compile_ok_supported_safe
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hStaticParams : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors → Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams entry.1.params)
    (hSafeBodies : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false entry.1.body) :
    Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeNativeFragment
      (Compiler.emitYul irContract).runtimeCode = true :=
  Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeNativeFragment_emitYul_runtimeCode_noFallback_noReceive
    irContract
    (generatedRuntimePrefixFunctionNamesUnique_of_compile_ok_supported
      hCompile hSupported)
    (generatedRuntimeInternalsAreFuncDefs_of_compile_ok_supported
      hCompile hSupported)
    (generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_safe
      hCompile hSupported hStaticParams hSafeBodies)
    (generatedRuntimeInternalBodiesHaveNoFuncDefs_of_compile_ok_supported
      hCompile hSupported)
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noFallbackEntrypoint
      spec selectors hSupported irContract hCompile)
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noReceiveEntrypoint
      spec selectors hSupported irContract hCompile)

/-- The weaker mapping-write-supported compiler output satisfies the native
generated-runtime fragment validator once each actual mapping-write statement
has slot-safety evidence. -/
theorem generatedRuntimeNativeFragment_of_compile_ok_supported_except_mapping_writes_stmt_safety
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (hSafety :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        ∀ stmt, stmt ∈ entry.1.body →
          StmtMappingWriteSlotSafe spec.fields stmt) :
    Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeNativeFragment
      (Compiler.emitYul irContract).runtimeCode = true :=
  Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeNativeFragment_emitYul_runtimeCode_noFallback_noReceive
    irContract
    (generatedRuntimePrefixFunctionNamesUnique_of_compile_ok_supported_except_mapping_writes
      hCompile hSupported)
    (generatedRuntimeInternalsAreFuncDefs_of_compile_ok_supported_except_mapping_writes
      hCompile hSupported)
    (generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_supported_except_mapping_writes_stmt_safety
      hCompile hSupported hSafety)
    (generatedRuntimeInternalBodiesHaveNoFuncDefs_of_compile_ok_supported_except_mapping_writes
      hCompile hSupported)
    (Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_noFallbackEntrypoint_except_mapping_writes
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile))
    (Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_noReceiveEntrypoint_except_mapping_writes
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile))

/-- Supported compiler output satisfies the native generated-runtime fragment
validator once source body closure is supplied; static-scalar parameter closure
is derived directly from `SupportedSpec`. -/
theorem generatedRuntimeNativeFragment_of_compile_ok_supported_safeBodies
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hSafeBodies : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false entry.1.body) :
    Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeNativeFragment
      (Compiler.emitYul irContract).runtimeCode = true :=
  generatedRuntimeNativeFragment_of_compile_ok_supported_safe
    hCompile hSupported (generatedRuntimeStaticScalarParams_of_supported hSupported)
    hSafeBodies

/-- `SupportedSpec` is enough to validate the Yul runtime emitted by `emitYul`
as a generated native-runtime fragment. -/
theorem generatedRuntimeNativeFragment_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeNativeFragment
      (Compiler.emitYul irContract).runtimeCode = true :=
  generatedRuntimeNativeFragment_of_compile_ok_supported_except_mapping_writes_stmt_safety
    hCompile hSupported.exceptMappingWrites
    (stmtMappingWriteSlotSafe_of_supported_stateClosed hSupported)

/-- Supported compiler output passes the native generated-runtime fragment
validator. -/
theorem validateGeneratedRuntimeNativeFragment_of_compile_ok_supported_safe
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hStaticParams : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors → Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams entry.1.params)
    (hSafeBodies : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false entry.1.body) :
    Compiler.Proofs.YulGeneration.Backends.Native.validateGeneratedRuntimeNativeFragment
      (Compiler.emitYul irContract).runtimeCode = .ok () :=
  Compiler.Proofs.YulGeneration.Backends.Native.validateGeneratedRuntimeNativeFragment_ok
    (Compiler.emitYul irContract).runtimeCode
    (generatedRuntimeNativeFragment_of_compile_ok_supported_safe
      hCompile hSupported hStaticParams hSafeBodies)

theorem validateGeneratedRuntimeNativeFragment_of_compile_ok_supported_safeBodies
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hSafeBodies : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false entry.1.body) :
    Compiler.Proofs.YulGeneration.Backends.Native.validateGeneratedRuntimeNativeFragment
      (Compiler.emitYul irContract).runtimeCode = .ok () :=
  Compiler.Proofs.YulGeneration.Backends.Native.validateGeneratedRuntimeNativeFragment_ok
    (Compiler.emitYul irContract).runtimeCode
    (generatedRuntimeNativeFragment_of_compile_ok_supported_safeBodies
      hCompile hSupported hSafeBodies)

/-- Executable native-fragment validation succeeds for the `emitYul` runtime of
any supported compilation result. -/
theorem validateGeneratedRuntimeNativeFragment_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    Compiler.Proofs.YulGeneration.Backends.Native.validateGeneratedRuntimeNativeFragment
      (Compiler.emitYul irContract).runtimeCode = .ok () :=
  validateGeneratedRuntimeNativeFragment_of_compile_ok_supported_safeBodies
    hCompile hSupported (generatedRuntimeSafeBodies_of_supported hSupported)

theorem validateGeneratedRuntimeNativeFragment_of_compile_ok_supported_except_mapping_writes_stmt_safety
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (hSafety :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        ∀ stmt, stmt ∈ entry.1.body →
          StmtMappingWriteSlotSafe spec.fields stmt) :
    Compiler.Proofs.YulGeneration.Backends.Native.validateGeneratedRuntimeNativeFragment
      (Compiler.emitYul irContract).runtimeCode = .ok () :=
  Compiler.Proofs.YulGeneration.Backends.Native.validateGeneratedRuntimeNativeFragment_ok
    (Compiler.emitYul irContract).runtimeCode
    (generatedRuntimeNativeFragment_of_compile_ok_supported_except_mapping_writes_stmt_safety
      hCompile hSupported hSafety)

/-- The direct generated-runtime `callDispatcher` result is the executable
native harness result once the supported emitted runtime lowers successfully
and its native environment is valid. -/
private theorem callDispatcherResult_eq_nativeRuntime_supported_local
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul irContract).runtimeCode = .ok nativeContract)
    (hEnv : Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
      (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) =
        .ok ()) :
    nativeGeneratedCallDispatcherResultOf irContract tx state observableSlots
        nativeContract =
      Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        (Nat.succ (sizeOf (Compiler.emitYul irContract).runtimeCode))
        irContract tx state observableSlots := by
  have hInterp :=
    Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative
      (Nat.succ (sizeOf (Compiler.emitYul irContract).runtimeCode))
      irContract tx state observableSlots nativeContract
      (generatedRuntimeNativeFragment_of_compile_ok_supported hCompile hSupported)
      hLower hEnv
  simp [nativeGeneratedCallDispatcherResultOf, Compiler.emitYul,
    Compiler.runtimeCode, Compiler.CodegenCommon.emitYul]
  exact hInterp.symm

/-- Source-level compiler correctness over the direct projected
`EvmYul.Yul.callDispatcher` result.

This is the thinnest public native composition surface: callers prove the
actual projected native result matches `interpretIR`; this theorem composes
that result match with the supported source-to-IR compiler theorem. It exposes
no generated-dispatcher oracle predicate. -/
theorem compile_preserves_native_evmYulLean_of_nativeGeneratedCallDispatcherResult_match
    (model : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok irContract)
    (hNative :
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx
          (FunctionBody.initialIRStateForTx model tx initialWorld))
        (nativeGeneratedCallDispatcherResultOf irContract tx
          (FunctionBody.initialIRStateForTx model tx initialWorld)
          observableSlots nativeContract)) :
    sourceResultMatchesNativeOn observableSlots
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (nativeGeneratedCallDispatcherResultOf irContract tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)
        observableSlots nativeContract) := by
  exact
    sourceResultMatchesNativeOn_of_sourceResultMatchesIRResult_of_nativeResultsMatchOn
      (Compiler.Proofs.IRGeneration.Contract.compile_preserves_semantics
        model selectors hSupported irContract tx initialWorld
        htxNormalized hcalldataSizeFits hcompile)
      hNative

/-- Supported compiler output with no mapping helper reduces native runtime
lowering to the generated `initFreeMemoryPointer; buildSwitch` runtime shell. -/
theorem lowerRuntimeContractNative_of_compile_ok_supported_noMapping
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hNoMapping : irContract.usesMapping = false) :
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode =
      match Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
          [Compiler.CodegenCommon.initFreeMemoryPointer,
            Compiler.CodegenCommon.buildSwitch irContract.functions none none] with
      | .ok dispatcher =>
          .ok { dispatcher := .Block dispatcher
                functions :=
                  (∅ :
                    Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap) }
      | .error err => .error err :=
  Compiler.Proofs.YulGeneration.Backends.Native.lowerRuntimeContractNative_emitYul_noMapping_noInternals_noFallback_noReceive
    irContract hNoMapping
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_internalFunctions_nil
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile))
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noFallbackEntrypoint
      spec selectors hSupported irContract hCompile)
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noReceiveEntrypoint
      spec selectors hSupported irContract hCompile)

/-- Successful no-mapping native lowering for supported compiler output exposes
the concrete generated dispatcher lowering and produced native contract. -/
private theorem lowerRuntimeContractNative_of_compile_ok_supported_noMapping_ok_dispatcher
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hNoMapping : irContract.usesMapping = false)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract) :
    ∃ dispatcher : List EvmYul.Yul.Ast.Stmt,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
          [Compiler.CodegenCommon.initFreeMemoryPointer,
            Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok dispatcher ∧
      nativeContract = nativeContractOfDispatcher dispatcher :=
  Compiler.Proofs.YulGeneration.Backends.Native.lowerRuntimeContractNative_emitYul_noMapping_ok_dispatcher
    irContract nativeContract hNoMapping
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_internalFunctions_nil
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile))
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noFallbackEntrypoint
      spec selectors hSupported irContract hCompile)
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noReceiveEntrypoint
      spec selectors hSupported irContract hCompile)
    hLower

/-- Supported compiler output with the mapping helper reduces native runtime
lowering to the generated dispatcher shell plus the lowered native
`mappingSlot` helper. The dispatcher is lowered under the same reserved-name
context as the full emitted runtime, because native switch lowering allocates
fresh temporaries from that context. -/
theorem lowerRuntimeContractNative_of_compile_ok_supported_mapping_reserved
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hMapping : irContract.usesMapping = true) :
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode =
      match Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
            (Compiler.emitYul irContract).runtimeCode)
          0 [Compiler.CodegenCommon.initFreeMemoryPointer,
            Compiler.CodegenCommon.buildSwitch irContract.functions none none] with
      | .ok (dispatcher, _) =>
          .ok { dispatcher := .Block dispatcher
                functions := ((∅ :
                  Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap).insert
                  "mappingSlot"
                  Compiler.Proofs.YulGeneration.Backends.Native.nativeMappingSlotFunctionDefinition) }
      | .error err => .error err :=
  Compiler.Proofs.YulGeneration.Backends.Native.lowerRuntimeContractNative_emitYul_mapping_noInternals_noFallback_noReceive_reserved
    irContract hMapping
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_internalFunctions_nil
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile))
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noFallbackEntrypoint
      spec selectors hSupported irContract hCompile)
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noReceiveEntrypoint
      spec selectors hSupported irContract hCompile)

/-- Supported compiler output gives successful native lowering for the
generated helper-free dispatcher statement. -/
theorem lowerStmtsNative_buildSwitch_noFallback_noReceive_exists_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    ∃ dispatcher : List EvmYul.Yul.Ast.Stmt,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok dispatcher := by
  have hBodies :
      ∀ fn, fn ∈ irContract.functions →
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
          fn.body = false :=
    generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_safe
      hCompile hSupported (generatedRuntimeStaticScalarParams_of_supported hSupported)
      (generatedRuntimeSafeBodies_of_supported hSupported)
  have hSwitchNoFunc :
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtContainsFuncDef
        (Compiler.CodegenCommon.buildSwitch irContract.functions none none) =
          false :=
    Compiler.Proofs.YulGeneration.Backends.Native.buildSwitch_noFuncDefs_noFallback_noReceive
      irContract.functions hBodies
  have hDispatcherNoFunc :
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
        [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
          false := by
    simp [Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef,
      hSwitchNoFunc]
  exact
    Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNative_ok_of_yulStmtsContainFuncDef_false
      [Compiler.CodegenCommon.buildSwitch irContract.functions none none]
      hDispatcherNoFunc

/-- Supported compiler output gives successful native lowering for the
generated dispatcher statement in any switch-id context. This is the mapping
helper variant used by full runtime lowering. -/
theorem lowerStmtsNativeWithSwitchIds_buildSwitch_noFallback_noReceive_exists_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (reservedNames : List String) (nextSwitchId : Nat)
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    ∃ (dispatcher : List EvmYul.Yul.Ast.Stmt) (finalSwitchId : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames nextSwitchId
          [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok (dispatcher, finalSwitchId) := by
  have hBodies :
      ∀ fn, fn ∈ irContract.functions →
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
          fn.body = false :=
    generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_safe
      hCompile hSupported (generatedRuntimeStaticScalarParams_of_supported hSupported)
      (generatedRuntimeSafeBodies_of_supported hSupported)
  have hSwitchNoFunc :
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtContainsFuncDef
        (Compiler.CodegenCommon.buildSwitch irContract.functions none none) =
          false :=
    Compiler.Proofs.YulGeneration.Backends.Native.buildSwitch_noFuncDefs_noFallback_noReceive
      irContract.functions hBodies
  have hDispatcherNoFunc :
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
        [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
          false := by
    simp [Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef,
      hSwitchNoFunc]
  exact
    Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
      reservedNames nextSwitchId
      [Compiler.CodegenCommon.buildSwitch irContract.functions none none]
      hDispatcherNoFunc

/-- Supported compiler output gives successful native lowering for the selected
generated switch-case body. -/
theorem lowerStmtsNativeWithSwitchIds_selectedSwitchCaseBody_exists_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {tx : IRTransaction} {fn : IRFunction}
    (reservedNames : List String) (nextSwitchId : Nat)
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (finalSwitchId : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames nextSwitchId
          (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
        .ok (bodyNative, finalSwitchId) := by
  exact
    Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
      reservedNames nextSwitchId
      (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn)
      (generatedRuntimeSelectedSwitchCaseBodyHasNoFuncDefs_of_compile_ok_supported_safe
        hCompile hSupported hFind)

/-- Supported compiler output gives successful native lowering for the selected
generated user function body. This is the lowering half of the remaining
selector-hit body-semantics bridge; the dispatcher wrapper theorem above covers
`switchCaseBody fn`, while this theorem exposes the direct `fn.body` target. -/
theorem lowerStmtsNativeWithSwitchIds_selectedFunctionBody_exists_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {tx : IRTransaction} {fn : IRFunction}
    (reservedNames : List String) (nextSwitchId : Nat)
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (finalSwitchId : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames nextSwitchId fn.body =
        .ok (bodyNative, finalSwitchId) := by
  exact
    Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
      reservedNames nextSwitchId fn.body
      (generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_safe
        hCompile hSupported
        (generatedRuntimeStaticScalarParams_of_supported hSupported)
        (generatedRuntimeSafeBodies_of_supported hSupported)
        fn (List.mem_of_find?_eq_some hFind))

/-- Supported compiler output gives both the bridged-fragment witness and the
successful native lowering for the selected generated user function body. -/
theorem selectedFunctionBodyBridgedAndLowered_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {tx : IRTransaction} {fn : IRFunction}
    (reservedNames : List String) (nextSwitchId : Nat)
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn) :
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body ∧
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (finalSwitchId : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames nextSwitchId fn.body =
        .ok (bodyNative, finalSwitchId) := by
  exact ⟨
    generatedRuntimeSelectedFunctionBodyBridged_of_compile_ok_supported
      hCompile hSupported hFind,
    lowerStmtsNativeWithSwitchIds_selectedFunctionBody_exists_of_compile_ok_supported
      reservedNames nextSwitchId hCompile hSupported hFind⟩

/-- Supported compiler output discharges the selected generated user-body
closure facts that are independent of semantic execution: the selected body is
in the bridged fragment, the native body lowerer succeeds in the caller's
switch-id context, and the selected ABI calldata threshold fits in an EVM word.

This is the compile-derived half of the remaining selected-body result bridge;
the still-missing piece is the generic native simulation theorem that turns the
lowered body execution into the `NativeGeneratedSelectedUserBodyResultBridgeAtFuel`
result surface. -/
theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.selected_body_closure_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract) :
    ∀ (fn : IRFunction) (reservedNames : List String) (nextSwitchId : Nat),
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body ∧
      (∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (finalSwitchId : Nat),
        Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
            reservedNames nextSwitchId fn.body =
          .ok (bodyNative, finalSwitchId)) ∧
      4 + fn.params.length * 32 < EvmYul.UInt256.size := by
  intro fn reservedNames nextSwitchId hFind
  rcases selectedFunctionBodyBridgedAndLowered_of_compile_ok_supported
      reservedNames nextSwitchId hcompile hSupported hFind with
    ⟨hBridged, hLowered⟩
  exact ⟨hBridged, hLowered,
    generatedFunctionCalldataThreshold_of_compile_ok_supported
      spec selectors hSupported irContract tx hcompile fn hFind⟩

/-- Supported compiler output produces a generated runtime dispatcher list
without nested Yul function definitions. -/
private theorem generatedRuntimeDispatcherHasNoFuncDefs_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    Native.yulStmtsContainFuncDef
      [CodegenCommon.initFreeMemoryPointer,
        CodegenCommon.buildSwitch irContract.functions none none] = false := by
  have hBodies :=
    generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_safe
      hCompile hSupported (generatedRuntimeStaticScalarParams_of_supported hSupported)
      (generatedRuntimeSafeBodies_of_supported hSupported)
  have hSwitchNoFunc :=
    Native.buildSwitch_noFuncDefs_noFallback_noReceive irContract.functions hBodies
  simp [Native.yulStmtsContainFuncDef, Native.yulStmtContainsFuncDef,
    CodegenCommon.initFreeMemoryPointer, hSwitchNoFunc]

/-- Supported compiler output always lowers to a native generated-runtime
contract. This discharges the executable lowerer from `SupportedSpec +
compile`: supported external bodies contain no nested function definitions, and
the native lowerer is total for such generated dispatcher statements. -/
theorem lowerRuntimeContractNative_of_compile_ok_supported_exists
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract := by
  have hDispatcherNoFunc :=
    generatedRuntimeDispatcherHasNoFuncDefs_of_compile_ok_supported hCompile hSupported
  cases hMapping : irContract.usesMapping
  · rcases Native.lowerStmtsNative_ok_of_yulStmtsContainFuncDef_false
        [CodegenCommon.initFreeMemoryPointer,
          CodegenCommon.buildSwitch irContract.functions none none]
        hDispatcherNoFunc with ⟨dispatcher, hLowerDispatcher⟩
    refine ⟨nativeContractOfDispatcher dispatcher, ?_⟩
    rw [lowerRuntimeContractNative_of_compile_ok_supported_noMapping
      hCompile hSupported hMapping, hLowerDispatcher]
  · rcases Native.lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
        (yulStmtsIdentifierNames (emitYul irContract).runtimeCode) 0
        [CodegenCommon.initFreeMemoryPointer,
          CodegenCommon.buildSwitch irContract.functions none none]
        hDispatcherNoFunc with ⟨dispatcher, nextSwitchId, hLowerDispatcher⟩
    refine ⟨nativeContractOfDispatcherWithMapping dispatcher, ?_⟩
    rw [lowerRuntimeContractNative_of_compile_ok_supported_mapping_reserved
      hCompile hSupported hMapping, hLowerDispatcher]

/-- Successful mapping-helper native lowering for supported compiler output
exposes the concrete generated dispatcher lowering, threaded switch counter,
and produced native contract. -/
private theorem lowerRuntimeContractNative_of_compile_ok_supported_mapping_ok_dispatcher_reserved
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hMapping : irContract.usesMapping = true)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract) :
    ∃ (dispatcher : List EvmYul.Yul.Ast.Stmt) (nextSwitchId : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
            (Compiler.emitYul irContract).runtimeCode)
          0 [Compiler.CodegenCommon.initFreeMemoryPointer,
            Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok (dispatcher, nextSwitchId) ∧
      nativeContract = nativeContractOfDispatcherWithMapping dispatcher :=
  Compiler.Proofs.YulGeneration.Backends.Native.lowerRuntimeContractNative_emitYul_mapping_ok_dispatcher_reserved
    irContract nativeContract hMapping
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_internalFunctions_nil
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile))
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noFallbackEntrypoint
      spec selectors hSupported irContract hCompile)
    (Compiler.Proofs.IRGeneration.ContractShape.compile_ok_yields_noReceiveEntrypoint
      spec selectors hSupported irContract hCompile)
    hLower

/-- `CodegenCommon.buildSwitch funcs none none` is always a `YulStmt.block`. -/
private theorem buildSwitch_noFallback_noReceive_eq_block (funcs : List IRFunction) :
    ∃ stmts, CodegenCommon.buildSwitch funcs none none = Yul.YulStmt.block stmts := by
  unfold CodegenCommon.buildSwitch
  dsimp
  exact ⟨_, rfl⟩

private theorem lowerStmtsNativeWithSwitchIds_buildSwitch_noFallback_noReceive_ok_block
    (reservedNames : List String) (nextSwitchId : Nat)
    (funcs : List IRFunction) (dispatcher : List EvmYul.Yul.Ast.Stmt) (finalSwitchId : Nat)
    (h : lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId
      [CodegenCommon.buildSwitch funcs none none] = .ok (dispatcher, finalSwitchId)) :
    ∃ inner, dispatcher = [.Block inner] ∧
      lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId
        [CodegenCommon.buildSwitch funcs none none] = .ok ([.Block inner], finalSwitchId) := by
  rcases buildSwitch_noFallback_noReceive_eq_block funcs with ⟨stmts, hBuild⟩
  rw [hBuild] at h
  rw [lowerStmtsNativeWithSwitchIds_cons, lowerStmtGroupNativeWithSwitchIds_block] at h
  cases hInner : lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId stmts with
  | error err =>
      rw [hInner] at h
      simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok pair =>
      rcases pair with ⟨inner, midSwitchId⟩
      rw [hInner] at h
      simp only [lowerStmtsNativeWithSwitchIds_nil, Bind.bind, Except.bind, Pure.pure, Except.pure,
        List.append_nil, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨inner, rfl, ?_⟩
      rw [hBuild, lowerStmtsNativeWithSwitchIds_cons, lowerStmtGroupNativeWithSwitchIds_block, hInner]
      simp only [lowerStmtsNativeWithSwitchIds_nil, Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]

private theorem lowerStmtsNative_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
    (funcs : List IRFunction) (dispatcher : List EvmYul.Yul.Ast.Stmt)
    (h : lowerStmtsNative [CodegenCommon.initFreeMemoryPointer,
      CodegenCommon.buildSwitch funcs none none] = .ok dispatcher) :
    ∃ (inner : List EvmYul.Yul.Ast.Stmt) (nextSwitchId : Nat),
      dispatcher =
        [.ExprStmtCall (lowerExprNative (Yul.YulExpr.call "mstore"
          [Yul.YulExpr.lit Constants.freeMemoryPointer, Yul.YulExpr.lit 128])),
         .Block inner] ∧
      lowerStmtsNativeWithSwitchIds
          (yulStmtsIdentifierNames [CodegenCommon.initFreeMemoryPointer,
            CodegenCommon.buildSwitch funcs none none])
          0 [CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], nextSwitchId) := by
  unfold lowerStmtsNative at h
  dsimp at h
  rw [lowerStmtsNativeWithSwitchIds_cons] at h
  simp [CodegenCommon.initFreeMemoryPointer] at h
  simp only [Bind.bind, Except.bind] at h
  cases hTail : lowerStmtsNativeWithSwitchIds
      (yulStmtsIdentifierNames
        [Yul.YulStmt.exprStmt (Yul.YulExpr.call "mstore"
          [Yul.YulExpr.lit Constants.freeMemoryPointer, Yul.YulExpr.lit 128]),
         CodegenCommon.buildSwitch funcs none none])
      0 [CodegenCommon.buildSwitch funcs none none] with
  | error err =>
      rw [hTail] at h
      simp at h
  | ok pair =>
      rcases pair with ⟨tail, next⟩
      rw [hTail] at h
      simp at h
      subst h
      rcases lowerStmtsNativeWithSwitchIds_buildSwitch_noFallback_noReceive_ok_block
          _ 0 funcs tail next hTail with ⟨inner, rfl, hLowerBlock⟩
      exact ⟨inner, next, rfl, by simpa [CodegenCommon.initFreeMemoryPointer] using hLowerBlock⟩

private theorem lowerStmtsNativeWithSwitchIds_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
    (reservedNames : List String) (nextSwitchId : Nat)
    (funcs : List IRFunction) (dispatcher : List EvmYul.Yul.Ast.Stmt)
    (finalSwitchId : Nat)
    (h :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames nextSwitchId
          [Compiler.CodegenCommon.initFreeMemoryPointer,
            Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok (dispatcher, finalSwitchId)) :
    ∃ inner,
      dispatcher =
        [.ExprStmtCall
          (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
            (Yul.YulExpr.call "mstore"
              [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
                Yul.YulExpr.lit 128])),
         .Block inner] ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames nextSwitchId
          [Compiler.CodegenCommon.buildSwitch funcs none none] =
        .ok ([.Block inner], finalSwitchId) := by
  rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons]
    at h
  simp [Compiler.CodegenCommon.initFreeMemoryPointer] at h
  simp only [Bind.bind, Except.bind] at h
  cases hTail :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames nextSwitchId
        [Compiler.CodegenCommon.buildSwitch funcs none none] with
  | error err =>
      rw [hTail] at h
      simp at h
  | ok pair =>
      cases pair with
      | mk tail next =>
          rw [hTail] at h
          simp at h
          rcases h with ⟨hDispatcher, hFinal⟩
          subst hDispatcher
          subst hFinal
          rcases lowerStmtsNativeWithSwitchIds_buildSwitch_noFallback_noReceive_ok_block
              reservedNames nextSwitchId funcs tail next hTail with
            ⟨inner, hTailEq, hLowerBlock⟩
          subst hTailEq
          exact ⟨inner, rfl, rfl⟩

private theorem lowerSwitchCasesNativeWithSwitchIds_buildSwitch_tags_range_of_functionSelectorsRange
    (reservedNames : List String) (nextSwitchId finalSwitchId : Nat)
    (funcs : List IRFunction)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hLowerCases :
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
        reservedNames nextSwitchId
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          funcs) = .ok (cases', finalSwitchId))
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ funcs → fn.selector < EvmYul.UInt256.size) :
    ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size := by
  intro tag body hmem
  have hTagsEq :
      cases'.map (·.1) =
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          funcs).map (·.1) :=
    Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq
      reservedNames nextSwitchId finalSwitchId
      (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases funcs)
      cases' hLowerCases
  have hTagMem : tag ∈ cases'.map (·.1) :=
    List.mem_map_of_mem (f := Prod.fst) hmem
  rw [hTagsEq] at hTagMem
  simp [Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases]
    at hTagMem
  rcases hTagMem with ⟨fnTag, hFnTag, hTag⟩
  subst hTag
  exact hFunctionSelectorsRange fnTag hFnTag

/-- No-mapping selector-miss dispatcher match at canonical generated-runtime fuel. -/
private theorem nativeGeneratedCallDispatcherMatchesIROn_selector_miss_noMapping_canonical
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hNoMapping : irContract.usesMapping = false)
    (hLowerDispatcher : lowerStmtsNative
      [CodegenCommon.initFreeMemoryPointer, CodegenCommon.buildSwitch irContract.functions none none] =
        .ok [nativeInitFreeMemoryPointerStmt, .Block inner])
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = none)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    nativeGeneratedDispatcherExecMatchesIROn irContract tx state
      observableSlots (nativeContractOfInitPrefixedDispatcher [.Block inner]) := by
  rcases lowerStmtsNative_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
      irContract.functions [nativeInitFreeMemoryPointerStmt, .Block inner] hLowerDispatcher with
    ⟨inner', nextSwitchId, hDispatcherEq, hLowerBlock⟩
  simp [nativeInitFreeMemoryPointerStmt] at hDispatcherEq
  subst inner'
  rcases nativeDispatcherExecMatchesIRPositive_of_initFreeMemoryPointer_buildSwitch_selector_miss_noFallback_noReceive_withSwitchIds_atFuel
      (nativeRuntimeDispatcherFuel irContract)
      (yulStmtsIdentifierNames [CodegenCommon.initFreeMemoryPointer, CodegenCommon.buildSwitch irContract.functions none none])
      0 irContract tx state observableSlots inner nextSwitchId (∅ : NativeFunctionMap)
      hLowerBlock hFind hSelectorRange hNoWrap hFunctionSelectorsRange with
    ⟨n0, cases', midN, hLowerCases, hNativeDispatcherExec⟩
  have hFuel : cases'.length + 20 ≤ nativeRuntimeDispatcherFuel irContract := by
    dsimp [nativeRuntimeDispatcherFuel]
    have h := sizeOf_emitYul_runtimeCode_noMapping_ge_lowered_cases_length_plus24
      hcompile hSupported hNoMapping hLowerCases
    omega
  simpa [nativeGeneratedDispatcherExecMatchesIROn, nativeDispatcherExecMatchesIRPositive,
    nativeContractOfInitPrefixedDispatcher, nativeInitFreeMemoryPointerStmt] using
    hNativeDispatcherExec hFuel

/-- Mapping-helper selector-miss dispatcher match at canonical generated-runtime fuel. -/
private theorem nativeGeneratedCallDispatcherMatchesIROn_selector_miss_mapping_canonical
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (inner : List EvmYul.Yul.Ast.Stmt) (nextSwitchId : Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hMapping : irContract.usesMapping = true)
    (hLowerDispatcher : lowerStmtsNativeWithSwitchIds (yulStmtsIdentifierNames (emitYul irContract).runtimeCode) 0
      [CodegenCommon.initFreeMemoryPointer, CodegenCommon.buildSwitch irContract.functions none none] =
        .ok ([nativeInitFreeMemoryPointerStmt, .Block inner], nextSwitchId))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = none)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size) :
    nativeGeneratedDispatcherExecMatchesIROn irContract tx state
      observableSlots (nativeContractOfInitPrefixedDispatcherWithMapping [.Block inner]) := by
  let reservedNames := yulStmtsIdentifierNames (emitYul irContract).runtimeCode
  let functions := ((∅ : NativeFunctionMap).insert "mappingSlot" Native.nativeMappingSlotFunctionDefinition)
  rcases lowerStmtsNativeWithSwitchIds_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
      reservedNames 0 irContract.functions [nativeInitFreeMemoryPointerStmt, .Block inner] nextSwitchId hLowerDispatcher with
    ⟨inner', hDispatcherEq, hLowerBlock⟩
  simp [nativeInitFreeMemoryPointerStmt] at hDispatcherEq
  subst inner'
  rcases nativeDispatcherExecMatchesIRPositive_of_initFreeMemoryPointer_buildSwitch_selector_miss_noFallback_noReceive_withSwitchIds_atFuel
      (nativeRuntimeDispatcherFuel irContract) reservedNames 0 irContract tx state observableSlots inner nextSwitchId functions
      hLowerBlock hFind hSelectorRange hNoWrap hFunctionSelectorsRange with
    ⟨switchStart, cases', midN, hLowerCases, hNativeDispatcherExec⟩
  have hFuel : cases'.length + 20 ≤ nativeRuntimeDispatcherFuel irContract := by
    dsimp [nativeRuntimeDispatcherFuel]
    have h := sizeOf_emitYul_runtimeCode_mapping_ge_lowered_cases_length_plus24
      hcompile hSupported hMapping hLowerCases
    omega
  simpa [nativeGeneratedDispatcherExecMatchesIROn, nativeDispatcherExecMatchesIRPositive,
    nativeContractOfInitPrefixedDispatcherWithMapping, nativeInitFreeMemoryPointerStmt, functions]
    using hNativeDispatcherExec hFuel

/-- Native-vs-IR selector-miss theorem for a supported generated runtime.

This is the direct `nativeGeneratedCallDispatcherResultOf` selector-miss case:
successful whole-runtime lowering is decomposed into the generated dispatcher
shape, and the generic native selector-miss execution lemma supplies the
projected native result match. -/
private theorem nativeGeneratedCallDispatcherResult_selector_miss_matchesIR_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hLowerRuntime : lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = none)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    nativeResultsMatchOn observableSlots (interpretIR irContract tx state)
      (nativeGeneratedCallDispatcherResultOf irContract tx state observableSlots nativeContract) := by
  have hFunctionSelectorsRange :=
    generatedRuntimeFunctionSelectorsRange_of_compile_ok_supported hcompile hSupported hSelectorsRange
  by_cases hUsesMapping : irContract.usesMapping
  · have hMapping : irContract.usesMapping = true := by simpa using hUsesMapping
    rcases lowerRuntimeContractNative_of_compile_ok_supported_mapping_ok_dispatcher_reserved
        hcompile hSupported hMapping hLowerRuntime with ⟨dispatcher, nextSwitchId, hLowerDispatcher, hNativeContract⟩
    rcases lowerStmtsNativeWithSwitchIds_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
        (yulStmtsIdentifierNames (emitYul irContract).runtimeCode) 0 irContract.functions dispatcher nextSwitchId
        hLowerDispatcher with ⟨inner, hDispatcher, _⟩
    subst nativeContract
    subst dispatcher
    exact nativeGeneratedCallDispatcherMatchesIROn_of_dispatcherExec
      (nativeGeneratedCallDispatcherMatchesIROn_selector_miss_mapping_canonical
        spec selectors hSupported irContract tx state observableSlots inner nextSwitchId
        hcompile hMapping hLowerDispatcher hFind hSelectorRange hNoWrap hFunctionSelectorsRange)
  · have hNoMapping : irContract.usesMapping = false := Bool.eq_false_iff.2 hUsesMapping
    rcases lowerRuntimeContractNative_of_compile_ok_supported_noMapping_ok_dispatcher
        hcompile hSupported hNoMapping hLowerRuntime with ⟨dispatcher, hLowerDispatcher, hNativeContract⟩
    rcases lowerStmtsNative_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
        irContract.functions dispatcher hLowerDispatcher with ⟨inner, _, hDispatcher, _⟩
    subst nativeContract
    subst dispatcher
    exact nativeGeneratedCallDispatcherMatchesIROn_of_dispatcherExec
      (nativeGeneratedCallDispatcherMatchesIROn_selector_miss_noMapping_canonical
        spec selectors hSupported irContract tx state observableSlots inner
        hcompile hNoMapping hLowerDispatcher hFind hSelectorRange hNoWrap hFunctionSelectorsRange)

/-- Selector-miss native-vs-IR theorem with native lowering produced from
`SupportedSpec + compile`. -/
theorem nativeGeneratedCallDispatcherResult_selector_miss_matchesIR_exists_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        none)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (_hEnv : Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
      (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) =
        .ok ()) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  rcases lowerRuntimeContractNative_of_compile_ok_supported_exists
      hcompile hSupported with
    ⟨nativeContract, hLowerRuntime⟩
  exact ⟨nativeContract, hLowerRuntime,
    nativeGeneratedCallDispatcherResult_selector_miss_matchesIR_of_compile_ok_supported
      spec selectors hSupported irContract tx state observableSlots nativeContract
      hcompile hLowerRuntime hFind hSelectorRange hSelectorsRange hNoWrap⟩

/-- Init-prefixed native contract shell parameterized by the native function table. -/
private abbrev nativeInitPrefixedContract
    (inner : List EvmYul.Yul.Ast.Stmt) (functions : NativeFunctionMap) :
    EvmYul.Yul.Ast.YulContract :=
  { dispatcher := .Block [nativeInitFreeMemoryPointerStmt, .Block inner]
    functions := functions }

/-- Post-selector-match native Yul state at the start of a hit switch-case body. -/
private abbrev nativeSwitchHitMatchedState
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (contract : EvmYul.Yul.Ast.YulContract)
    (switchId : Nat) : EvmYul.Yul.State :=
  ((((Native.nativeSwitchPostInitFreeMemoryState contract (YulTransaction.ofIR tx)
        state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
        Native.nativeSwitchHasSelectorStore).insert
      (nativeSwitchDiscrTempName switchId)
      (EvmYul.UInt256.ofNat ((YulTransaction.ofIR tx).functionSelector % Constants.selectorModulus))).insert
    (nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 0)).insert
    (nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 1))

/-- Canonical lowered statement list inside the generated outer switch block. -/
private abbrev nativeSwitchInnerShape
    (reservedNames : List String) (switchStart : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (body1 : List EvmYul.Yul.Ast.Stmt) : List EvmYul.Yul.Ast.Stmt :=
  [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
      (some (lowerExprNative (Yul.YulExpr.call "iszero"
        [Yul.YulExpr.call "lt" [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))),
   EvmYul.Yul.Ast.Stmt.If
      (lowerExprNative (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident "__has_selector"])) body1,
   EvmYul.Yul.Ast.Stmt.If
      (lowerExprNative (Yul.YulExpr.ident "__has_selector"))
      [lowerNativeSwitchBlock
        (Yul.YulExpr.call "shr"
          [Yul.YulExpr.lit Constants.selectorShift, Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
        (freshNativeSwitchId reservedNames switchStart) cases' [Native.nativeRevertZeroZeroStmt]]]

/-- Unpacks a lowered supported generated runtime contract into its switch
block, reserved-name context, function table, and switch-case fuel bound,
uniformly across mapping-helper and helper-free contracts. -/
private theorem lowerRuntimeContractNative_of_compile_ok_supported_switch_block_and_fuel
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {nativeContract : EvmYul.Yul.Ast.YulContract}
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hLowerRuntime : lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract) :
    ∃ (reservedNames : List String) (functions : NativeFunctionMap)
      (inner : List EvmYul.Yul.Ast.Stmt) (nextSwitchId : Nat),
      nativeContract = nativeInitPrefixedContract inner functions ∧
      lowerStmtsNativeWithSwitchIds reservedNames 0
        [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], nextSwitchId) ∧
      (∀ switchStart cases' midN,
        lowerSwitchCasesNativeWithSwitchIds reservedNames
          (freshNativeSwitchId reservedNames switchStart + 1)
          (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) →
        cases'.length + 24 ≤ nativeRuntimeDispatcherFuel irContract) := by
  by_cases hUsesMapping : irContract.usesMapping
  · have hMapping : irContract.usesMapping = true := by simpa using hUsesMapping
    rcases lowerRuntimeContractNative_of_compile_ok_supported_mapping_ok_dispatcher_reserved
        hcompile hSupported hMapping hLowerRuntime with ⟨dispatcher, nextSwitchId, hLowerDispatcher, hNativeContract⟩
    rcases lowerStmtsNativeWithSwitchIds_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
        (yulStmtsIdentifierNames (emitYul irContract).runtimeCode) 0 irContract.functions dispatcher nextSwitchId
        hLowerDispatcher with ⟨inner, hDispatcher, hLowerBlock⟩
    subst nativeContract; subst dispatcher
    refine ⟨_, _, inner, nextSwitchId, rfl, hLowerBlock, fun _ _ _ hLC => ?_⟩
    exact sizeOf_emitYul_runtimeCode_mapping_ge_lowered_cases_length_plus24 hcompile hSupported hMapping hLC
  · have hNoMapping : irContract.usesMapping = false := Bool.eq_false_iff.2 hUsesMapping
    rcases lowerRuntimeContractNative_of_compile_ok_supported_noMapping_ok_dispatcher
        hcompile hSupported hNoMapping hLowerRuntime with ⟨dispatcher, hLowerDispatcher, hNativeContract⟩
    rcases lowerStmtsNative_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
        irContract.functions dispatcher hLowerDispatcher with ⟨inner, nextSwitchId, hDispatcher, hLowerBlock⟩
    subst nativeContract; subst dispatcher
    refine ⟨_, ∅, inner, nextSwitchId, rfl, hLowerBlock, fun _ _ _ hLC => ?_⟩
    exact sizeOf_emitYul_runtimeCode_noMapping_ge_lowered_cases_length_plus24 hcompile hSupported hNoMapping hLC

/-- Generic selector-hit revert execution lemma for a lowered init-prefixed
switch dispatcher once the selected lowered case body is known to revert. -/
private theorem contractDispatcherExecResult_selector_hit_revert_of_case_revert
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (reservedNames : List String)
    (functions : NativeFunctionMap) (inner body1 body' : List EvmYul.Yul.Ast.Stmt)
    (switchStart fuel k : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hInner : inner = nativeSwitchInnerShape reservedNames switchStart cases' body1)
    (hCase : cases'.find? (fun (tag, _) => tag == tx.functionSelector) = some (tx.functionSelector, body'))
    (hTagsRange : ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size)
    (hFuelShape : nativeRuntimeDispatcherFuel irContract = fuel + cases'.length + (k + 20))
    (hBody : ∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
      EvmYul.Yul.exec (((fuel + k) + 1) + suffix.length + 7) (.Block body')
        (some (nativeInitPrefixedContract inner functions))
        (nativeSwitchHitMatchedState irContract tx state observableSlots
          (nativeInitPrefixedContract inner functions)
          (freshNativeSwitchId reservedNames switchStart)) =
      .error EvmYul.Yul.Exception.Revert) :
    Native.contractDispatcherExecResult (nativeRuntimeDispatcherFuel irContract)
      (nativeInitPrefixedContract inner functions)
      (Native.initialState (nativeInitPrefixedContract inner functions)
        (YulTransaction.ofIR tx) state.storage
        (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)) =
      .error EvmYul.Yul.Exception.Revert := by
  have hSelector : tx.functionSelector =
      (YulTransaction.ofIR tx).functionSelector % Constants.selectorModulus := by
    simpa [YulTransaction.ofIR] using (Nat.mod_eq_of_lt hSelectorRange).symm
  have hPeel :=
    Native.contractDispatcherExecResult_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_peel
      (fuel + k) reservedNames switchStart cases' body1 inner functions (YulTransaction.ofIR tx)
      state.storage (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      hInner (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hSwitch :=
    Native.exec_block_lowerNativeSwitchBlock_selector_find_hit_postInitFreeMemory_hasSelectorState_error_projectResult_eq
      (fuel + k) tx.functionSelector (freshNativeSwitchId reservedNames switchStart)
      tx.functionSelector cases' [Native.nativeRevertZeroZeroStmt] body'
      (nativeInitPrefixedContract inner functions) (YulTransaction.ofIR tx) state.storage state.events
      (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
      EvmYul.Yul.Exception.Revert
      (Native.projectResult (YulTransaction.ofIR tx) state.storage state.events (.error EvmYul.Yul.Exception.Revert))
      hSelector hCase (Nat.lt_trans hSelectorRange (by decide)) hTagsRange hBody rfl
  rw [hFuelShape, show fuel + cases'.length + (k + 20) = (fuel + k) + cases'.length + 20 by omega]
  simpa [nativeInitPrefixedContract, nativeInitFreeMemoryPointerStmt, YulGeneration.selectorExpr] using
    hPeel.trans hSwitch.1

/-- Non-payable nonzero-value selector-hit revert execution from a lowered
generated switch block. -/
private theorem contractDispatcherExecResult_selector_hit_nonpayable_nonzero_revert_of_lowerBlock
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (reservedNames : List String)
    (functions : NativeFunctionMap) (inner : List EvmYul.Yul.Ast.Stmt)
    (nextSwitchId : Nat) (fn : IRFunction)
    (hLowerBlock : lowerStmtsNativeWithSwitchIds reservedNames 0
      [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], nextSwitchId))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false) (hNonzero : tx.msgValue % Constants.evmModulus ≠ 0)
    (hFuelBound : ∀ switchStart cases' midN,
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames switchStart + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) →
      cases'.length + 24 ≤ nativeRuntimeDispatcherFuel irContract) :
    Native.contractDispatcherExecResult (nativeRuntimeDispatcherFuel irContract)
      (nativeInitPrefixedContract inner functions)
      (Native.initialState (nativeInitPrefixedContract inner functions)
        (YulTransaction.ofIR tx) state.storage
        (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)) =
      .error EvmYul.Yul.Exception.Revert := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd, hInner, hLowerCases, hCase, hBodyLower⟩ :=
    Native.buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames 0 irContract.functions inner nextSwitchId tx.functionSelector fn hLowerBlock hFind
  rcases Native.lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hNonPayable hBodyLower with ⟨bodyNative, _, hBodyShape, _⟩
  have hTagsRange := lowerSwitchCasesNativeWithSwitchIds_buildSwitch_tags_range_of_functionSelectorsRange
    reservedNames (freshNativeSwitchId reservedNames switchStart + 1) midN
    irContract.functions cases' hLowerCases hFunctionSelectorsRange
  have hFuel := hFuelBound switchStart cases' midN hLowerCases
  let fuel := nativeRuntimeDispatcherFuel irContract - (cases'.length + 24)
  apply contractDispatcherExecResult_selector_hit_revert_of_case_revert
    irContract tx state observableSlots reservedNames functions inner body1 body'
    switchStart fuel 4 cases' hSelectorRange hNoWrap hInner hCase hTagsRange (by dsimp [fuel]; omega)
  intro _ suffix _
  rw [hBodyShape, show (((fuel + 4) + 1) + suffix.length + 7) = (fuel + suffix.length) + 12 by omega]
  exact Native.exec_switchCaseBody_nonpayable_callvalue_revert_postInitFreeMemory_fuel
    (fuel + suffix.length) [Native.nativeRevertZeroZeroStmt] bodyNative
    (nativeInitPrefixedContract inner functions) (YulTransaction.ofIR tx) state.storage
    (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)
    (freshNativeSwitchId reservedNames switchStart) Native.nativeSwitchHasSelectorStore
    (4 + fn.params.length * 32) (by simpa [YulTransaction.ofIR] using hNonzero)

/-- Native-vs-IR selector-hit theorem for the generated non-payable value guard.

When the selected generated function is non-payable and the transaction value is
nonzero modulo the EVM word modulus, both the generated native dispatcher and
the IR interpreter revert before entering the user body. -/
private theorem nativeGeneratedCallDispatcherResult_selector_hit_nonpayable_nonzero_revert_matchesIR_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction) (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hLowerRuntime : lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false) (hNonzero : tx.msgValue % Constants.evmModulus ≠ 0) :
    nativeResultsMatchOn observableSlots (interpretIR irContract tx state)
      (nativeGeneratedCallDispatcherResultOf irContract tx state observableSlots nativeContract) := by
  have hFunctionSelectorsRange :=
    generatedRuntimeFunctionSelectorsRange_of_compile_ok_supported hcompile hSupported hSelectorsRange
  have hIRRevert :=
    nativeResultsMatchOn_projectResult_revert_of_nonpayable_nonzero
      irContract tx state observableSlots fn hFind hNonPayable hNonzero
  rcases lowerRuntimeContractNative_of_compile_ok_supported_switch_block_and_fuel
      hcompile hSupported hLowerRuntime with
    ⟨reservedNames, functions, inner, nextSwitchId, hNativeContract, hLowerBlock, hFuelBound⟩
  subst nativeContract
  have hExec := contractDispatcherExecResult_selector_hit_nonpayable_nonzero_revert_of_lowerBlock
    irContract tx state observableSlots reservedNames functions inner nextSwitchId fn
    hLowerBlock hFind hSelectorRange hNoWrap hFunctionSelectorsRange hNonPayable hNonzero hFuelBound
  apply nativeGeneratedCallDispatcherMatchesIROn_of_dispatcherExec
  simpa [nativeGeneratedDispatcherExecMatchesIROn, hExec] using hIRRevert

/-- Payable args-short selector-hit revert execution from a lowered generated
switch block. -/
private theorem contractDispatcherExecResult_selector_hit_payable_args_short_revert_of_lowerBlock
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (reservedNames : List String)
    (functions : NativeFunctionMap) (inner : List EvmYul.Yul.Ast.Stmt) (nextSwitchId : Nat) (fn : IRFunction)
    (hLowerBlock : lowerStmtsNativeWithSwitchIds reservedNames 0
      [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], nextSwitchId))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus) (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hguards : DispatchGuardsSafe fn tx) (hPayable : fn.payable = true) (hArgsShort : ¬ fn.params.length ≤ tx.args.length)
    (hFuelBound : ∀ switchStart cases' midN,
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames switchStart + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) →
      cases'.length + 24 ≤ nativeRuntimeDispatcherFuel irContract) :
    Native.contractDispatcherExecResult (nativeRuntimeDispatcherFuel irContract) (nativeInitPrefixedContract inner functions)
      (Native.initialState (nativeInitPrefixedContract inner functions) (YulTransaction.ofIR tx) state.storage
        (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)) = .error EvmYul.Yul.Exception.Revert := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd, hInner, hLowerCases, hCase, hBodyLower⟩ :=
    Native.buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames 0 irContract.functions inner nextSwitchId tx.functionSelector fn hLowerBlock hFind
  rcases Native.lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hPayable hBodyLower with ⟨bodyNative, _, hBodyShape, _⟩
  have hTagsRange := lowerSwitchCasesNativeWithSwitchIds_buildSwitch_tags_range_of_functionSelectorsRange
    reservedNames (freshNativeSwitchId reservedNames switchStart + 1) midN irContract.functions cases' hLowerCases hFunctionSelectorsRange
  have hFuel24 := hFuelBound switchStart cases' midN hLowerCases
  let fuel := nativeRuntimeDispatcherFuel irContract - (cases'.length + 23)
  have hCalldataLt : 4 + (YulTransaction.ofIR tx).args.length * 32 < 4 + fn.params.length * 32 := by
    simpa [YulTransaction.ofIR_args] using (by omega : 4 + tx.args.length * 32 < 4 + fn.params.length * 32)
  apply contractDispatcherExecResult_selector_hit_revert_of_case_revert
    irContract tx state observableSlots reservedNames functions inner body1 body'
    switchStart fuel 3 cases' hSelectorRange hNoWrap hInner hCase hTagsRange (by dsimp [fuel]; omega)
  intro _ suffix _
  rw [hBodyShape, show (((fuel + 3) + 1) + suffix.length + 7) = (fuel + suffix.length) + 11 by omega]
  exact Native.exec_switchCaseBody_payable_calldata_revert_postInitFreeMemory_fuel
    (fuel + suffix.length) bodyNative (nativeInitPrefixedContract inner functions) (YulTransaction.ofIR tx) state.storage
    (Native.materializedStorageSlots (runtimeCode irContract) observableSlots) (freshNativeSwitchId reservedNames switchStart)
    Native.nativeSwitchHasSelectorStore (4 + fn.params.length * 32) (by simpa [YulTransaction.ofIR_args] using hNoWrap)
    (Native.DispatchGuardsSafe_calldata_threshold_lt fn tx hguards) hCalldataLt

/-- Non-payable zero-value args-short selector-hit revert execution from a
lowered generated switch block. -/
private theorem contractDispatcherExecResult_selector_hit_nonpayable_args_short_revert_of_lowerBlock
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (reservedNames : List String)
    (functions : NativeFunctionMap) (inner : List EvmYul.Yul.Ast.Stmt) (nextSwitchId : Nat) (fn : IRFunction)
    (hLowerBlock : lowerStmtsNativeWithSwitchIds reservedNames 0
      [CodegenCommon.buildSwitch irContract.functions none none] = .ok ([.Block inner], nextSwitchId))
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus) (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hguards : DispatchGuardsSafe fn tx) (hNonPayable : fn.payable = false)
    (hZero : tx.msgValue % Constants.evmModulus = 0) (hArgsShort : ¬ fn.params.length ≤ tx.args.length)
    (hFuelBound : ∀ switchStart cases' midN,
      lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames switchStart + 1)
        (Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) →
      cases'.length + 24 ≤ nativeRuntimeDispatcherFuel irContract) :
    Native.contractDispatcherExecResult (nativeRuntimeDispatcherFuel irContract) (nativeInitPrefixedContract inner functions)
      (Native.initialState (nativeInitPrefixedContract inner functions) (YulTransaction.ofIR tx) state.storage
        (Native.materializedStorageSlots (runtimeCode irContract) observableSlots)) = .error EvmYul.Yul.Exception.Revert := by
  obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd, hInner, hLowerCases, hCase, hBodyLower⟩ :=
    Native.buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
      reservedNames 0 irContract.functions inner nextSwitchId tx.functionSelector fn hLowerBlock hFind
  rcases Native.lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hNonPayable hBodyLower with ⟨bodyNative, _, hBodyShape, _⟩
  have hTagsRange := lowerSwitchCasesNativeWithSwitchIds_buildSwitch_tags_range_of_functionSelectorsRange
    reservedNames (freshNativeSwitchId reservedNames switchStart + 1) midN irContract.functions cases' hLowerCases hFunctionSelectorsRange
  have hFuel24 := hFuelBound switchStart cases' midN hLowerCases
  let fuel := nativeRuntimeDispatcherFuel irContract - (cases'.length + 24)
  have hCalldataLt : 4 + (YulTransaction.ofIR tx).args.length * 32 < 4 + fn.params.length * 32 := by
    simpa [YulTransaction.ofIR_args] using (by omega : 4 + tx.args.length * 32 < 4 + fn.params.length * 32)
  apply contractDispatcherExecResult_selector_hit_revert_of_case_revert
    irContract tx state observableSlots reservedNames functions inner body1 body'
    switchStart fuel 4 cases' hSelectorRange hNoWrap hInner hCase hTagsRange (by dsimp [fuel]; omega)
  intro _ suffix _
  rw [hBodyShape, show (((fuel + 4) + 1) + suffix.length + 7) = (fuel + suffix.length) + 12 by omega]
  exact Native.exec_switchCaseBody_nonpayable_calldata_revert_postInitFreeMemory_fuel
    (fuel + suffix.length) bodyNative (nativeInitPrefixedContract inner functions) (YulTransaction.ofIR tx) state.storage
    (Native.materializedStorageSlots (runtimeCode irContract) observableSlots) (freshNativeSwitchId reservedNames switchStart)
    Native.nativeSwitchHasSelectorStore (4 + fn.params.length * 32) (by simpa [YulTransaction.ofIR] using hZero)
    (by simpa [YulTransaction.ofIR_args] using hNoWrap) (Native.DispatchGuardsSafe_calldata_threshold_lt fn tx hguards) hCalldataLt

/-- Native-vs-IR selector-hit theorem for the generated calldata-size guard.

When the selected generated function is value-safe but the transaction calldata
does not contain all selected ABI arguments, both the generated native
dispatcher and the IR interpreter revert before entering the user body. -/
private theorem nativeGeneratedCallDispatcherResult_selector_hit_args_short_revert_matchesIR_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction) (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hLowerRuntime : lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Constants.selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hguards : DispatchGuardsSafe fn tx)
    (hValue : fn.payable = true ∨ tx.msgValue % Constants.evmModulus = 0)
    (hArgsShort : ¬ fn.params.length ≤ tx.args.length) :
    nativeResultsMatchOn observableSlots (interpretIR irContract tx state)
      (nativeGeneratedCallDispatcherResultOf irContract tx state observableSlots nativeContract) := by
  have hFunctionSelectorsRange :=
    generatedRuntimeFunctionSelectorsRange_of_compile_ok_supported hcompile hSupported hSelectorsRange
  have hIRRevert :=
    nativeResultsMatchOn_projectResult_revert_of_args_short
      irContract tx state observableSlots fn hFind hValue hArgsShort
  rcases lowerRuntimeContractNative_of_compile_ok_supported_switch_block_and_fuel
      hcompile hSupported hLowerRuntime with
    ⟨reservedNames, functions, inner, nextSwitchId, hNativeContract, hLowerBlock, hFuelBound⟩
  subst nativeContract
  by_cases hPayable : fn.payable = true
  · have hExec := contractDispatcherExecResult_selector_hit_payable_args_short_revert_of_lowerBlock
      irContract tx state observableSlots reservedNames functions inner nextSwitchId fn
      hLowerBlock hFind hSelectorRange hNoWrap hFunctionSelectorsRange hguards hPayable hArgsShort hFuelBound
    apply nativeGeneratedCallDispatcherMatchesIROn_of_dispatcherExec
    simpa [nativeGeneratedDispatcherExecMatchesIROn, hExec] using hIRRevert
  · have hNonPayable : fn.payable = false := Bool.eq_false_iff.2 hPayable
    have hZero : tx.msgValue % Constants.evmModulus = 0 := by
      rcases hValue with hPayable' | hZero
      · exact False.elim (hPayable hPayable')
      · exact hZero
    have hExec := contractDispatcherExecResult_selector_hit_nonpayable_args_short_revert_of_lowerBlock
      irContract tx state observableSlots reservedNames functions inner nextSwitchId fn
      hLowerBlock hFind hSelectorRange hNoWrap hFunctionSelectorsRange hguards hNonPayable hZero hArgsShort hFuelBound
    apply nativeGeneratedCallDispatcherMatchesIROn_of_dispatcherExec
    simpa [nativeGeneratedDispatcherExecMatchesIROn, hExec] using hIRRevert

/-- Selector-hit non-payable value-guard revert theorem with native lowering
produced from `SupportedSpec + compile`. -/
theorem nativeGeneratedCallDispatcherResult_selector_hit_nonpayable_nonzero_revert_matchesIR_exists_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (fn : IRFunction)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false)
    (hNonzero : tx.msgValue % Compiler.Constants.evmModulus ≠ 0) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  rcases lowerRuntimeContractNative_of_compile_ok_supported_exists
      hcompile hSupported with
    ⟨nativeContract, hLowerRuntime⟩
  exact ⟨nativeContract, hLowerRuntime,
    nativeGeneratedCallDispatcherResult_selector_hit_nonpayable_nonzero_revert_matchesIR_of_compile_ok_supported
      spec selectors hSupported irContract tx state observableSlots nativeContract
      fn hcompile hLowerRuntime hFind hSelectorRange hSelectorsRange hNoWrap
      hNonPayable hNonzero⟩

/-- Selector-hit calldata-size guard revert theorem with native lowering
produced from `SupportedSpec + compile`. -/
theorem nativeGeneratedCallDispatcherResult_selector_hit_args_short_revert_matchesIR_exists_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (fn : IRFunction)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hguards : DispatchGuardsSafe fn tx)
    (hValue :
      fn.payable = true ∨
        tx.msgValue % Compiler.Constants.evmModulus = 0)
    (hArgsShort : ¬ fn.params.length ≤ tx.args.length) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  rcases lowerRuntimeContractNative_of_compile_ok_supported_exists
      hcompile hSupported with
    ⟨nativeContract, hLowerRuntime⟩
  exact ⟨nativeContract, hLowerRuntime,
    nativeGeneratedCallDispatcherResult_selector_hit_args_short_revert_matchesIR_of_compile_ok_supported
      spec selectors hSupported irContract tx state observableSlots nativeContract
      fn hcompile hLowerRuntime hFind hSelectorRange hSelectorsRange hNoWrap
      hguards hValue hArgsShort⟩

-- Lean 4.31 no longer unfolds these thin state constructors in the selector
-- bridge `simpa` calls below.
section

open Compiler.Constants
open Compiler.Proofs.IRGeneration.Function
open Compiler.Proofs.IRGeneration.FunctionBody
open Compiler.Proofs.YulGeneration.Backends.Native
open EvmYul
open EvmYul.Yul
open EvmYul.Yul.Ast
open Verity
open YulTransaction

attribute [local simp]
  Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
  Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStorePrefixStateForId

/-- Extract the reserved-context `buildSwitch` block lowering from a no-mapping
dispatcher lowering. -/
private theorem lowerStmtsNative_noMapping_dispatcher_to_buildSwitch_block
    {fns : List IRFunction} {inner : List Stmt}
    (hLowerDispatcher : lowerStmtsNative
      [CodegenCommon.initFreeMemoryPointer, CodegenCommon.buildSwitch fns none none] =
      .ok [nativeInitFreeMemoryPointerStmt, .Block inner]) :
    ∃ nextSwitchId,
      lowerStmtsNativeWithSwitchIds
        (yulStmtsIdentifierNames
          [CodegenCommon.initFreeMemoryPointer, CodegenCommon.buildSwitch fns none none]) 0
        [CodegenCommon.buildSwitch fns none none] = .ok ([.Block inner], nextSwitchId) := by
  rcases
    lowerStmtsNative_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
      fns [nativeInitFreeMemoryPointerStmt, .Block inner] hLowerDispatcher with
    ⟨inner', nextSwitchId, hDispatcher, hLowerBlock⟩
  have hInnerEq : inner = inner' := by
    simpa [nativeInitFreeMemoryPointerStmt] using hDispatcher
  subst inner'
  exact ⟨nextSwitchId, hLowerBlock⟩

/-- Derive the final matched-flag lookup on `final` from a selector-hit case
split and block-level word preservation on the executed body. -/
private theorem finalMatched_of_case_preserves
    {fuelOf : List (Nat × List Stmt) → Nat} {selector switchId : Nat}
    {cases' : List (Nat × List Stmt)} {body' execBody : List Stmt}
    {contract : YulContract} {tx : IRTransaction}
    {storage : IRStorageSlot → IRStorageWord} {materializedSlots : List Nat}
    {final : State}
    (hCase : cases'.find? (fun entry => entry.1 == selector) = some (selector, body'))
    (hBody : ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
      exec (fuelOf suffix) (.Block execBody) (some contract)
        (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract
          (ofIR tx) storage materializedSlots switchId
          nativeSwitchHasSelectorStore) = .ok final)
    (hPreserves : ∀ pre suffix, cases' = pre ++ (selector, body') :: suffix →
      NativeBlockPreservesWord (nativeSwitchMatchedTempName switchId)
        (UInt256.ofNat 1) execBody (some contract)) :
    ∀ matchedName : Identifier,
      matchedName = nativeSwitchMatchedTempName switchId →
        final[matchedName]! = UInt256.ofNat 1 := by
  intro matchedName hMatchedName
  subst matchedName
  rcases nativeSwitch_find_hit_split selector cases' selector body' hCase with
    ⟨pre, suffix, hCases, _hTag, _hPrefix⟩
  exact hPreserves pre suffix hCases (fuelOf suffix)
    (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId contract
      (ofIR tx) storage materializedSlots switchId
      nativeSwitchHasSelectorStore)
    final
    (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId_matched contract
      (ofIR tx) storage materializedSlots switchId
      nativeSwitchHasSelectorStore (nativeSwitchMatchedTempName switchId) rfl)
    (hBody pre suffix hCases)

private abbrev LoweredSwitchInnerShape
    (reservedNames : List String) (switchStart : Nat) (body1 : List Stmt)
    (cases' : List (Nat × List Stmt)) : List Stmt :=
  [Stmt.Let ["__has_selector"]
      (some (lowerExprNative (Yul.YulExpr.call "iszero"
        [Yul.YulExpr.call "lt" [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))),
    Stmt.If (lowerExprNative (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident "__has_selector"])) body1,
    Stmt.If (lowerExprNative (Yul.YulExpr.ident "__has_selector"))
      [lowerNativeSwitchBlock
        (Yul.YulExpr.call "shr"
          [Yul.YulExpr.lit selectorShift, Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
        (freshNativeSwitchId reservedNames switchStart) cases' [nativeRevertZeroZeroStmt]]]

private abbrev nativeContractOfInitPrefixedFunctions
    (functions : NativeFunctionMap) (dispatcher : List Stmt) : YulContract :=
  { dispatcher := .Block (nativeInitFreeMemoryPointerStmt :: dispatcher)
    functions := functions }

/-- Execute the generated dispatcher to `.ok final` on a selector hit
given whole-case body execution and final matched-flag preservation. -/
private theorem selector_hit_exec_ok_of_finalMatched
    {fuel0 targetFuel switchStart midN : Nat} {reservedNames : List String}
    {functions : NativeFunctionMap} {irContract : IRContract} {tx : IRTransaction}
    {storage : IRStorageSlot → IRStorageWord} {events : List (List Nat)}
    {materializedSlots : List Nat} {body1 inner : List Stmt}
    {cases' : List (Nat × List Stmt)} {body' : List Stmt} {final : State}
    (hFuel : targetFuel = fuel0 + cases'.length + 20)
    (hInner : inner = LoweredSwitchInnerShape reservedNames switchStart body1 cases')
    (hLowerCases : lowerSwitchCasesNativeWithSwitchIds reservedNames
      (freshNativeSwitchId reservedNames switchStart + 1)
      (buildSwitchSourceCases irContract.functions) = .ok (cases', midN))
    (hCase : cases'.find? (fun entry => entry.1 == tx.functionSelector) =
      some (tx.functionSelector, body'))
    (hSelectorRange : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < UInt256.size)
    (hBodyWhole : ∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
      exec (((fuel0 + 1) + suffix.length + 7)) (.Block body')
        (some (nativeContractOfInitPrefixedFunctions functions [.Block inner]))
        (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
          (nativeContractOfInitPrefixedFunctions functions [.Block inner]) (ofIR tx)
          storage materializedSlots (freshNativeSwitchId reservedNames switchStart)
          nativeSwitchHasSelectorStore) = .ok final)
    (hFinalMatched : ∀ matchedName : Identifier,
      matchedName = nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames switchStart) →
        final[matchedName]! = UInt256.ofNat 1) :
    contractDispatcherExecResult targetFuel
      (nativeContractOfInitPrefixedFunctions functions [.Block inner])
      (initialState (nativeContractOfInitPrefixedFunctions functions [.Block inner])
        (ofIR tx) storage materializedSlots) = .ok final := by
  subst hFuel
  have hPeel := contractDispatcherExecResult_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_peel
    fuel0 reservedNames switchStart cases' body1 inner functions (ofIR tx) storage
    materializedSlots hInner (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hSwitch :=
    exec_block_lowerNativeSwitchBlock_selector_find_hit_postInitFreeMemory_hasSelectorState_ok_projectResult_eq_finalMatched
      fuel0 tx.functionSelector (freshNativeSwitchId reservedNames switchStart) tx.functionSelector
      cases' [nativeRevertZeroZeroStmt] body'
      (nativeContractOfInitPrefixedFunctions functions [.Block inner]) (ofIR tx) storage events
      materializedSlots final (projectResult (ofIR tx) storage events (.ok (final, [])))
      (by simpa [ofIR] using (Nat.mod_eq_of_lt hSelectorRange).symm) hCase
      (Nat.lt_trans hSelectorRange (by decide))
      (lowerSwitchCasesNativeWithSwitchIds_buildSwitch_tags_range_of_functionSelectorsRange
        reservedNames (freshNativeSwitchId reservedNames switchStart + 1) midN
        irContract.functions cases' hLowerCases hFunctionSelectorsRange) hBodyWhole hFinalMatched rfl
  simpa [nativeContractOfInitPrefixedFunctions, nativeInitFreeMemoryPointerStmt, selectorExpr] using
    hPeel.trans hSwitch.1

/-- Split canonical `nativeRuntimeDispatcherFuel` into `fuel0 + cases'.length + 20`
for a supported no-mapping contract. -/
private theorem nativeRuntimeDispatcherFuel_split_noMapping
    {model : CompilationModel.CompilationModel} {selectors : List Nat}
    {hSupported : SupportedSpec model selectors} {irContract : IRContract}
    {switchStart midN : Nat} {cases' : List (Nat × List Stmt)}
    (hcompile : CompilationModel.compile model selectors = .ok irContract)
    (hNoMapping : irContract.usesMapping = false)
    (hLowerCases : lowerSwitchCasesNativeWithSwitchIds
      (yulStmtsIdentifierNames
        [CodegenCommon.initFreeMemoryPointer, CodegenCommon.buildSwitch irContract.functions none none])
      (freshNativeSwitchId
        (yulStmtsIdentifierNames
          [CodegenCommon.initFreeMemoryPointer, CodegenCommon.buildSwitch irContract.functions none none])
        switchStart + 1)
      (buildSwitchSourceCases irContract.functions) = .ok (cases', midN)) :
    nativeRuntimeDispatcherFuel irContract =
      (nativeRuntimeDispatcherFuel irContract - (cases'.length + 20)) + cases'.length + 20 := by
  have hBig :=
    sizeOf_emitYul_runtimeCode_noMapping_ge_lowered_cases_length_plus24
      hcompile hSupported hNoMapping hLowerCases
  dsimp [nativeRuntimeDispatcherFuel] at *
  omega

/-- Extract the reserved-context `buildSwitch` block lowering from a mapping
dispatcher lowering. -/
private theorem lowerStmtsNative_mapping_dispatcher_to_buildSwitch_block
    {reservedNames : List String} {fns : List IRFunction} {inner : List Stmt} {nextSwitchId : Nat}
    (hLowerDispatcher : lowerStmtsNativeWithSwitchIds reservedNames 0
      [CodegenCommon.initFreeMemoryPointer, CodegenCommon.buildSwitch fns none none] =
      .ok ([nativeInitFreeMemoryPointerStmt, .Block inner], nextSwitchId)) :
    lowerStmtsNativeWithSwitchIds reservedNames 0
      [CodegenCommon.buildSwitch fns none none] = .ok ([.Block inner], nextSwitchId) := by
  rcases
    lowerStmtsNativeWithSwitchIds_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
      reservedNames 0 fns [nativeInitFreeMemoryPointerStmt, .Block inner] nextSwitchId
      hLowerDispatcher with
    ⟨inner', hDispatcher, hLowerBlock⟩
  have hInnerEq : inner = inner' := by
    simpa [nativeInitFreeMemoryPointerStmt] using hDispatcher
  subst inner'
  exact hLowerBlock

/-- Extract the init-prefixed `buildSwitch` block lowering and concrete native
contract from a supported mapping runtime lowering. -/
private theorem lowerRuntimeContractNative_mapping_to_prefixed_block
    {model : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {nativeContract : YulContract}
    (hcompile : CompilationModel.compile model selectors = .ok irContract)
    (hSupported : SupportedSpec model selectors)
    (hMapping : irContract.usesMapping = true)
    (hLowerRuntime : lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract) :
    ∃ inner nextSwitchId,
      lowerStmtsNativeWithSwitchIds (yulStmtsIdentifierNames (emitYul irContract).runtimeCode) 0
        [CodegenCommon.initFreeMemoryPointer, CodegenCommon.buildSwitch irContract.functions none none] =
        .ok ([nativeInitFreeMemoryPointerStmt, .Block inner], nextSwitchId) ∧
      nativeContract = nativeContractOfInitPrefixedDispatcherWithMapping [.Block inner] := by
  rcases lowerRuntimeContractNative_of_compile_ok_supported_mapping_ok_dispatcher_reserved
      hcompile hSupported hMapping hLowerRuntime with
    ⟨dispatcher, nextSwitchId, hLowerDispatcher, rfl⟩
  rcases
    lowerStmtsNativeWithSwitchIds_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
      (yulStmtsIdentifierNames (emitYul irContract).runtimeCode)
      0 irContract.functions dispatcher nextSwitchId hLowerDispatcher with
    ⟨inner, rfl, _hLowerBlock⟩
  exact ⟨inner, nextSwitchId, hLowerDispatcher, rfl⟩

/-- Extract the init-prefixed `buildSwitch` block lowering and concrete native
contract from a supported no-mapping runtime lowering. -/
private theorem lowerRuntimeContractNative_noMapping_to_prefixed_block
    {model : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {nativeContract : YulContract}
    (hcompile : CompilationModel.compile model selectors = .ok irContract)
    (hSupported : SupportedSpec model selectors)
    (hNoMapping : irContract.usesMapping = false)
    (hLowerRuntime : lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract) :
    ∃ inner,
      lowerStmtsNative
        [CodegenCommon.initFreeMemoryPointer, CodegenCommon.buildSwitch irContract.functions none none] =
        .ok [nativeInitFreeMemoryPointerStmt, .Block inner] ∧
      nativeContract = nativeContractOfInitPrefixedDispatcher [.Block inner] := by
  rcases lowerRuntimeContractNative_of_compile_ok_supported_noMapping_ok_dispatcher
      hcompile hSupported hNoMapping hLowerRuntime with
    ⟨dispatcher, hLowerDispatcher, rfl⟩
  rcases
    lowerStmtsNative_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
      irContract.functions dispatcher hLowerDispatcher with
    ⟨inner, _nextSwitchId, rfl, _hLowerBlock⟩
  exact ⟨inner, hLowerDispatcher, rfl⟩

/-- Canonical dispatcher fuel decomposes into `(fuel - (cases'.length + 20)) + cases'.length + 20`
for a supported mapping contract. -/
private theorem nativeRuntimeDispatcherFuel_split_mapping
    {model : CompilationModel.CompilationModel} {selectors : List Nat}
    {hSupported : SupportedSpec model selectors} {irContract : IRContract}
    {switchStart midN : Nat} {cases' : List (Nat × List Stmt)}
    (hcompile : CompilationModel.compile model selectors = .ok irContract)
    (hMapping : irContract.usesMapping = true)
    (hLowerCases : lowerSwitchCasesNativeWithSwitchIds
      (yulStmtsIdentifierNames (emitYul irContract).runtimeCode)
      (freshNativeSwitchId (yulStmtsIdentifierNames (emitYul irContract).runtimeCode) switchStart + 1)
      (buildSwitchSourceCases irContract.functions) = .ok (cases', midN)) :
    nativeRuntimeDispatcherFuel irContract =
      (nativeRuntimeDispatcherFuel irContract - (cases'.length + 20)) + cases'.length + 20 := by
  have hBig :=
    sizeOf_emitYul_runtimeCode_mapping_ge_lowered_cases_length_plus24
      hcompile hSupported hMapping hLowerCases
  dsimp [nativeRuntimeDispatcherFuel] at *
  omega

/-- Execute the lowered init-prefixed dispatcher through the selector-hit switch
to `err` when the selected case body faults/halts. -/
private theorem selector_hit_exec_error
    {targetFuel fuel0 switchStart midN : Nat} {irContract : IRContract} {tx : IRTransaction}
    {reservedNames : List String} {body1 inner body' : List Stmt}
    {cases' : List (Nat × List Stmt)} {functions : NativeFunctionMap}
    {storage : IRStorageSlot → IRStorageWord} {events : List (List Nat)} {materializedSlots : List Nat}
    {err : Exception} {nativeYul : YulResult}
    (hFuel : targetFuel = fuel0 + cases'.length + 20)
    (hInner : inner = LoweredSwitchInnerShape reservedNames switchStart body1 cases')
    (hLowerCases : lowerSwitchCasesNativeWithSwitchIds reservedNames
      (freshNativeSwitchId reservedNames switchStart + 1)
      (buildSwitchSourceCases irContract.functions) = .ok (cases', midN))
    (hCase : cases'.find? (fun entry => entry.1 == tx.functionSelector) =
      some (tx.functionSelector, body'))
    (hSelectorRange : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < UInt256.size)
    (hFunctionSelectorsRange : ∀ fn, fn ∈ irContract.functions → fn.selector < UInt256.size)
    (hBody : ∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
      exec (((fuel0 + 1) + suffix.length + 7)) (.Block body')
        (some (nativeContractOfInitPrefixedFunctions functions [.Block inner]))
        (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
          (nativeContractOfInitPrefixedFunctions functions [.Block inner]) (ofIR tx)
          storage materializedSlots (freshNativeSwitchId reservedNames switchStart)
          nativeSwitchHasSelectorStore) = .error err)
    (hProject : projectResult (ofIR tx) storage events (.error err) = nativeYul) :
    contractDispatcherExecResult targetFuel
      (nativeContractOfInitPrefixedFunctions functions [.Block inner])
      (initialState (nativeContractOfInitPrefixedFunctions functions [.Block inner])
        (ofIR tx) storage materializedSlots) = .error err := by
  subst hFuel
  have hPeel := contractDispatcherExecResult_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_peel
    fuel0 reservedNames switchStart cases' body1 inner functions (ofIR tx) storage
    materializedSlots hInner (by simpa [YulTransaction.ofIR_args] using hNoWrap)
  have hSwitch :=
    exec_block_lowerNativeSwitchBlock_selector_find_hit_postInitFreeMemory_hasSelectorState_error_projectResult_eq
      fuel0 tx.functionSelector (freshNativeSwitchId reservedNames switchStart) tx.functionSelector
      cases' [nativeRevertZeroZeroStmt] body'
      (nativeContractOfInitPrefixedFunctions functions [.Block inner]) (ofIR tx) storage events
      materializedSlots err nativeYul
      (by simpa [ofIR] using (Nat.mod_eq_of_lt hSelectorRange).symm) hCase
      (Nat.lt_trans hSelectorRange (by decide))
      (lowerSwitchCasesNativeWithSwitchIds_buildSwitch_tags_range_of_functionSelectorsRange
        reservedNames (freshNativeSwitchId reservedNames switchStart + 1) midN
        irContract.functions cases' hLowerCases hFunctionSelectorsRange) hBody hProject
  simpa [nativeContractOfInitPrefixedFunctions, nativeInitFreeMemoryPointerStmt, selectorExpr] using
    hPeel.trans hSwitch.1

/-- Extract the unified `nativeContractOfInitPrefixedFunctions` shape, lowered
switch cases, selected case body, and canonical fuel split from a supported
generated runtime lowering on a selector hit. -/
private theorem lowerRuntimeContractNative_selector_hit_inner
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {tx : IRTransaction} {nativeContract : YulContract}
    {fn : IRFunction}
    (hcompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hLowerRuntime : lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn) :
    ∃ (reservedNames : List String) (functions : NativeFunctionMap)
      (body1 inner : List Stmt) (switchStart : Nat)
      (cases' : List (Nat × List Stmt)) (midN : Nat)
      (body' : List Stmt) (bodyStart bodyEnd : Nat),
      nativeContract = nativeContractOfInitPrefixedFunctions functions [.Block inner] ∧
      inner = LoweredSwitchInnerShape reservedNames switchStart body1 cases' ∧
      lowerSwitchCasesNativeWithSwitchIds reservedNames
        (freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) =
        some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (switchCaseBody fn) =
        .ok (body', bodyEnd) ∧
      nativeRuntimeDispatcherFuel irContract =
        (nativeRuntimeDispatcherFuel irContract - (cases'.length + 20)) + cases'.length + 20 := by
  by_cases hUsesMapping : irContract.usesMapping
  · have hMapping : irContract.usesMapping = true := by simpa using hUsesMapping
    rcases lowerRuntimeContractNative_mapping_to_prefixed_block hcompile hSupported
        hMapping hLowerRuntime with ⟨inner, nextSwitchId, hLowerDispatcher, rfl⟩
    have hLowerBlock := lowerStmtsNative_mapping_dispatcher_to_buildSwitch_block hLowerDispatcher
    obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
        hInner, hLowerCases, hCase, hBodyLower⟩ :=
      buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
        _ 0 irContract.functions inner nextSwitchId tx.functionSelector fn hLowerBlock hFind
    exact ⟨_, _, body1, inner, switchStart, cases', midN, body', bodyStart, bodyEnd,
      rfl, hInner, hLowerCases, hCase, hBodyLower,
      nativeRuntimeDispatcherFuel_split_mapping (hSupported := hSupported) hcompile hMapping hLowerCases⟩
  · have hNoMapping : irContract.usesMapping = false := Bool.eq_false_iff.2 hUsesMapping
    rcases lowerRuntimeContractNative_noMapping_to_prefixed_block hcompile hSupported
        hNoMapping hLowerRuntime with ⟨inner, hLowerDispatcher, rfl⟩
    rcases lowerStmtsNative_noMapping_dispatcher_to_buildSwitch_block hLowerDispatcher with
      ⟨nextSwitchId, hLowerBlock⟩
    obtain ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
        hInner, hLowerCases, hCase, hBodyLower⟩ :=
      buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
        _ 0 irContract.functions inner nextSwitchId tx.functionSelector fn hLowerBlock hFind
    exact ⟨_, _, body1, inner, switchStart, cases', midN, body', bodyStart, bodyEnd,
      rfl, hInner, hLowerCases, hCase, hBodyLower,
      nativeRuntimeDispatcherFuel_split_noMapping (hSupported := hSupported) hcompile hNoMapping hLowerCases⟩

/-- Compose a faulting/halting native dispatcher execution at canonical fuel
with `nativeGeneratedCallDispatcherResultOf` matching `interpretIR`. -/
private theorem callDispatcher_matchesIR_of_exec_error
    {irContract : IRContract} {tx : IRTransaction} {state : IRState}
    {observableSlots : List Nat} {contract : YulContract}
    {err : Exception} {nativeYul : YulResult}
    (hExec : contractDispatcherExecResult (nativeRuntimeDispatcherFuel irContract) contract
      (initialState contract (ofIR tx) state.storage
        (materializedStorageSlots (runtimeCode irContract) observableSlots)) = .error err)
    (hProject : projectResult (ofIR tx) state.storage state.events (.error err) = nativeYul)
    (hMatch : nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul)) :
    nativeResultsMatchOn observableSlots (interpretIR irContract tx state)
      (nativeGeneratedCallDispatcherResultOf irContract tx state observableSlots contract) := by
  apply nativeGeneratedCallDispatcherMatchesIROn_of_dispatcherExec
  refine nativeDispatcherExecMatchesIRPositive_of_project_eq_match
    (contract := irContract) (tx := tx) (state := state)
    (observableSlots := observableSlots) (nativeContract := contract) ?_ hMatch
  simpa [nativeProjectedDispatcherResultEq, hExec] using hProject

/-- Compose a successful native dispatcher execution at canonical fuel
with `nativeGeneratedCallDispatcherResultOf` matching `interpretIR`. -/
private theorem callDispatcher_matchesIR_of_exec_ok
    {irContract : IRContract} {tx : IRTransaction} {state : IRState}
    {observableSlots : List Nat} {contract : YulContract}
    {final : State} {nativeYul : YulResult}
    (hExec : contractDispatcherExecResult (nativeRuntimeDispatcherFuel irContract) contract
      (initialState contract (ofIR tx) state.storage
        (materializedStorageSlots (runtimeCode irContract) observableSlots)) = .ok final)
    (hProject : projectResult (ofIR tx) state.storage state.events
      (.ok (((final.reviveJump.overwrite? (initialState contract (ofIR tx) state.storage
        (materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
        (initialState contract (ofIR tx) state.storage
          (materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul)
    (hMatch : nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul)) :
    nativeResultsMatchOn observableSlots (interpretIR irContract tx state)
      (nativeGeneratedCallDispatcherResultOf irContract tx state observableSlots contract) := by
  apply nativeGeneratedCallDispatcherMatchesIROn_of_dispatcherExec
  refine nativeDispatcherExecMatchesIRPositive_of_project_eq_match
    (contract := irContract) (tx := tx) (state := state)
    (observableSlots := observableSlots) (nativeContract := contract) ?_ hMatch
  simpa [nativeProjectedDispatcherResultEq, hExec] using hProject

private abbrev CallDispatcherErrorMatchesIRGoal
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (nativeContract : YulContract)
    (fn : IRFunction) (err : Exception) (nativeYul : YulResult) : Prop :=
  ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List Stmt))
    (body' : List Stmt) (bodyStart bodyEnd : Nat),
    cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
    lowerStmtsNativeWithSwitchIds reservedNames bodyStart (switchCaseBody fn) = .ok (body', bodyEnd) ∧
    ((∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
        exec (((nativeRuntimeDispatcherFuel irContract - (cases'.length + 20)) + 1) + suffix.length + 7)
          (.Block body') (some nativeContract)
          (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId nativeContract (ofIR tx)
            state.storage (materializedStorageSlots (runtimeCode irContract) observableSlots)
            (freshNativeSwitchId reservedNames n0) nativeSwitchHasSelectorStore) = .error err) →
      projectResult (ofIR tx) state.storage state.events (.error err) = nativeYul →
      nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
      nativeResultsMatchOn observableSlots (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state observableSlots nativeContract))

/-- Native-vs-IR selector-hit error theorem for a supported generated runtime. -/
private theorem nativeGeneratedCallDispatcherResult_selector_hit_error_matchesIR_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (nativeContract : YulContract)
    (fn : IRFunction) (err : Exception) (nativeYul : YulResult)
    (hcompile : CompilationModel.compile spec selectors = .ok irContract)
    (hLowerRuntime : lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < UInt256.size) :
    CallDispatcherErrorMatchesIRGoal irContract tx state observableSlots nativeContract fn err nativeYul := by
  rcases lowerRuntimeContractNative_selector_hit_inner hcompile hSupported hLowerRuntime hFind with
    ⟨reservedNames, functions, body1, inner, switchStart, cases', midN, body',
      bodyStart, bodyEnd, rfl, hInner, hLowerCases, hCase, hBodyLower, hFuel⟩
  refine ⟨reservedNames, switchStart, cases', body', bodyStart, bodyEnd, hCase, hBodyLower, ?_⟩
  intro hBody hProject hMatch
  exact callDispatcher_matchesIR_of_exec_error
    (selector_hit_exec_error hFuel hInner hLowerCases hCase hSelectorRange hNoWrap
      (generatedRuntimeFunctionSelectorsRange_of_compile_ok_supported hcompile hSupported hSelectorsRange)
      hBody hProject)
    hProject hMatch

private abbrev CallDispatcherErrorArtifactMatchesIRGoal
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (nativeContract : YulContract) (fn : IRFunction) : Prop :=
  ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List Stmt)) (midN : Nat)
    (body' : List Stmt) (bodyStart bodyEnd : Nat),
    lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames n0 + 1)
      (buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
    cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
    lowerStmtsNativeWithSwitchIds reservedNames bodyStart (switchCaseBody fn) = .ok (body', bodyEnd) ∧
    (∀ (err : Exception) (nativeYul : YulResult),
      (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
        exec (((nativeRuntimeDispatcherFuel irContract - (cases'.length + 20)) + 1) + suffix.length + 7)
          (.Block body') (some nativeContract)
          (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId nativeContract (ofIR tx)
            state.storage (materializedStorageSlots (runtimeCode irContract) observableSlots)
            (freshNativeSwitchId reservedNames n0) nativeSwitchHasSelectorStore) = .error err) →
      projectResult (ofIR tx) state.storage state.events (.error err) = nativeYul →
      nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
      nativeResultsMatchOn observableSlots (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state observableSlots nativeContract))

/-- Artifact-fixed native-vs-IR selector-hit error theorem for a supported
generated runtime. -/
private theorem nativeGeneratedCallDispatcherResult_selector_hit_error_artifact_matchesIR_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (nativeContract : YulContract) (fn : IRFunction)
    (hcompile : CompilationModel.compile spec selectors = .ok irContract)
    (hLowerRuntime : lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < UInt256.size) :
    CallDispatcherErrorArtifactMatchesIRGoal irContract tx state observableSlots nativeContract fn := by
  rcases lowerRuntimeContractNative_selector_hit_inner hcompile hSupported hLowerRuntime hFind with
    ⟨reservedNames, functions, body1, inner, switchStart, cases', midN, body',
      bodyStart, bodyEnd, rfl, hInner, hLowerCases, hCase, hBodyLower, hFuel⟩
  refine ⟨reservedNames, switchStart, cases', midN, body', bodyStart, bodyEnd,
    hLowerCases, hCase, hBodyLower, ?_⟩
  intro err nativeYul hBody hProject hMatch
  exact callDispatcher_matchesIR_of_exec_error
    (selector_hit_exec_error hFuel hInner hLowerCases hCase hSelectorRange hNoWrap
      (generatedRuntimeFunctionSelectorsRange_of_compile_ok_supported hcompile hSupported hSelectorsRange)
      hBody hProject)
    hProject hMatch

/-- Selector-hit error native-vs-IR theorem with native lowering produced from
`SupportedSpec + compile`. -/
theorem nativeGeneratedCallDispatcherResult_selector_hit_error_matchesIR_exists_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (fn : IRFunction)
    (err : Exception) (nativeYul : YulResult)
    (hcompile : CompilationModel.compile spec selectors = .ok irContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < UInt256.size) :
    ∃ (nativeContract : YulContract),
      lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract ∧
      CallDispatcherErrorMatchesIRGoal irContract tx state observableSlots nativeContract fn err nativeYul := by
  rcases lowerRuntimeContractNative_of_compile_ok_supported_exists hcompile hSupported with
    ⟨nativeContract, hLowerRuntime⟩
  exact ⟨nativeContract, hLowerRuntime,
    nativeGeneratedCallDispatcherResult_selector_hit_error_matchesIR_of_compile_ok_supported
      spec selectors hSupported irContract tx state observableSlots nativeContract fn err nativeYul
      hcompile hLowerRuntime hFind hSelectorRange hSelectorsRange hNoWrap⟩

private abbrev CallDispatcherOkMatchesIRBodyCont
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (nativeContract : YulContract)
    (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List Stmt))
    (body' : List Stmt) (final : State) (nativeYul : YulResult) : Prop :=
  (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
    exec (((nativeRuntimeDispatcherFuel irContract - (cases'.length + 20)) + 1) + suffix.length + 7)
      (.Block body') (some nativeContract)
      (nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId nativeContract (ofIR tx)
        state.storage (materializedStorageSlots (runtimeCode irContract) observableSlots)
        (freshNativeSwitchId reservedNames n0) nativeSwitchHasSelectorStore) = .ok final) →
  (∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
    NativeBlockPreservesWord (nativeSwitchMatchedTempName (freshNativeSwitchId reservedNames n0))
      (UInt256.ofNat 1) body' (some nativeContract)) →
  projectResult (ofIR tx) state.storage state.events (.ok (((final.reviveJump.overwrite?
    (initialState nativeContract (ofIR tx) state.storage
      (materializedStorageSlots (runtimeCode irContract) observableSlots))).setStore
    (initialState nativeContract (ofIR tx) state.storage
      (materializedStorageSlots (runtimeCode irContract) observableSlots))), [])) = nativeYul →
  nativeResultsMatchOn observableSlots (interpretIR irContract tx state) (.ok nativeYul) →
  nativeResultsMatchOn observableSlots (interpretIR irContract tx state)
    (nativeGeneratedCallDispatcherResultOf irContract tx state observableSlots nativeContract)

private abbrev CallDispatcherOkMatchesIRGoal
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (nativeContract : YulContract)
    (fn : IRFunction) (final : State) (nativeYul : YulResult) : Prop :=
  ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List Stmt))
    (midN : Nat) (body' : List Stmt) (bodyStart bodyEnd : Nat),
    lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames n0 + 1)
      (buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
    cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
    lowerStmtsNativeWithSwitchIds reservedNames bodyStart (switchCaseBody fn) = .ok (body', bodyEnd) ∧
    CallDispatcherOkMatchesIRBodyCont irContract tx state observableSlots nativeContract
      reservedNames n0 cases' body' final nativeYul

/-- Native-vs-IR selector-hit success theorem for a supported generated runtime. -/
private theorem nativeGeneratedCallDispatcherResult_selector_hit_ok_matchesIR_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (nativeContract : YulContract)
    (fn : IRFunction) (final : State) (nativeYul : YulResult)
    (hcompile : CompilationModel.compile spec selectors = .ok irContract)
    (hLowerRuntime : lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < UInt256.size) :
    CallDispatcherOkMatchesIRGoal irContract tx state observableSlots nativeContract fn final nativeYul := by
  rcases lowerRuntimeContractNative_selector_hit_inner hcompile hSupported hLowerRuntime hFind with
    ⟨reservedNames, functions, body1, inner, switchStart, cases', midN, body',
      bodyStart, bodyEnd, rfl, hInner, hLowerCases, hCase, hBodyLower, hFuel⟩
  refine ⟨reservedNames, switchStart, cases', midN, body', bodyStart, bodyEnd,
    hLowerCases, hCase, hBodyLower, ?_⟩
  intro hBody hPreservesMatched hProject hMatch
  exact callDispatcher_matchesIR_of_exec_ok
    (selector_hit_exec_ok_of_finalMatched (events := state.events) hFuel hInner hLowerCases hCase
      hSelectorRange hNoWrap
      (generatedRuntimeFunctionSelectorsRange_of_compile_ok_supported hcompile hSupported hSelectorsRange)
      hBody (finalMatched_of_case_preserves hCase hBody hPreservesMatched))
    hProject hMatch

private abbrev CallDispatcherOkForallMatchesIRGoal
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (nativeContract : YulContract) (fn : IRFunction) : Prop :=
  ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List Stmt))
    (midN : Nat) (body' : List Stmt) (bodyStart bodyEnd : Nat),
    lowerSwitchCasesNativeWithSwitchIds reservedNames (freshNativeSwitchId reservedNames n0 + 1)
      (buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
    cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
    lowerStmtsNativeWithSwitchIds reservedNames bodyStart (switchCaseBody fn) = .ok (body', bodyEnd) ∧
    (∀ final nativeYul,
      CallDispatcherOkMatchesIRBodyCont irContract tx state observableSlots nativeContract
        reservedNames n0 cases' body' final nativeYul)

/-- Native-vs-IR selector-hit success theorem for a supported generated runtime
with the selected-body result quantified inside the continuation. -/
private theorem nativeGeneratedCallDispatcherResult_selector_hit_ok_matchesIR_forall_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (nativeContract : YulContract) (fn : IRFunction)
    (hcompile : CompilationModel.compile spec selectors = .ok irContract)
    (hLowerRuntime : lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < UInt256.size) :
    CallDispatcherOkForallMatchesIRGoal irContract tx state observableSlots nativeContract fn := by
  rcases lowerRuntimeContractNative_selector_hit_inner hcompile hSupported hLowerRuntime hFind with
    ⟨reservedNames, functions, body1, inner, switchStart, cases', midN, body',
      bodyStart, bodyEnd, rfl, hInner, hLowerCases, hCase, hBodyLower, hFuel⟩
  refine ⟨reservedNames, switchStart, cases', midN, body', bodyStart, bodyEnd,
    hLowerCases, hCase, hBodyLower, ?_⟩
  intro final nativeYul hBody hPreservesMatched hProject hMatch
  exact callDispatcher_matchesIR_of_exec_ok
    (selector_hit_exec_ok_of_finalMatched (events := state.events) hFuel hInner hLowerCases hCase
      hSelectorRange hNoWrap
      (generatedRuntimeFunctionSelectorsRange_of_compile_ok_supported hcompile hSupported hSelectorsRange)
      hBody (finalMatched_of_case_preserves hCase hBody hPreservesMatched))
    hProject hMatch

private abbrev CallDispatcherOkMatchesIRExistsGoal
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (fn : IRFunction) (final : State) (nativeYul : YulResult) : Prop :=
  ∃ (nativeContract : YulContract),
    lowerRuntimeContractNative (emitYul irContract).runtimeCode = .ok nativeContract ∧
    ∃ (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List Stmt))
      (body' : List Stmt) (bodyStart bodyEnd : Nat),
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
      lowerStmtsNativeWithSwitchIds reservedNames bodyStart (switchCaseBody fn) = .ok (body', bodyEnd) ∧
      CallDispatcherOkMatchesIRBodyCont irContract tx state observableSlots nativeContract
        reservedNames n0 cases' body' final nativeYul

/-- Selector-hit success native-vs-IR theorem with native lowering produced
from `SupportedSpec + compile`. -/
theorem nativeGeneratedCallDispatcherResult_selector_hit_ok_matchesIR_exists_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat) (fn : IRFunction)
    (final : State) (nativeYul : YulResult)
    (hcompile : CompilationModel.compile spec selectors = .ok irContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < UInt256.size) :
    CallDispatcherOkMatchesIRExistsGoal irContract tx state observableSlots fn final nativeYul := by
  rcases lowerRuntimeContractNative_of_compile_ok_supported_exists hcompile hSupported with
    ⟨nativeContract, hLowerRuntime⟩
  rcases nativeGeneratedCallDispatcherResult_selector_hit_ok_matchesIR_of_compile_ok_supported
      spec selectors hSupported irContract tx state observableSlots nativeContract fn final nativeYul
      hcompile hLowerRuntime hFind hSelectorRange hSelectorsRange hNoWrap with
    ⟨reservedNames, n0, cases', _midN, body', bodyStart, bodyEnd,
      _hLowerCases, hCase, hBodyLower, hDispatcherContinuation⟩
  exact ⟨nativeContract, hLowerRuntime, reservedNames, n0, cases',
    body', bodyStart, bodyEnd, hCase, hBodyLower, hDispatcherContinuation⟩

end

private theorem lowerRuntimeContractNative_of_compile_ok_supported_mapping_ok_prefixed_block
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hMapping : irContract.usesMapping = true)
    (hLowerRuntime :
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract) :
    ∃ (inner : List EvmYul.Yul.Ast.Stmt) (nextSwitchId : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
          (Compiler.emitYul irContract).runtimeCode) 0
        [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok ([EvmYul.Yul.Ast.Stmt.Block inner], nextSwitchId) := by
  let reservedNames :=
    Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
      (Compiler.emitYul irContract).runtimeCode
  rcases lowerRuntimeContractNative_of_compile_ok_supported_mapping_ok_dispatcher_reserved
      hcompile hSupported hMapping hLowerRuntime with
    ⟨dispatcher, nextSwitchId, hLowerDispatcher, _hNativeContract⟩
  rcases
    lowerStmtsNativeWithSwitchIds_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
      reservedNames 0 irContract.functions dispatcher nextSwitchId hLowerDispatcher with
    ⟨inner, _hDispatcher, hLowerBlock⟩
  exact ⟨inner, nextSwitchId, by simpa [reservedNames] using hLowerBlock⟩

private theorem lowerRuntimeContractNative_of_compile_ok_supported_noMapping_ok_prefixed_block
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hNoMapping : irContract.usesMapping = false)
    (hLowerRuntime :
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract) :
    ∃ (inner : List EvmYul.Yul.Ast.Stmt) (nextSwitchId : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
          [Compiler.CodegenCommon.initFreeMemoryPointer,
            Compiler.CodegenCommon.buildSwitch irContract.functions none none]) 0
        [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok ([EvmYul.Yul.Ast.Stmt.Block inner], nextSwitchId) := by
  rcases lowerRuntimeContractNative_of_compile_ok_supported_noMapping_ok_dispatcher
      hcompile hSupported hNoMapping hLowerRuntime with
    ⟨dispatcher, hLowerDispatcher, _hNativeContract⟩
  rcases
    lowerStmtsNative_initFreeMemoryPointer_buildSwitch_noFallback_noReceive_ok_prefixed_block
      irContract.functions dispatcher hLowerDispatcher with
    ⟨inner, nextSwitchId, _hDispatcher, hLowerBlock⟩
  exact ⟨inner, nextSwitchId, hLowerBlock⟩

private theorem nativeGeneratedSelectorHitSuccessUserBodyLoweredArtifacts_of_lowered_block_payable
    (reservedNames : List String) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat)
    (inner : List EvmYul.Yul.Ast.Stmt) (nextSwitchId : Nat)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap) (fn : IRFunction)
    (hLowerBlock :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames 0
        [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok ([EvmYul.Yul.Ast.Stmt.Block inner], nextSwitchId))
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hPayable : fn.payable = true)
    (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0 + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) =
        some (tx.functionSelector, body') ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames
        userBodyStart fn.body = .ok (bodyNative, bodyEnd) := by
  let dummyNativeState : EvmYul.Yul.State := (inferInstance : Inhabited EvmYul.Yul.State).default
  let dummyYul : YulResult :=
    { success := false, returnValue := none, finalStorage := state.storage
      finalMappings := Compiler.Proofs.storageAsMappings state.storage, events := state.events }
  rcases
    nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_payable_withSwitchIds_generated_prefix
      0 reservedNames 0 irContract tx state observableSlots inner nextSwitchId functions fn
      dummyNativeState dummyYul hLowerBlock hFind hSelectorRange hNoWrap hFunctionSelectorsRange
      hPayable hguards hArgs with
    ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart,
      hLowerCases, hCase, hBodyLower, hUserBodyLower, _hDispatcherContinuation⟩
  exact ⟨reservedNames, switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower⟩

private theorem nativeGeneratedSelectorHitSuccessUserBodyLoweredArtifacts_of_lowered_block_nonpayable
    (reservedNames : List String) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat)
    (inner : List EvmYul.Yul.Ast.Stmt) (nextSwitchId : Nat)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap) (fn : IRFunction)
    (hLowerBlock :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames 0
        [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok ([EvmYul.Yul.Ast.Stmt.Block inner], nextSwitchId))
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hNonPayable : fn.payable = false)
    (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0 + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) =
        some (tx.functionSelector, body') ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames
        userBodyStart fn.body = .ok (bodyNative, bodyEnd) := by
  let dummyNativeState : EvmYul.Yul.State := (inferInstance : Inhabited EvmYul.Yul.State).default
  let dummyYul : YulResult :=
    { success := false, returnValue := none, finalStorage := state.storage
      finalMappings := Compiler.Proofs.storageAsMappings state.storage, events := state.events }
  rcases
    nativeDispatcherExecMatchesIRPositive_of_buildSwitch_selector_hit_ok_noFallback_noReceive_nonpayable_withSwitchIds_generated_prefix
      0 reservedNames 0 irContract tx state observableSlots inner nextSwitchId functions fn
      dummyNativeState dummyYul hLowerBlock hFind hSelectorRange hNoWrap hFunctionSelectorsRange
      hNonPayable hguards hArgs with
    ⟨switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd, userBodyStart,
      hLowerCases, hCase, hBodyLower, hUserBodyLower, _hDispatcherContinuation⟩
  exact ⟨reservedNames, switchStart, cases', midN, body', bodyNative, bodyStart, bodyEnd,
    userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower⟩

private theorem nativeGeneratedSelectorHitSuccessUserBodyLoweredArtifacts_of_lowered_block
    (reservedNames : List String) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat)
    (inner : List EvmYul.Yul.Ast.Stmt) (nextSwitchId : Nat)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap) (fn : IRFunction)
    (hLowerBlock :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames 0
        [Compiler.CodegenCommon.buildSwitch irContract.functions none none] =
        .ok ([EvmYul.Yul.Ast.Stmt.Block inner], nextSwitchId))
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hFunctionSelectorsRange :
      ∀ fn, fn ∈ irContract.functions → fn.selector < EvmYul.UInt256.size)
    (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0 + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) =
        some (tx.functionSelector, body') ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames
        userBodyStart fn.body = .ok (bodyNative, bodyEnd) := by
  by_cases hPayable : fn.payable
  · exact nativeGeneratedSelectorHitSuccessUserBodyLoweredArtifacts_of_lowered_block_payable
      reservedNames irContract tx state observableSlots inner nextSwitchId functions fn
      hLowerBlock hFind hSelectorRange hNoWrap hFunctionSelectorsRange
      (by simpa using hPayable) hguards hArgs
  · exact nativeGeneratedSelectorHitSuccessUserBodyLoweredArtifacts_of_lowered_block_nonpayable
      reservedNames irContract tx state observableSlots inner nextSwitchId functions fn
      hLowerBlock hFind hSelectorRange hNoWrap hFunctionSelectorsRange
      (Bool.eq_false_iff.2 hPayable) hguards hArgs

/-- Selector-hit success lowered artifacts for a supported generated runtime. -/
private theorem nativeGeneratedSelectorHitSuccessUserBodyLoweredArtifacts_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract)
    (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hLowerRuntime : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0 + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == tx.functionSelector) =
        some (tx.functionSelector, body') ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames
        userBodyStart fn.body = .ok (bodyNative, bodyEnd) := by
  have hFnSelRange :=
    generatedRuntimeFunctionSelectorsRange_of_compile_ok_supported hcompile hSupported hSelectorsRange
  by_cases hUsesMapping : irContract.usesMapping
  · rcases lowerRuntimeContractNative_of_compile_ok_supported_mapping_ok_prefixed_block
        spec selectors hSupported irContract nativeContract hcompile
        (by simpa using hUsesMapping) hLowerRuntime with ⟨inner, nextSwitchId, hLowerBlock⟩
    exact nativeGeneratedSelectorHitSuccessUserBodyLoweredArtifacts_of_lowered_block
      _ irContract tx state observableSlots inner nextSwitchId
      ((∅ : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap).insert "mappingSlot"
        Compiler.Proofs.YulGeneration.Backends.Native.nativeMappingSlotFunctionDefinition)
      fn hLowerBlock hFind hSelectorRange hNoWrap hFnSelRange hguards hArgs
  · rcases lowerRuntimeContractNative_of_compile_ok_supported_noMapping_ok_prefixed_block
        spec selectors hSupported irContract nativeContract hcompile
        (Bool.eq_false_iff.2 hUsesMapping) hLowerRuntime with ⟨inner, nextSwitchId, hLowerBlock⟩
    exact nativeGeneratedSelectorHitSuccessUserBodyLoweredArtifacts_of_lowered_block
      _ irContract tx state observableSlots inner nextSwitchId
      (∅ : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
      fn hLowerBlock hFind hSelectorRange hNoWrap hFnSelRange hguards hArgs

/-- Selector-hit success lowered artifacts with native runtime lowering from `compile`. -/
theorem nativeGeneratedSelectorHitSuccessUserBodyLoweredArtifacts_exists_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract)
    (tx : IRTransaction) (state : IRState) (observableSlots : List Nat) (fn : IRFunction)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors → selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (nativeContract : EvmYul.Yul.Ast.YulContract),
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      ∃ (reservedNames : List String) (n0 : Nat)
        (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
        (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
        Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0 + 1)
          (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
            irContract.functions) = .ok (cases', midN) ∧
        cases'.find? (fun entry => entry.1 == tx.functionSelector) =
          some (tx.functionSelector, body') ∧
        Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
          (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
        Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames
          userBodyStart fn.body = .ok (bodyNative, bodyEnd) := by
  rcases lowerRuntimeContractNative_of_compile_ok_supported_exists hcompile hSupported with
    ⟨nativeContract, hLowerRuntime⟩
  exact ⟨nativeContract, hLowerRuntime,
    nativeGeneratedSelectorHitSuccessUserBodyLoweredArtifacts_of_compile_ok_supported
      spec selectors hSupported irContract tx state observableSlots nativeContract fn
      hcompile hLowerRuntime hFind hSelectorRange hSelectorsRange hNoWrap hguards hArgs⟩

/-- Selector-hit lowered artifacts plus compile-derived selected-body closure. -/
theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.selected_body_artifacts_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat) (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract) (tx : IRTransaction) (state : IRState) (observableSlots : List Nat) (fn : IRFunction)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    ∃ (nativeContract : EvmYul.Yul.Ast.YulContract),
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      ∃ (reservedNames : List String) (n0 : Nat)
        (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
        (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
        Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0 + 1)
          (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases irContract.functions) = .ok (cases', midN) ∧
        cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') ∧
        Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
          (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) ∧
        Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames
          userBodyStart fn.body = .ok (bodyNative, bodyEnd) ∧
        Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body ∧
        4 + fn.params.length * 32 < EvmYul.UInt256.size := by
  rcases nativeGeneratedSelectorHitSuccessUserBodyLoweredArtifacts_exists_of_compile_ok_supported
      spec selectors hSupported irContract tx state observableSlots fn hcompile hFind
      hSelectorRange hSelectorsRange hNoWrap hguards hArgs with
    ⟨nativeContract, hLowerRuntime, reservedNames, n0, cases', midN, body', bodyNative,
      bodyStart, bodyEnd, userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower⟩
  rcases NativeGeneratedSelectedUserBodyResultBridgeAtFuel.selected_body_closure_of_compile_ok_supported
      spec selectors hSupported irContract tx hcompile fn reservedNames userBodyStart hFind with
    ⟨hBridged, _hLowered, hThreshold⟩
  exact ⟨nativeContract, hLowerRuntime, reservedNames, n0, cases', midN, body', bodyNative,
    bodyStart, bodyEnd, userBodyStart, hLowerCases, hCase, hBodyLower, hUserBodyLower, hBridged, hThreshold⟩

/-- Selector-hit bridge premise for the final generated-dispatcher composition.

The selector miss case is closed generically by
`nativeGeneratedCallDispatcherResult_selector_miss_matchesIR_of_compile_ok_supported`.
This predicate isolates the remaining selector-hit obligation: once the
generated runtime has lowered and `interpretIR` selected a function, the native
generated `callDispatcher` result must match the IR result. Proving this from
native execution of `lowerStmtsNativeWithSwitchIds ... fn.body` is the remaining
body-semantics bridge. -/
private def NativeGeneratedSelectorHitBridge
    (_spec : CompilationModel.CompilationModel) (_selectors : List Nat)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat) : Prop :=
  ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction),
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
    irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn →
    nativeResultsMatchOn observableSlots
      (interpretIR irContract tx state)
      (nativeGeneratedCallDispatcherResultOf irContract tx state
        observableSlots nativeContract)

/-- Success-only selector-hit bridge target.

Generated selector-hit guard failures are discharged separately by
`NativeGeneratedSelectorHitBridge.of_success_bridge_and_generated_guard_reverts`.
This predicate names the remaining selected-function success case: the selected
function has passed generated value/calldata guards, so the native generated
`callDispatcher` result must match the IR result. -/
def NativeGeneratedSelectorHitSuccessBridge
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat) : Prop :=
  ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction),
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
    irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn →
    DispatchGuardsSafe fn tx →
    fn.params.length ≤ tx.args.length →
    nativeResultsMatchOn observableSlots
      (interpretIR irContract tx state)
      (nativeGeneratedCallDispatcherResultOf irContract tx state
        observableSlots nativeContract)

/-- Native user-body fuel remaining after the generated selector-hit prefix.

The payable path contributes one less generated guard than the non-payable
path, so the direct lowered `fn.body` proof must use the same split as the
generated-prefix dispatcher lemmas. -/
noncomputable def nativeGeneratedSelectorHitUserBodyFuel
    (irContract : IRContract) (fn : IRFunction)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) : Nat :=
  if fn.payable then
    nativeRuntimeDispatcherFuel irContract - (cases'.length + 24)
  else
    nativeRuntimeDispatcherFuel irContract - (cases'.length + 25)

/-- Revived native function-body bridge with the IR side stated directly as the
selected function-body semantics.

This is the boundary expected from the future native body-correctness theorem:
after the generated dispatcher prefix has selected a function and its success
guards are known, prove the direct lowered `fn.body` native execution and match
it against `execIRFunction`. The theorem
`NativeGeneratedSelectorHitUserBodyBridgeAtFuelRevived.of_execIRFunction`
below retargets this to the top-level `interpretIR` bridge consumed by the
generated dispatcher stack. -/
private def NativeGeneratedSelectorHitUserBodyExecBridgeAtFuelRevived
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat) : Prop :=
  ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
    (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
    (bodyStart bodyEnd userBodyStart : Nat),
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
    irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn →
    cases'.find? (fun entry => entry.1 == tx.functionSelector) =
        some (tx.functionSelector, body') →
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
          .ok (body', bodyEnd) →
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames userBodyStart fn.body =
          .ok (bodyNative, bodyEnd) →
    DispatchGuardsSafe fn tx →
    fn.params.length ≤ tx.args.length →
    ∃ (final : EvmYul.Yul.State) (nativeYul : YulResult)
      (shared : EvmYul.SharedState EvmYul.OperationType.Yul)
      (store : EvmYul.Yul.VarStore),
      (∀ pre suffix,
        cases' = pre ++ (tx.functionSelector, body') :: suffix →
        EvmYul.Yul.exec
          (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
              suffix.length + 10) (.Block bodyNative)
          (some nativeContract)
          (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
            nativeContract
            (YulTransaction.ofIR tx)
            state.storage
            (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
              (Compiler.runtimeCode irContract) observableSlots)
            (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
              reservedNames n0)
            Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) =
          .ok final) ∧
      (∀ pre suffix,
        cases' = pre ++ (tx.functionSelector, body') :: suffix →
        Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord
          (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
            (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
              reservedNames n0))
          (EvmYul.UInt256.ofNat 1) bodyNative
          (some nativeContract)) ∧
      final.reviveJump = EvmYul.Yul.State.Ok shared store ∧
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events
        (.ok (final.reviveJump, [])) =
        nativeYul ∧
      nativeResultsMatchOn observableSlots
        (execIRFunction fn tx.args (applyIRTransactionContext tx state))
        (.ok nativeYul)

/-- Revived native function-body ExecBridge without matched-flag
preservation.

This separates the semantic part of the future native body-correctness theorem
from the dispatcher-local matched-temp preservation proof. The preservation
side can be supplied independently from native switch freshness and
per-statement no-write facts, then recombined by
`NativeGeneratedSelectorHitUserBodyExecBridgeAtFuelRevived.of_exec_only_and_preserves`.
-/
private def NativeGeneratedSelectorHitUserBodyExecOnlyBridgeAtFuelRevived
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat) : Prop :=
  ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
    (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
    (bodyStart bodyEnd userBodyStart : Nat),
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
    irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn →
    cases'.find? (fun entry => entry.1 == tx.functionSelector) =
        some (tx.functionSelector, body') →
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
          .ok (body', bodyEnd) →
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames userBodyStart fn.body =
          .ok (bodyNative, bodyEnd) →
    DispatchGuardsSafe fn tx →
    fn.params.length ≤ tx.args.length →
    ∃ (final : EvmYul.Yul.State) (nativeYul : YulResult)
      (shared : EvmYul.SharedState EvmYul.OperationType.Yul)
      (store : EvmYul.Yul.VarStore),
      (∀ pre suffix,
        cases' = pre ++ (tx.functionSelector, body') :: suffix →
        EvmYul.Yul.exec
          (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
              suffix.length + 10) (.Block bodyNative)
          (some nativeContract)
          (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
            nativeContract
            (YulTransaction.ofIR tx)
            state.storage
            (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
              (Compiler.runtimeCode irContract) observableSlots)
            (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
              reservedNames n0)
            Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) =
          .ok final) ∧
      final.reviveJump = EvmYul.Yul.State.Ok shared store ∧
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events
        (.ok (final.reviveJump, [])) =
        nativeYul ∧
      nativeResultsMatchOn observableSlots
        (execIRFunction fn tx.args (applyIRTransactionContext tx state))
        (.ok nativeYul)

/-- Direct selected-user-body halt bridge.

This is the halt-channel companion to
`NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived`: it targets the
lowered `fn.body` directly when the generated user body exits through
`stop`/`return`, which EVMYulLean represents as `YulHalt`. -/
def NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat) : Prop :=
  ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
    (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (bodyNative : List EvmYul.Yul.Ast.Stmt)
    (bodyEnd userBodyStart : Nat),
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
    irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn →
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames userBodyStart fn.body =
          .ok (bodyNative, bodyEnd) →
    DispatchGuardsSafe fn tx →
    fn.params.length ≤ tx.args.length →
    ∃ (haltState : EvmYul.Yul.State) (haltValue : EvmYul.Yul.Ast.Literal)
      (nativeYul : YulResult),
      (∀ (_pre : List (Nat × List EvmYul.Yul.Ast.Stmt))
          (suffix : List (Nat × List EvmYul.Yul.Ast.Stmt)),
        EvmYul.Yul.exec
          (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
              suffix.length + 10) (.Block bodyNative)
          (some nativeContract)
          (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
            nativeContract
            (YulTransaction.ofIR tx)
            state.storage
            (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
              (Compiler.runtimeCode irContract) observableSlots)
            (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
              reservedNames n0)
            Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) =
          .error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) ∧
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        nativeYul ∧
      nativeResultsMatchOn observableSlots
        (execIRFunction fn tx.args (applyIRTransactionContext tx state))
        (.ok nativeYul)

private def NativeGeneratedSwitchCaseBodyHaltAtFuel
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction) (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (body' : List EvmYul.Yul.Ast.Stmt) : Prop :=
  ∃ (haltState : EvmYul.Yul.State) (haltValue : EvmYul.Yul.Ast.Literal)
    (nativeYul : YulResult),
    (∀ pre suffix,
      cases' = pre ++ (tx.functionSelector, body') :: suffix →
      EvmYul.Yul.exec
        (((nativeRuntimeDispatcherFuel irContract - (cases'.length + 20)) +
              1) + suffix.length + 7) (.Block body')
        (some nativeContract)
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
          nativeContract (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode irContract) observableSlots)
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0)
          Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) ∧
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      (YulTransaction.ofIR tx) state.storage state.events
      (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
      nativeYul ∧
    nativeResultsMatchOn observableSlots
      (execIRFunction fn tx.args (applyIRTransactionContext tx state))
      (.ok nativeYul)

/-- Lift a direct selected-user-body halt proof through the payable switch-case prefix. -/
private theorem exec_switchCaseBody_payable_halt_of_selected_user_body_halt
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction) (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hLowerRuntime : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hBodyLower : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
      reservedNames bodyStart (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
        .ok (body', bodyEnd))
    (hPayable : fn.payable = true) (hguards : DispatchGuardsSafe fn tx)
    (hArgs : fn.params.length ≤ tx.args.length)
    (hBound24 : cases'.length + 24 ≤ nativeRuntimeDispatcherFuel irContract)
    (hSelectedUserBodyHalt :
      NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state observableSlots) :
    NativeGeneratedSwitchCaseBodyHaltAtFuel irContract tx state observableSlots
      nativeContract fn reservedNames n0 cases' body' := by
  rcases Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_eq
      reservedNames bodyStart fn body' bodyEnd hPayable hBodyLower with
    ⟨guardBody, bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
  rcases hSelectedUserBodyHalt nativeContract fn reservedNames n0 cases'
      bodyNative bodyEnd userBodyStart hLowerRuntime hFind hUserBodyLower hguards hArgs with
    ⟨haltState, haltValue, nativeYul, hBody, hProject, hMatch⟩
  refine ⟨haltState, haltValue, nativeYul, ?_, hProject, hMatch⟩
  intro pre suffix _hCases
  rw [hBodyShape]
  have hPrefix :=
    Compiler.Proofs.YulGeneration.Backends.Native.exec_switchCaseBody_payable_prefix_postInitFreeMemory_eq
      (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' + suffix.length + 1)
      guardBody bodyNative nativeContract (YulTransaction.ofIR tx) state.storage
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots)
      (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0)
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
      (4 + fn.params.length * 32) (by simpa [YulTransaction.ofIR_args] using hNoWrap)
      (Compiler.Proofs.YulGeneration.Backends.Native.DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
      (Nat.add_le_add_left (Nat.mul_le_mul_right 32 hArgs) 4)
  have hFuelEq :
      suffix.length + (1 + (11 + (nativeRuntimeDispatcherFuel irContract - (cases'.length + 24)))) =
        suffix.length + (1 + (7 + (nativeRuntimeDispatcherFuel irContract - (cases'.length + 20)))) := by
    omega
  simpa [nativeGeneratedSelectorHitUserBodyFuel, hPayable,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hFuelEq] using hPrefix.trans (hBody pre suffix)

/-- Lift a direct selected-user-body halt proof through the nonpayable switch-case prefix. -/
private theorem exec_switchCaseBody_nonpayable_halt_of_selected_user_body_halt
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction) (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hLowerRuntime : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hBodyLower : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
      reservedNames bodyStart (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
        .ok (body', bodyEnd))
    (hNonPayable : fn.payable = false) (hguards : DispatchGuardsSafe fn tx)
    (hArgs : fn.params.length ≤ tx.args.length)
    (hBound25 : cases'.length + 25 ≤ nativeRuntimeDispatcherFuel irContract)
    (hSelectedUserBodyHalt :
      NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state observableSlots) :
    NativeGeneratedSwitchCaseBodyHaltAtFuel irContract tx state observableSlots
      nativeContract fn reservedNames n0 cases' body' := by
  rcases Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_eq
      reservedNames bodyStart fn body' bodyEnd hNonPayable hBodyLower with
    ⟨callvalueGuardBody, calldataGuardBody, bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
  rcases hSelectedUserBodyHalt nativeContract fn reservedNames n0 cases'
      bodyNative bodyEnd userBodyStart hLowerRuntime hFind hUserBodyLower hguards hArgs with
    ⟨haltState, haltValue, nativeYul, hBody, hProject, hMatch⟩
  refine ⟨haltState, haltValue, nativeYul, fun pre suffix _hCases => ?_, hProject, hMatch⟩
  rw [hBodyShape]
  have hPrefix :=
    Compiler.Proofs.YulGeneration.Backends.Native.exec_switchCaseBody_nonpayable_prefix_postInitFreeMemory_eq
      (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' + suffix.length + 1)
      callvalueGuardBody calldataGuardBody bodyNative nativeContract (YulTransaction.ofIR tx)
      state.storage (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots)
      (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0)
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
      (4 + fn.params.length * 32)
      (Compiler.Proofs.YulGeneration.Backends.Native.DispatchGuardsSafe_msgValue_zero_mod_of_nonpayable
        fn tx hguards hNonPayable)
      (by simpa [YulTransaction.ofIR_args] using hNoWrap)
      (Compiler.Proofs.YulGeneration.Backends.Native.DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
      (Nat.add_le_add_left (Nat.mul_le_mul_right 32 hArgs) 4)
  have hFuelEq :
      suffix.length + (1 + (12 + (nativeRuntimeDispatcherFuel irContract - (cases'.length + 25)))) =
        suffix.length + (1 + (7 + (nativeRuntimeDispatcherFuel irContract - (cases'.length + 20)))) := by omega
  simpa [nativeGeneratedSelectorHitUserBodyFuel, hNonPayable,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hFuelEq] using hPrefix.trans (hBody pre suffix)

/-- Lift a direct selected-user-body halt proof through either switch-case prefix. -/
private theorem exec_switchCaseBody_halt_of_selected_user_body_halt
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction) (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hLowerRuntime : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hBodyLower : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
      reservedNames bodyStart (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
        .ok (body', bodyEnd))
    (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length)
    (hBound24 : fn.payable = true → cases'.length + 24 ≤ nativeRuntimeDispatcherFuel irContract)
    (hBound25 : fn.payable = false → cases'.length + 25 ≤ nativeRuntimeDispatcherFuel irContract)
    (hSelectedUserBodyHalt :
      NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state observableSlots) :
    NativeGeneratedSwitchCaseBodyHaltAtFuel irContract tx state observableSlots
      nativeContract fn reservedNames n0 cases' body' := by
  by_cases hPayable : fn.payable
  · exact exec_switchCaseBody_payable_halt_of_selected_user_body_halt
      irContract tx state observableSlots nativeContract fn reservedNames n0 cases'
      body' bodyStart bodyEnd hNoWrap hLowerRuntime hFind hBodyLower
      (by simpa using hPayable) hguards hArgs (hBound24 (by simpa using hPayable))
      hSelectedUserBodyHalt
  · have hNonPayable : fn.payable = false := Bool.eq_false_iff.2 hPayable
    exact exec_switchCaseBody_nonpayable_halt_of_selected_user_body_halt
      irContract tx state observableSlots nativeContract fn reservedNames n0 cases'
      body' bodyStart bodyEnd hNoWrap hLowerRuntime hFind hBodyLower
      hNonPayable hguards hArgs (hBound25 hNonPayable) hSelectedUserBodyHalt

private theorem nativeRuntimeDispatcherFuel_ge_lowered_cases_length_plus24
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract)
    (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hLowerCases :
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0 + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions) = .ok (cases', midN)) :
    cases'.length + 24 ≤ nativeRuntimeDispatcherFuel irContract := by
  dsimp [nativeRuntimeDispatcherFuel]
  by_cases hUsesMapping : irContract.usesMapping
  · exact sizeOf_emitYul_runtimeCode_mapping_ge_lowered_cases_length_plus24
      hcompile hSupported (by simpa using hUsesMapping) hLowerCases
  · exact sizeOf_emitYul_runtimeCode_noMapping_ge_lowered_cases_length_plus24
      hcompile hSupported (Bool.eq_false_iff.2 hUsesMapping) hLowerCases

private theorem nativeRuntimeDispatcherFuel_ge_lowered_cases_length_plus25
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract)
    (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hLowerCases :
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0 + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases
          irContract.functions) = .ok (cases', midN)) :
    cases'.length + 25 ≤ nativeRuntimeDispatcherFuel irContract := by
  dsimp [nativeRuntimeDispatcherFuel]
  by_cases hUsesMapping : irContract.usesMapping
  · exact sizeOf_emitYul_runtimeCode_mapping_ge_lowered_cases_length_plus25
      hcompile hSupported (by simpa using hUsesMapping) hLowerCases
  · exact sizeOf_emitYul_runtimeCode_noMapping_ge_lowered_cases_length_plus25
      hcompile hSupported (Bool.eq_false_iff.2 hUsesMapping) hLowerCases

/-- A direct selected-user-body halt bridge supplies the public selector-hit
success bridge for supported generated runtimes. -/
private theorem NativeGeneratedSelectorHitSuccessBridge.of_selected_user_body_halt_exec_atFuel
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract)
    (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors → selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hSelectedUserBodyHalt :
      NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state observableSlots) :
    NativeGeneratedSelectorHitSuccessBridge irContract tx state observableSlots := by
  intro nativeContract fn hLowerRuntime hFind hguards hArgs
  rcases
    nativeGeneratedCallDispatcherResult_selector_hit_error_artifact_matchesIR_of_compile_ok_supported
      spec selectors hSupported irContract tx state observableSlots
      nativeContract fn hcompile hLowerRuntime hFind hSelectorRange
      hSelectorsRange hNoWrap with
    ⟨reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
      hLowerCases, _hCase, hBodyLower, hDispatcherContinuation⟩
  rcases exec_switchCaseBody_halt_of_selected_user_body_halt
      irContract tx state observableSlots nativeContract fn reservedNames n0 cases'
      body' bodyStart bodyEnd hNoWrap hLowerRuntime hFind hBodyLower hguards hArgs
      (fun _ => nativeRuntimeDispatcherFuel_ge_lowered_cases_length_plus24
        spec selectors hSupported irContract reservedNames n0 cases' midN hcompile hLowerCases)
      (fun _ => nativeRuntimeDispatcherFuel_ge_lowered_cases_length_plus25
        spec selectors hSupported irContract reservedNames n0 cases' midN hcompile hLowerCases)
      hSelectedUserBodyHalt with
    ⟨haltState, haltValue, nativeYul, hCaseBody, hProject, hMatchExec⟩
  exact hDispatcherContinuation (EvmYul.Yul.Exception.YulHalt haltState haltValue) nativeYul
    hCaseBody hProject
    (nativeResultsMatchOn_interpretIR_of_execIRFunction_dispatchGuards
      irContract tx state observableSlots fn (.ok nativeYul) hFind hguards hArgs hMatchExec)

/-- Direct selected-user-body ExecBridge without switch-case lowering
artifacts.

This is the narrowest current success-case target for the future native
function-body theorem: the selected `fn.body` has lowered successfully, the
generated success guards are known, and executing the lowered body at the exact
dispatcher-provided fuel projects to the selected IR function semantics. The
small projection theorem below threads this cleaner body target into the
existing dispatcher bridge that still carries switch-case evidence. -/
private def NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat) : Prop :=
  ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
    (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (bodyNative : List EvmYul.Yul.Ast.Stmt)
    (bodyEnd userBodyStart : Nat),
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
    irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn →
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames userBodyStart fn.body =
          .ok (bodyNative, bodyEnd) →
    DispatchGuardsSafe fn tx →
    fn.params.length ≤ tx.args.length →
    ∃ (final : EvmYul.Yul.State) (nativeYul : YulResult)
      (shared : EvmYul.SharedState EvmYul.OperationType.Yul)
      (store : EvmYul.Yul.VarStore),
      (∀ (_pre : List (Nat × List EvmYul.Yul.Ast.Stmt))
          (suffix : List (Nat × List EvmYul.Yul.Ast.Stmt)),
        EvmYul.Yul.exec
          (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' +
              suffix.length + 10) (.Block bodyNative)
          (some nativeContract)
          (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
            nativeContract
            (YulTransaction.ofIR tx)
            state.storage
            (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
              (Compiler.runtimeCode irContract) observableSlots)
            (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
              reservedNames n0)
            Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) =
          .ok final) ∧
      final.reviveJump = EvmYul.Yul.State.Ok shared store ∧
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events
        (.ok (final.reviveJump, [])) =
        nativeYul ∧
      nativeResultsMatchOn observableSlots
        (execIRFunction fn tx.args (applyIRTransactionContext tx state))
        (.ok nativeYul)

/-- Empty selected user bodies execute as a native no-op and project to the same
observable result as `execIRFunction`.

This is the base case for the remaining selected-function-body theorem. It also
records the transaction-entry invariant that stale IR return values are cleared
before function execution, matching the native transaction entry state. -/
private theorem nativeResultsMatchOn_execIRFunction_empty_body_markedPrefix
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (fn : IRFunction)
    (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (hBody : fn.body = []) :
    nativeResultsMatchOn observableSlots
      (execIRFunction fn tx.args (applyIRTransactionContext tx state))
      (.ok
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events
          (.ok
            ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
              nativeContract (YulTransaction.ofIR tx) state.storage
              (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
                (Compiler.runtimeCode irContract) observableSlots)
              switchId store).reviveJump, [])))) := by
  simp only [nativeResultsMatchOn,
    Compiler.Proofs.YulGeneration.Backends.Native.nativeResultsMatchOn]
  simp [hBody, applyIRTransactionContext,
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId_reviveJump_eq]
  constructor
  · intro slot hSlot
    exact
      (Compiler.Proofs.YulGeneration.Backends.Native.projectResult_ok_nativeSwitchStoreMarkedPrefixStateForId_observableStorageSlot
        nativeContract (YulTransaction.ofIR tx) state.storage state.events
        (Compiler.runtimeCode irContract) observableSlots switchId store slot
        hSlot).symm
  · simpa [Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState]
      using
        (Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState_nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
          nativeContract (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode irContract) observableSlots)
          switchId store)

/-- Build the direct selected-user-body ExecBridge for contracts whose
selected generated function body is empty. -/
private theorem NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived.of_empty_body
    (irContract : IRContract) (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (hEmpty : ∀ fn,
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      fn.body = []) :
    NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived irContract tx state observableSlots := by
  intro nativeContract fn reservedNames n0 cases' bodyNative bodyEnd
    userBodyStart _hLowerRuntime hFind hUserBodyLower _hguards _hArgs
  have hBody : fn.body = [] := hEmpty fn hFind
  simp [hBody] at hUserBodyLower
  rcases hUserBodyLower with ⟨rfl, _rfl⟩
  let switchId := Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0
  let final :=
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
      nativeContract (YulTransaction.ofIR tx) state.storage
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots)
      switchId Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
  let nativeYul :=
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      (YulTransaction.ofIR tx) state.storage state.events (.ok (final.reviveJump, []))
  have hFinalOk : ∃ shared store, final = EvmYul.Yul.State.Ok shared store := by
    simp [final,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStorePrefixStateForId,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryState,
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemorySharedState,
      EvmYul.Yul.State.insert]
  rcases hFinalOk with ⟨shared, store, hFinalOk⟩
  refine ⟨final, nativeYul, shared, store, ?_, by rw [hFinalOk]; rfl, rfl, ?_⟩
  · intro _pre suffix
    simpa [final] using
      (Compiler.Proofs.YulGeneration.Backends.Native.exec_block_nil_ok_add_ten
        (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases')
        suffix.length (some nativeContract) final)
  · exact nativeResultsMatchOn_execIRFunction_empty_body_markedPrefix
      irContract tx state observableSlots nativeContract fn switchId
      Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore hBody

/-- Selected user bodies containing only `stop` execute as a native halt and
project to the same observable result as `execIRFunction`. -/
private theorem nativeResultsMatchOn_execIRFunction_stop_body_markedPrefix
    (irContract : IRContract) (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction) (switchId : Nat)
    (store : EvmYul.Yul.VarStore)
    (hBody : fn.body = [Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])]) :
    nativeResultsMatchOn observableSlots
      (execIRFunction fn tx.args (applyIRTransactionContext tx state))
      (.ok (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events
        (.error (EvmYul.Yul.Exception.YulHalt
          (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
            nativeContract (YulTransaction.ofIR tx) state.storage
            (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
              (Compiler.runtimeCode irContract) observableSlots)
            switchId store) ⟨0⟩)))) := by
  simp only [nativeResultsMatchOn, Compiler.Proofs.YulGeneration.Backends.Native.nativeResultsMatchOn]
  rw [Compiler.Proofs.IRGeneration.execIRFunction_single_stop fn tx.args
    (applyIRTransactionContext tx state) hBody]
  simp [applyIRTransactionContext]
  refine ⟨fun slot hSlot =>
    (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId_materializedStorageSlot
      nativeContract (YulTransaction.ofIR tx) state.storage
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots)
      switchId store slot
      (Compiler.Proofs.YulGeneration.Backends.Native.observableSlot_mem_materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots slot hSlot)).symm, ?_⟩
  simpa [Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState] using
    (Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState_nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
      nativeContract (YulTransaction.ofIR tx) state.storage
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots) switchId store)

/-- Build the direct selected-user-body halt bridge for contracts whose
selected generated function body is `stop`. -/
private theorem NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_stop_body
    (irContract : IRContract) (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (hStop : ∀ fn,
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      fn.body = [Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])]) :
    NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state observableSlots := by
  intro nativeContract fn reservedNames n0 cases' bodyNative bodyEnd
    userBodyStart _hLowerRuntime hFind hUserBodyLower _hguards _hArgs
  have hBody : fn.body = [Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])] := hStop fn hFind
  rw [hBody] at hUserBodyLower
  simp [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons,
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
    Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_expr,
    Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil] at hUserBodyLower
  rcases hUserBodyLower with ⟨rfl, _rfl⟩
  let switchId := Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0
  let haltState :=
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId
      nativeContract (YulTransaction.ofIR tx) state.storage
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode irContract) observableSlots)
      switchId Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore
  let nativeYul :=
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      (YulTransaction.ofIR tx) state.storage state.events
      (.error (EvmYul.Yul.Exception.YulHalt haltState ⟨0⟩))
  refine ⟨haltState, ⟨0⟩, nativeYul, ?_, rfl, ?_⟩
  · intro _pre suffix
    simpa [switchId, haltState] using
      (Compiler.Proofs.YulGeneration.Backends.Native.exec_block_stop_halt_add_ten
        (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases')
        suffix.length (some nativeContract) haltState)
  · simpa [switchId, haltState, nativeYul] using
      (nativeResultsMatchOn_execIRFunction_stop_body_markedPrefix
        irContract tx state observableSlots nativeContract fn switchId
        Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore hBody)

/-- Matched-flag preservation bridge for direct lowered selected user bodies. -/
private def NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel
    (irContract : IRContract)
    (tx : IRTransaction) : Prop :=
  ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
    (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (body' bodyNative : List EvmYul.Yul.Ast.Stmt)
    (bodyStart bodyEnd userBodyStart : Nat),
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
    irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn →
    cases'.find? (fun entry => entry.1 == tx.functionSelector) =
        some (tx.functionSelector, body') →
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
          .ok (body', bodyEnd) →
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames userBodyStart fn.body =
          .ok (bodyNative, bodyEnd) →
    ∀ pre suffix,
      cases' = pre ++ (tx.functionSelector, body') :: suffix →
      Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord
        (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
            reservedNames n0))
        (EvmYul.UInt256.ofNat 1) bodyNative (some nativeContract)

/-- Unified selected-user-body result boundary.

Native lowered function bodies can finish either by returning normally to the
Yul function frame (`leave`, represented by `.ok final` with a revivable
checkpoint) or by a generated EVM halt such as `stop`/`return` (represented by
`YulHalt`). This predicate keeps the remaining native function-body theorem
from having to pick one dispatcher adapter prematurely. The normal path also
carries the dispatcher-local matched-flag preservation fact needed by the
generated switch-case continuation. -/
def NativeGeneratedSelectedUserBodyResultBridgeAtFuel
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat) : Prop :=
  NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state
      observableSlots ∨
    (NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived irContract tx
        state observableSlots ∧
      NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel irContract tx)

theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_halt
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hHalt :
      NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel irContract tx state
        observableSlots) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
      observableSlots :=
  Or.inl hHalt

theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_stop_body
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hStop :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = [Yul.YulStmt.exprStmt (Yul.YulExpr.call "stop" [])]) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
      observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_halt irContract tx state
    observableSlots
    (NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_stop_body
      irContract tx state observableSlots hStop)

theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_exec_only_and_preserves
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hExec :
      NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived irContract tx
        state observableSlots)
    (hPreserves :
      NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel irContract tx) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
      observableSlots :=
  Or.inr ⟨hExec, hPreserves⟩

/-- Project the direct selected-user-body execution target into the existing
dispatcher-shaped exec-only bridge. -/
private theorem NativeGeneratedSelectorHitUserBodyExecOnlyBridgeAtFuelRevived.of_selected_user_body_exec_only
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hBridge :
      NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived irContract tx
        state observableSlots) :
    NativeGeneratedSelectorHitUserBodyExecOnlyBridgeAtFuelRevived irContract tx
      state observableSlots := by
  intro nativeContract fn reservedNames n0 cases' body' bodyNative bodyStart
    bodyEnd userBodyStart hLowerRuntime hFind _hCase _hBodyLower hUserBodyLower
    hguards hArgs
  unfold NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived at hBridge
  rcases hBridge nativeContract fn reservedNames n0 cases' bodyNative bodyEnd
      userBodyStart hLowerRuntime hFind hUserBodyLower hguards hArgs with
    ⟨final, nativeYul, shared, store, hBody, hRevive, hProject, hMatch⟩
  refine ⟨final, nativeYul, shared, store, ?_, hRevive, hProject, hMatch⟩
  intro pre suffix _hCases
  exact hBody pre suffix

/-- Build the selected user-body preservation bridge from block-level native
write-name freshness and per-statement preservation. -/
private theorem NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel.of_nativeStmtsWriteNames_not_mem
    (irContract : IRContract) (tx : IRTransaction)
    (hFresh : ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
        (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
        (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0) ∉
      Compiler.Proofs.YulGeneration.Backends.nativeStmtsWriteNames bodyNative)
    (hStmtPreserves : ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
        (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
        (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) →
      ∀ stmt, stmt ∈ bodyNative →
        Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0) ∉
        Compiler.Proofs.YulGeneration.Backends.nativeStmtWriteNames stmt →
        Compiler.Proofs.YulGeneration.Backends.Native.NativeStmtPreservesWord
          (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
            (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0))
          (EvmYul.UInt256.ofNat 1) stmt (some nativeContract)) :
    NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel irContract tx := by
  intro nativeContract fn reservedNames n0 cases' body' bodyNative bodyStart
    bodyEnd userBodyStart hLowerRuntime hFind hCase hBodyLower hUserBodyLower _pre _suffix _hCases
  exact Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
    (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
      (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0))
    (EvmYul.UInt256.ofNat 1) bodyNative (some nativeContract)
    (hFresh nativeContract fn reservedNames n0 cases' body' bodyNative
      bodyStart bodyEnd userBodyStart hLowerRuntime hFind hCase hBodyLower hUserBodyLower)
    (hStmtPreserves nativeContract fn reservedNames n0 cases' body'
      bodyNative bodyStart bodyEnd userBodyStart hLowerRuntime hFind hCase hBodyLower hUserBodyLower)

/-- Package direct selected-body execution with block-fresh preservation into
the unified selected-body result boundary. -/
theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_exec_only_and_nativeStmtsWriteNames_not_mem
    (irContract : IRContract) (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (hExec : NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived irContract tx state observableSlots)
    (hFresh : ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
        (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
        (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0) ∉
      Compiler.Proofs.YulGeneration.Backends.nativeStmtsWriteNames bodyNative)
    (hStmtPreserves : ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
        (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
        (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) →
      ∀ stmt, stmt ∈ bodyNative →
        Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0) ∉
        Compiler.Proofs.YulGeneration.Backends.nativeStmtWriteNames stmt →
        Compiler.Proofs.YulGeneration.Backends.Native.NativeStmtPreservesWord
          (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
            (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0))
          (EvmYul.UInt256.ofNat 1) stmt (some nativeContract)) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_exec_only_and_preserves
    irContract tx state observableSlots hExec
    (NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel.of_nativeStmtsWriteNames_not_mem
      irContract tx hFresh hStmtPreserves)

private theorem NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel.of_mappingFreePreservableStraightStmts
    (irContract : IRContract) (tx : IRTransaction)
    (hBodyStraight : ∀ fn,
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      Compiler.Proofs.YulGeneration.Backends.Native.NativeMappingFreePreservableStraightStmts fn.body)
    (hFresh : ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
        (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
        (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0) ∉
      Compiler.Proofs.YulGeneration.Backends.nativeStmtsWriteNames bodyNative) :
    NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel irContract tx := by
  intro nativeContract fn reservedNames n0 cases' body' bodyNative bodyStart
    bodyEnd userBodyStart hLowerRuntime hFind hCase hBodyLower hUserBodyLower _pre _suffix _hCases
  exact Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord_lowerStmtsNativeWithSwitchIds_of_mappingFreePreservableStraightStmts
    (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
      (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0))
    (EvmYul.UInt256.ofNat 1) reservedNames userBodyStart fn.body bodyNative bodyEnd
    (some nativeContract) (hBodyStraight fn hFind) hUserBodyLower
    (hFresh nativeContract fn reservedNames n0 cases' body' bodyNative
      bodyStart bodyEnd userBodyStart hLowerRuntime hFind hCase hBodyLower hUserBodyLower)

/-- Package direct selected-body execution with the mapping-free straight-body
preservation closure into the unified selected-body result bridge. -/
theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_exec_only_and_mappingFreePreservableStraightStmts
    (irContract : IRContract) (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (hExec : NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived irContract tx state observableSlots)
    (hBodyStraight : ∀ fn,
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      Compiler.Proofs.YulGeneration.Backends.Native.NativeMappingFreePreservableStraightStmts fn.body)
    (hFresh : ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
        (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
        (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0) ∉
      Compiler.Proofs.YulGeneration.Backends.nativeStmtsWriteNames bodyNative) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_exec_only_and_preserves
    irContract tx state observableSlots hExec
    (NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel.of_mappingFreePreservableStraightStmts
      irContract tx hBodyStraight hFresh)

/-- Package direct selected-body execution with historical straight-body
closure after excluding the mapping helper recursively. -/
theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_exec_only_and_bridgedStraightStmts_mappingFree
    (irContract : IRContract) (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (hExec : NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived irContract tx state observableSlots)
    (hBodyStraight : ∀ fn,
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      Compiler.Proofs.YulGeneration.Backends.BridgedStraightStmts fn.body)
    (hMappingFreeSide : ∀ fn,
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      ∀ stmt, stmt ∈ fn.body →
        Compiler.Proofs.YulGeneration.Backends.Native.NativeMappingFreeSideConditionForBridgedStraightStmt stmt)
    (hFresh : ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
        (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
        (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0) ∉
      Compiler.Proofs.YulGeneration.Backends.nativeStmtsWriteNames bodyNative) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_exec_only_and_mappingFreePreservableStraightStmts
    irContract tx state observableSlots hExec
    (fun fn hFind =>
      Compiler.Proofs.YulGeneration.Backends.Native.NativeMappingFreePreservableStraightStmts.of_bridgedStraightStmts
        (hBodyStraight fn hFind) (hMappingFreeSide fn hFind))
    hFresh

/-- Build the direct selected user-body preservation bridge for mapping-helper
generated runtimes whose selected source body is in the straight bridged fragment. -/
private theorem NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel.of_bridgedStraightStmts_mapping
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract) (tx : IRTransaction)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hMapping : irContract.usesMapping = true)
    (hBodyStraight : ∀ fn,
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      Compiler.Proofs.YulGeneration.Backends.BridgedStraightStmts fn.body)
    (hSide : ∀ fn,
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      ∀ stmt, stmt ∈ fn.body →
        Compiler.Proofs.YulGeneration.Backends.Native.NativePreservableSideConditionForBridgedStraightStmt stmt)
    (hFresh : ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
        (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
        (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0) ∉
      Compiler.Proofs.YulGeneration.Backends.nativeStmtsWriteNames bodyNative) :
    NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel irContract tx := by
  intro nativeContract fn reservedNames n0 cases' body' bodyNative bodyStart
    bodyEnd userBodyStart hLowerRuntime hFind hCase hBodyLower hUserBodyLower _pre _suffix _hCases
  rcases lowerRuntimeContractNative_of_compile_ok_supported_mapping_ok_dispatcher_reserved
      hcompile hSupported hMapping hLowerRuntime with
    ⟨dispatcher, _nextSwitchId, _hLowerDispatcher, hNativeContract⟩
  subst nativeContract
  exact Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord_lowerStmtsNativeWithSwitchIds_of_bridgedStraightStmts
    (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
      (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0))
    (EvmYul.UInt256.ofNat 1) reservedNames userBodyStart fn.body bodyNative bodyEnd
    (.Block dispatcher) (hBodyStraight fn hFind) (hSide fn hFind) hUserBodyLower
    (hFresh (nativeContractOfDispatcherWithMapping dispatcher) fn
      reservedNames n0 cases' body' bodyNative bodyStart bodyEnd
      userBodyStart hLowerRuntime hFind hCase hBodyLower hUserBodyLower)

/-- Package direct selected-body execution with the mapping-helper straight-body
preservation closure into the unified selected-body result bridge. -/
theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_exec_only_and_bridgedStraightStmts_mapping
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) (irContract : IRContract) (tx : IRTransaction)
    (state : IRState) (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hExec : NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived irContract tx state observableSlots)
    (hMapping : irContract.usesMapping = true)
    (hBodyStraight : ∀ fn,
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      Compiler.Proofs.YulGeneration.Backends.BridgedStraightStmts fn.body)
    (hSide : ∀ fn,
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      ∀ stmt, stmt ∈ fn.body →
        Compiler.Proofs.YulGeneration.Backends.Native.NativePreservableSideConditionForBridgedStraightStmt stmt)
    (hFresh : ∀ (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
        (reservedNames : List String) (n0 : Nat) (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
        (body' bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd userBodyStart : Nat),
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract →
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn →
      cases'.find? (fun entry => entry.1 == tx.functionSelector) = some (tx.functionSelector, body') →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) = .ok (body', bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds reservedNames userBodyStart
        fn.body = .ok (bodyNative, bodyEnd) →
      Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0) ∉
      Compiler.Proofs.YulGeneration.Backends.nativeStmtsWriteNames bodyNative) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_exec_only_and_preserves
    irContract tx state observableSlots hExec
    (NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel.of_bridgedStraightStmts_mapping
      spec selectors hSupported irContract tx hcompile hMapping hBodyStraight hSide hFresh)

/-- The generated `revert(0,0)` guard body cannot produce a normal `.ok`
state, so it vacuously preserves any dispatcher marker on successful
execution. -/
private theorem NativeBlockPreservesWord_nativeRevertZeroZero
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord
      name value
      [Compiler.Proofs.YulGeneration.Backends.Native.nativeRevertZeroZeroStmt]
      codeOverride := by
  refine
    Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord_singleton
      name value
      Compiler.Proofs.YulGeneration.Backends.Native.nativeRevertZeroZeroStmt
      codeOverride ?_
  simp only [Compiler.Proofs.YulGeneration.Backends.Native.nativeRevertZeroZeroStmt]
  exact
    Compiler.Proofs.YulGeneration.Backends.Native.NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves
      name value EvmYul.Operation.REVERT
      [EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 0),
       EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 0)]
      codeOverride
      (Compiler.Proofs.YulGeneration.Backends.Native.NativeEvalArgsPreservesWord_cons
        name value (EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 0))
        [EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 0)] codeOverride
        (Compiler.Proofs.YulGeneration.Backends.Native.NativeExprPreservesWord_lit
          name value (EvmYul.UInt256.ofNat 0) codeOverride)
        (Compiler.Proofs.YulGeneration.Backends.Native.NativeEvalArgsPreservesWord_cons
          name value (EvmYul.Yul.Ast.Expr.Lit (EvmYul.UInt256.ofNat 0))
          [] codeOverride
          (Compiler.Proofs.YulGeneration.Backends.Native.NativeExprPreservesWord_lit
            name value (EvmYul.UInt256.ofNat 0) codeOverride)
          (Compiler.Proofs.YulGeneration.Backends.Native.NativeEvalArgsPreservesWord_nil
            name value codeOverride)))
      (by
        exact
          Compiler.Proofs.YulGeneration.Backends.Native.NativePrimCallPreservesWord_revert_values
            name value)

private theorem NativeExprPreservesWord_lowerExprNative_callvalue_any
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    Compiler.Proofs.YulGeneration.Backends.Native.NativeExprPreservesWord
      name value
      (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Compiler.Yul.YulExpr.call "callvalue" []))
      codeOverride := by
  exact
    Compiler.Proofs.YulGeneration.Backends.Native.NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
      name "callvalue" value [] EvmYul.Operation.CALLVALUE codeOverride
      Compiler.Proofs.YulGeneration.Backends.lookupRuntimePrimOp_callvalue
      (Compiler.Proofs.YulGeneration.Backends.Native.NativeEvalArgsPreservesWord_nil
        name value codeOverride)
      (Compiler.Proofs.YulGeneration.Backends.Native.NativePrimCallPreservesWord_callvalue_values
        name value)

private theorem NativeExprPreservesWord_lowerExprNative_lt_calldatasize_lit_any
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (k : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    Compiler.Proofs.YulGeneration.Backends.Native.NativeExprPreservesWord
      name value
      (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Compiler.Yul.YulExpr.call "lt"
          [Compiler.Yul.YulExpr.call "calldatasize" [],
           Compiler.Yul.YulExpr.lit k]))
      codeOverride := by
  exact
    Compiler.Proofs.YulGeneration.Backends.Native.NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
      name "lt" value
      [Compiler.Yul.YulExpr.call "calldatasize" [], Compiler.Yul.YulExpr.lit k]
      EvmYul.Operation.LT codeOverride
      Compiler.Proofs.YulGeneration.Backends.lookupRuntimePrimOp_lt
      (Compiler.Proofs.YulGeneration.Backends.Native.NativeEvalArgsPreservesWord_map_lowerExprNative_reverse
        name value
        [Compiler.Yul.YulExpr.call "calldatasize" [], Compiler.Yul.YulExpr.lit k]
        codeOverride
        (by
          intro arg hArg
          simp at hArg
          rcases hArg with hArg | hArg
          · subst arg
            exact
              Compiler.Proofs.YulGeneration.Backends.Native.NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
                name "calldatasize" value [] EvmYul.Operation.CALLDATASIZE
                codeOverride
                Compiler.Proofs.YulGeneration.Backends.lookupRuntimePrimOp_calldatasize
                (Compiler.Proofs.YulGeneration.Backends.Native.NativeEvalArgsPreservesWord_nil
                  name value codeOverride)
                (Compiler.Proofs.YulGeneration.Backends.Native.NativePrimCallPreservesWord_calldatasize_values
                  name value)
          · subst arg
            exact
              Compiler.Proofs.YulGeneration.Backends.Native.NativeExprPreservesWord_lowerExprNative_lit
                name value k codeOverride))
      (Compiler.Proofs.YulGeneration.Backends.Native.NativePrimCallPreservesWord_lt_values
        name value)

/-- Matched-flag preservation for a lowered payable `switchCaseBody` prefix
followed by a preserved user body. -/
private theorem NativeBlockPreservesWord_switchCaseBody_payable_revert_cons
    (name : String) (value : EvmYul.UInt256) (minSize : Nat)
    (bodyNative : List EvmYul.Yul.Ast.Stmt)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hUserPreserves :
      Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord
        name value bodyNative (some nativeContract)) :
    Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord
      name value
      (EvmYul.Yul.Ast.Stmt.Block [] ::
        EvmYul.Yul.Ast.Stmt.If
          (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
            (Compiler.Yul.YulExpr.call "lt"
              [Compiler.Yul.YulExpr.call "calldatasize" [],
               Compiler.Yul.YulExpr.lit minSize]))
          [Compiler.Proofs.YulGeneration.Backends.Native.nativeRevertZeroZeroStmt] ::
        bodyNative)
      (some nativeContract) := by
  refine
    Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord_cons_stmt
      _ _ (.Block []) _ _ ?_ ?_
  · exact
      Compiler.Proofs.YulGeneration.Backends.Native.NativeStmtPreservesWord_block
        _ _ [] _ (Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord_nil _ _ _)
  · refine
      Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord_cons_stmt
        _ _ _ _ _ ?_ hUserPreserves
    exact
      Compiler.Proofs.YulGeneration.Backends.Native.NativeStmtPreservesWord_if_of_cond_preserves
        _ _ _ _ _
        (NativeExprPreservesWord_lowerExprNative_lt_calldatasize_lit_any _ _ minSize _)
        (NativeBlockPreservesWord_nativeRevertZeroZero _ _ _)

/-- Lift matched-flag preservation from a direct lowered selected user body to
the whole generated payable `switchCaseBody` wrapper. -/
private theorem NativeBlockPreservesWord_switchCaseBody_payable_of_user_body
    (fn : IRFunction) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (reservedNames : List String) (switchStart : Nat)
    (body' guardBody bodyNative : List EvmYul.Yul.Ast.Stmt)
    (bodyStart bodyEnd : Nat) (hPayable : fn.payable = true)
    (hBodyLower :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
          .ok (body', bodyEnd))
    (hBodyShape :
      body' =
        EvmYul.Yul.Ast.Stmt.Block [] ::
        EvmYul.Yul.Ast.Stmt.If
          (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
            (Compiler.Yul.YulExpr.call "lt"
              [Compiler.Yul.YulExpr.call "calldatasize" [],
               Compiler.Yul.YulExpr.lit (4 + fn.params.length * 32)]))
          guardBody ::
        bodyNative)
    (hUserPreserves :
      Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord
        (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
          reservedNames switchStart))
        (EvmYul.UInt256.ofNat 1) bodyNative (some nativeContract)) :
    Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord
        (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
          reservedNames switchStart))
      (EvmYul.UInt256.ofNat 1) body' (some nativeContract) := by
  rcases
    Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hPayable hBodyLower with
    ⟨bodyNative', _userBodyStart', hShape, _hUserBodyLower'⟩
  have hBodyNativeEq : bodyNative = bodyNative' := by
    rw [hShape] at hBodyShape; simp at hBodyShape; exact hBodyShape.2.symm
  subst bodyNative'
  rw [hShape]
  exact
    NativeBlockPreservesWord_switchCaseBody_payable_revert_cons _ _ _ _ _
      hUserPreserves

/-- Matched-flag preservation for a lowered non-payable `switchCaseBody` prefix
followed by a preserved user body. -/
private theorem NativeBlockPreservesWord_switchCaseBody_nonpayable_revert_cons
    (name : String) (value : EvmYul.UInt256) (minSize : Nat)
    (bodyNative : List EvmYul.Yul.Ast.Stmt)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hUserPreserves :
      Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord
        name value bodyNative (some nativeContract)) :
    Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord
      name value
      (EvmYul.Yul.Ast.Stmt.Block [] ::
        EvmYul.Yul.Ast.Stmt.If
          (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
            (Compiler.Yul.YulExpr.call "callvalue" []))
          [Compiler.Proofs.YulGeneration.Backends.Native.nativeRevertZeroZeroStmt] ::
        EvmYul.Yul.Ast.Stmt.If
          (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
            (Compiler.Yul.YulExpr.call "lt"
              [Compiler.Yul.YulExpr.call "calldatasize" [],
               Compiler.Yul.YulExpr.lit minSize]))
          [Compiler.Proofs.YulGeneration.Backends.Native.nativeRevertZeroZeroStmt] ::
        bodyNative)
      (some nativeContract) := by
  refine
    Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord_cons_stmt
      _ _ (.Block []) _ _
      (Compiler.Proofs.YulGeneration.Backends.Native.NativeStmtPreservesWord_block
        _ _ [] _ (Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord_nil _ _ _))
      ?_
  refine
    Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord_cons_stmt
      _ _ _ _ _
      (Compiler.Proofs.YulGeneration.Backends.Native.NativeStmtPreservesWord_if_of_cond_preserves
        _ _ _ _ _ (NativeExprPreservesWord_lowerExprNative_callvalue_any _ _ _)
        (NativeBlockPreservesWord_nativeRevertZeroZero _ _ _))
      ?_
  exact
    Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord_cons_stmt
      _ _ _ _ _
      (Compiler.Proofs.YulGeneration.Backends.Native.NativeStmtPreservesWord_if_of_cond_preserves
        _ _ _ _ _
        (NativeExprPreservesWord_lowerExprNative_lt_calldatasize_lit_any _ _ minSize _)
        (NativeBlockPreservesWord_nativeRevertZeroZero _ _ _))
      hUserPreserves

/-- Lift matched-flag preservation from a direct lowered selected user body to
the whole generated non-payable `switchCaseBody` wrapper. -/
private theorem NativeBlockPreservesWord_switchCaseBody_nonpayable_of_user_body
    (fn : IRFunction) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (reservedNames : List String) (switchStart : Nat)
    (body' callvalueGuardBody calldataGuardBody bodyNative :
      List EvmYul.Yul.Ast.Stmt)
    (bodyStart bodyEnd : Nat) (hNonPayable : fn.payable = false)
    (hBodyLower :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames bodyStart
        (Compiler.Proofs.YulGeneration.Backends.Native.switchCaseBody fn) =
          .ok (body', bodyEnd))
    (hBodyShape :
      body' =
        EvmYul.Yul.Ast.Stmt.Block [] ::
        EvmYul.Yul.Ast.Stmt.If
          (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
            (Compiler.Yul.YulExpr.call "callvalue" []))
          callvalueGuardBody ::
        EvmYul.Yul.Ast.Stmt.If
          (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
            (Compiler.Yul.YulExpr.call "lt"
              [Compiler.Yul.YulExpr.call "calldatasize" [],
               Compiler.Yul.YulExpr.lit (4 + fn.params.length * 32)]))
          calldataGuardBody ::
        bodyNative)
    (hUserPreserves :
      Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord
        (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
            reservedNames switchStart))
        (EvmYul.UInt256.ofNat 1) bodyNative (some nativeContract)) :
    Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord
      (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
          reservedNames switchStart))
      (EvmYul.UInt256.ofNat 1) body' (some nativeContract) := by
  rcases
    Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_revert_eq
      reservedNames bodyStart fn body' bodyEnd hNonPayable hBodyLower with
    ⟨bodyNative', _userBodyStart', hShape, _hUserBodyLower'⟩
  have hBodyNativeEq : bodyNative = bodyNative' := by
    rw [hShape] at hBodyShape; simp at hBodyShape; exact hBodyShape.2.2.symm
  subst bodyNative'
  rw [hShape]
  exact
    NativeBlockPreservesWord_switchCaseBody_nonpayable_revert_cons _ _ _ _ _
      hUserPreserves

/-- Recombine the factored selected user-body execution and preservation
bridges into the existing all-in-one bridge consumed by the dispatcher stack. -/
private theorem NativeGeneratedSelectorHitUserBodyExecBridgeAtFuelRevived.of_exec_only_and_preserves
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hExec :
      NativeGeneratedSelectorHitUserBodyExecOnlyBridgeAtFuelRevived
        irContract tx state observableSlots)
    (hPreserves :
      NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel irContract tx) :
    NativeGeneratedSelectorHitUserBodyExecBridgeAtFuelRevived irContract tx
      state observableSlots := by
  intro nativeContract fn reservedNames n0 cases' body' bodyNative bodyStart
    bodyEnd userBodyStart hLowerRuntime hFind hCase hBodyLower hUserBodyLower
    hguards hArgs
  rcases hExec nativeContract fn reservedNames n0 cases' body' bodyNative
      bodyStart bodyEnd userBodyStart hLowerRuntime hFind hCase hBodyLower
      hUserBodyLower hguards hArgs with
    ⟨final, nativeYul, shared, store, hBody, hRevive, hProject, hMatch⟩
  refine ⟨final, nativeYul, shared, store, hBody, ?_, hRevive, hProject,
    hMatch⟩
  intro pre suffix hCases
  exact
    hPreserves nativeContract fn reservedNames n0 cases' body' bodyNative
      bodyStart bodyEnd userBodyStart hLowerRuntime hFind hCase hBodyLower
      hUserBodyLower pre suffix hCases

/-- Empty selected user bodies preserve the generated matched flag. -/
private theorem NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel.of_empty_body
    (irContract : IRContract)
    (tx : IRTransaction)
    (hEmpty :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = []) :
    NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel irContract tx := by
  intro nativeContract fn reservedNames n0 cases' body' bodyNative bodyStart
    bodyEnd userBodyStart _hLowerRuntime hFind _hCase _hBodyLower
    hUserBodyLower _pre _suffix _hCases
  have hBody : fn.body = [] := hEmpty fn hFind
  simp [hBody] at hUserBodyLower
  rcases hUserBodyLower with ⟨rfl, _rfl⟩
  exact
    Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord_nil
      (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
          reservedNames n0))
      (EvmYul.UInt256.ofNat 1) (some nativeContract)

/-- Empty selected user bodies discharge the unified selected-body result
boundary. -/
theorem NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_empty_body
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hEmpty :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        fn.body = []) :
    NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
      observableSlots :=
  NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_exec_only_and_preserves
    irContract tx state observableSlots
    (NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived.of_empty_body
      irContract tx state observableSlots hEmpty)
    (NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel.of_empty_body
      irContract tx hEmpty)

/-- Projecting a restored call frame over `initialState` agrees with projecting
`final.reviveJump` directly whenever `final.reviveJump` is `Ok`. -/
private theorem projectResult_restoreCallFrame_initialState_eq_of_reviveJump_ok
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (final : EvmYul.Yul.State) (nativeYul : YulResult)
    (shared store)
    (hRevive : final.reviveJump = EvmYul.Yul.State.Ok shared store)
    (hProject :
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events
        (.ok (final.reviveJump, [])) = nativeYul) :
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      (YulTransaction.ofIR tx) state.storage state.events
      (.ok
        (((final.reviveJump.overwrite?
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            nativeContract (YulTransaction.ofIR tx) state.storage
            (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
              (Compiler.runtimeCode irContract) observableSlots))).setStore
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            nativeContract (YulTransaction.ofIR tx) state.storage
            (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
              (Compiler.runtimeCode irContract) observableSlots))), [])) =
      nativeYul := by
  have hInitialOk :
      ∃ initialShared initialStore,
        Compiler.Proofs.YulGeneration.Backends.Native.initialState
          nativeContract (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode irContract) observableSlots) =
          EvmYul.Yul.State.Ok initialShared initialStore := by
    simp [Compiler.Proofs.YulGeneration.Backends.Native.initialState]
  exact
    (Compiler.Proofs.YulGeneration.Backends.Native.projectResult_ok_restoreCallFrame_of_reviveJump_ok
      (YulTransaction.ofIR tx) state.storage state.events final
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        nativeContract (YulTransaction.ofIR tx) state.storage
        (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
          (Compiler.runtimeCode irContract) observableSlots))
      [] shared store hRevive hInitialOk).trans hProject

/-- Generic matched-flag preservation for a selected generated selector-hit
body.

The native switch proof only needs block preservation of the matched flag for
the selected case body. This theorem derives that block preservation from the
native switch freshness predicate plus per-statement preservation for statements
that do not write the matched flag. -/
theorem nativeGeneratedSelectorHitBodyPreservesMatched_of_fresh
    (tx : IRTransaction)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (body' : List EvmYul.Yul.Ast.Stmt)
    (hCase :
      cases'.find? (fun entry => entry.1 == tx.functionSelector) =
        some (tx.functionSelector, body'))
    (hFresh :
      Compiler.Proofs.YulGeneration.Backends.nativeSwitchTempsFreshForNativeBodies
        (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
          reservedNames n0)
        cases'
        [Compiler.Proofs.YulGeneration.Backends.Native.nativeRevertZeroZeroStmt])
    (hStmtPreserves :
      ∀ stmt, stmt ∈ body' →
        Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
            (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
              reservedNames n0) ∉
          Compiler.Proofs.YulGeneration.Backends.nativeStmtWriteNames stmt →
        Compiler.Proofs.YulGeneration.Backends.Native.NativeStmtPreservesWord
          (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
            (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
              reservedNames n0))
          (EvmYul.UInt256.ofNat 1) stmt (some nativeContract)) :
    ∀ pre suffix,
      cases' = pre ++ (tx.functionSelector, body') :: suffix →
      Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord
        (Compiler.Proofs.YulGeneration.Backends.nativeSwitchMatchedTempName
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
            reservedNames n0))
        (EvmYul.UInt256.ofNat 1) body' (some nativeContract) := by
  intro _pre _suffix _hCases
  exact
    Compiler.Proofs.YulGeneration.Backends.Native.NativeBlockPreservesWord_of_nativeSwitchFresh_find_hit_matched
      (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId
        reservedNames n0)
      tx.functionSelector tx.functionSelector body'
      [Compiler.Proofs.YulGeneration.Backends.Native.nativeRevertZeroZeroStmt]
      cases' (EvmYul.UInt256.ofNat 1) (some nativeContract)
      hFresh hCase hStmtPreserves

/-- Value-safe selector-hit case split under an explicit calldata threshold. -/
private theorem nativeGeneratedSelectorHit_of_value_safe_and_success_predicate_threshold
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hLowerRuntime :
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind :
      irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
        some fn)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThresholdFn : 4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (hSuccess :
      NativeGeneratedSelectorHitSuccessBridge irContract tx state observableSlots)
    (hValue :
      fn.payable = true ∨ tx.msgValue % Compiler.Constants.evmModulus = 0) :
    nativeResultsMatchOn observableSlots (interpretIR irContract tx state)
      (nativeGeneratedCallDispatcherResultOf irContract tx state
        observableSlots nativeContract) := by
  by_cases hArgs : fn.params.length ≤ tx.args.length
  · exact hSuccess nativeContract fn hLowerRuntime hFind
      (DispatchGuardsSafe.of_value_safe_of_args_le_of_noWrap
        fn tx hValue hArgs hNoWrap) hArgs
  · exact
      nativeGeneratedCallDispatcherResult_selector_hit_args_short_revert_matchesIR_of_compile_ok_supported
        spec selectors hSupported irContract tx state observableSlots
        nativeContract fn hcompile hLowerRuntime hFind hSelectorRange
        hSelectorsRange hNoWrap
        (DispatchGuardsSafe.of_value_safe_of_threshold fn tx hValue hThresholdFn)
        hValue hArgs

/-- Build the selector-hit bridge from a success-only bridge plus generated
guard-revert theorems, requiring only the generated calldata-threshold bound.

The success branch reconstructs `DispatchGuardsSafe` from the concrete value
and argument checks plus the transaction no-wrap fact. The short-calldata
branch reconstructs it from value safety plus the explicit selected-function
threshold, avoiding a public nonpayable/value guard premise for callers that
only need the generated guard split. -/
private theorem NativeGeneratedSelectorHitBridge.of_success_predicate_and_generated_guard_reverts_threshold
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (hSuccess :
      NativeGeneratedSelectorHitSuccessBridge irContract tx state
        observableSlots) :
    NativeGeneratedSelectorHitBridge spec selectors irContract tx state
      observableSlots := by
  intro nativeContract fn hLowerRuntime hFind
  by_cases hPayable : fn.payable = true
  · exact
      nativeGeneratedSelectorHit_of_value_safe_and_success_predicate_threshold
        spec selectors hSupported irContract tx state observableSlots
        nativeContract fn hcompile hLowerRuntime hFind hSelectorRange
        hSelectorsRange hNoWrap (hThreshold fn hFind) hSuccess (Or.inl hPayable)
  · by_cases hZero : tx.msgValue % Compiler.Constants.evmModulus = 0
    · exact
        nativeGeneratedSelectorHit_of_value_safe_and_success_predicate_threshold
          spec selectors hSupported irContract tx state observableSlots
          nativeContract fn hcompile hLowerRuntime hFind hSelectorRange
          hSelectorsRange hNoWrap (hThreshold fn hFind) hSuccess (Or.inr hZero)
    · exact
        nativeGeneratedCallDispatcherResult_selector_hit_nonpayable_nonzero_revert_matchesIR_of_compile_ok_supported
          spec selectors hSupported irContract tx state observableSlots
          nativeContract fn hcompile hLowerRuntime hFind hSelectorRange
          hSelectorsRange hNoWrap (Bool.eq_false_iff.2 hPayable) hZero

/-- Generated `callDispatcher` result theorem from `SupportedSpec + compile`,
modulo the remaining selector-hit body bridge.

This composes the completed generated lowering and selector-miss proof with a
single selector-hit bridge premise. The premise is intentionally narrow: it is
exactly what the future native function-body correctness theorem must supply. -/
private theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selector_hit_bridge
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hHitBridge :
      NativeGeneratedSelectorHitBridge spec selectors irContract tx state
        observableSlots) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  rcases lowerRuntimeContractNative_of_compile_ok_supported_exists
      hcompile hSupported with
    ⟨nativeContract, hLowerRuntime⟩
  cases hFind :
      irContract.functions.find?
        (fun fn => fn.selector == tx.functionSelector) with
  | none =>
      exact ⟨nativeContract, hLowerRuntime,
        nativeGeneratedCallDispatcherResult_selector_miss_matchesIR_of_compile_ok_supported
          spec selectors hSupported irContract tx state observableSlots
          nativeContract hcompile hLowerRuntime hFind hSelectorRange
          hSelectorsRange hNoWrap⟩
  | some fn =>
      exact ⟨nativeContract, hLowerRuntime,
        hHitBridge nativeContract fn hLowerRuntime hFind⟩

/-- Generated `callDispatcher` result theorem from `SupportedSpec + compile`,
modulo the remaining success-only selector-hit bridge and only an explicit
generated calldata-threshold bound.

Selector miss, non-payable value guard failure, and calldata-size guard failure
are closed generically. Compared with
`nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selector_hit_success_bridge`,
this wrapper avoids exposing full `DispatchGuardsSafe` outside the success
branch. -/
private theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selector_hit_success_bridge_threshold
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size)
    (hSuccess :
      NativeGeneratedSelectorHitSuccessBridge irContract tx state
        observableSlots) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  exact
    nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selector_hit_bridge
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap
      (NativeGeneratedSelectorHitBridge.of_success_predicate_and_generated_guard_reverts_threshold
        spec selectors hSupported irContract tx state observableSlots hcompile
        hSelectorRange hSelectorsRange hNoWrap hThreshold hSuccess)

/-- Lowered runtime switch cases have length at most `nativeRuntimeDispatcherFuel irContract - 24`. -/
private theorem nativeRuntimeDispatcherFuel_ge_cases_length_plus24
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {reservedNames : List String} {n0 : Nat}
    {cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)} {midN : Nat}
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hLowerCases :
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
        reservedNames (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0 + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases irContract.functions) =
          .ok (cases', midN)) :
    cases'.length + 24 ≤ nativeRuntimeDispatcherFuel irContract := by
  dsimp [nativeRuntimeDispatcherFuel]
  by_cases hUsesMapping : irContract.usesMapping
  · exact sizeOf_emitYul_runtimeCode_mapping_ge_lowered_cases_length_plus24
      hcompile hSupported (by simpa using hUsesMapping) hLowerCases
  · exact sizeOf_emitYul_runtimeCode_noMapping_ge_lowered_cases_length_plus24
      hcompile hSupported (Bool.eq_false_iff.2 hUsesMapping) hLowerCases

/-- Lowered runtime switch cases have length at most `nativeRuntimeDispatcherFuel irContract - 25`. -/
private theorem nativeRuntimeDispatcherFuel_ge_cases_length_plus25
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract} {reservedNames : List String} {n0 : Nat}
    {cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)} {midN : Nat}
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hLowerCases :
      Compiler.Proofs.YulGeneration.Backends.lowerSwitchCasesNativeWithSwitchIds
        reservedNames (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0 + 1)
        (Compiler.Proofs.YulGeneration.Backends.Native.buildSwitchSourceCases irContract.functions) =
          .ok (cases', midN)) :
    cases'.length + 25 ≤ nativeRuntimeDispatcherFuel irContract := by
  dsimp [nativeRuntimeDispatcherFuel]
  by_cases hUsesMapping : irContract.usesMapping
  · exact sizeOf_emitYul_runtimeCode_mapping_ge_lowered_cases_length_plus25
      hcompile hSupported (by simpa using hUsesMapping) hLowerCases
  · exact sizeOf_emitYul_runtimeCode_noMapping_ge_lowered_cases_length_plus25
      hcompile hSupported (Bool.eq_false_iff.2 hUsesMapping) hLowerCases

/-- Executing a payable lowered `switchCaseBody` reduces to executing the lowered user body
when the calldata guard succeeds. -/
private theorem exec_switchCaseBody_payable_of_userBody_exec
    (irContract : IRContract) (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction) (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (body' guardBody bodyNative : List EvmYul.Yul.Ast.Stmt)
    (final : EvmYul.Yul.State) (hPayable : fn.payable = true)
    (hFuelBound24 : cases'.length + 24 ≤ nativeRuntimeDispatcherFuel irContract)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length)
    (hBodyShape : body' = EvmYul.Yul.Ast.Stmt.Block [] ::
      EvmYul.Yul.Ast.Stmt.If (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Yul.YulExpr.call "lt" [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit (4 + fn.params.length * 32)]))
        guardBody :: bodyNative)
    (hBody : ∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
      EvmYul.Yul.exec (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' + suffix.length + 10) (.Block bodyNative) (some nativeContract)
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId nativeContract (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots (Compiler.runtimeCode irContract) observableSlots)
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0) Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) = .ok final) :
    ∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
      EvmYul.Yul.exec (((nativeRuntimeDispatcherFuel irContract - (cases'.length + 20)) + 1) + suffix.length + 7) (.Block body') (some nativeContract)
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId nativeContract (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots (Compiler.runtimeCode irContract) observableSlots)
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0) Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) = .ok final := by
  intro pre suffix hCases; rw [hBodyShape]
  have hPrefix := Compiler.Proofs.YulGeneration.Backends.Native.exec_switchCaseBody_payable_prefix_postInitFreeMemory_eq
    (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' + suffix.length + 1) guardBody bodyNative nativeContract (YulTransaction.ofIR tx) state.storage
    (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots (Compiler.runtimeCode irContract) observableSlots)
    (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0)
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore (4 + fn.params.length * 32)
    (by simpa [YulTransaction.ofIR_args] using hNoWrap)
    (Compiler.Proofs.YulGeneration.Backends.Native.DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
    (Nat.add_le_add_left (Nat.mul_le_mul_right 32 hArgs) 4)
  have hFuelEq : suffix.length + (1 + (11 + (nativeRuntimeDispatcherFuel irContract - (cases'.length + 24)))) =
      suffix.length + (1 + (7 + (nativeRuntimeDispatcherFuel irContract - (cases'.length + 20)))) := by omega
  simpa [nativeGeneratedSelectorHitUserBodyFuel, hPayable, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hFuelEq] using hPrefix.trans (hBody pre suffix hCases)

/-- Executing a nonpayable lowered `switchCaseBody` reduces to executing the lowered user body
when the callvalue and calldata guards succeed. -/
private theorem exec_switchCaseBody_nonpayable_of_userBody_exec
    (irContract : IRContract) (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction) (reservedNames : List String) (n0 : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (body' callvalueGuardBody calldataGuardBody bodyNative : List EvmYul.Yul.Ast.Stmt)
    (final : EvmYul.Yul.State) (hNonPayable : fn.payable = false)
    (hFuelBound25 : cases'.length + 25 ≤ nativeRuntimeDispatcherFuel irContract)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length)
    (hBodyShape : body' = EvmYul.Yul.Ast.Stmt.Block [] ::
      EvmYul.Yul.Ast.Stmt.If (Compiler.Proofs.YulGeneration.Backends.lowerExprNative (Yul.YulExpr.call "callvalue" [])) callvalueGuardBody ::
      EvmYul.Yul.Ast.Stmt.If (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Yul.YulExpr.call "lt" [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit (4 + fn.params.length * 32)]))
        calldataGuardBody :: bodyNative)
    (hBody : ∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
      EvmYul.Yul.exec (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' + suffix.length + 10) (.Block bodyNative) (some nativeContract)
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId nativeContract (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots (Compiler.runtimeCode irContract) observableSlots)
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0) Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) = .ok final) :
    ∀ pre suffix, cases' = pre ++ (tx.functionSelector, body') :: suffix →
      EvmYul.Yul.exec (((nativeRuntimeDispatcherFuel irContract - (cases'.length + 20)) + 1) + suffix.length + 7) (.Block body') (some nativeContract)
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchPostInitFreeMemoryStoreMarkedPrefixStateForId nativeContract (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots (Compiler.runtimeCode irContract) observableSlots)
          (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0) Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore) = .ok final := by
  intro pre suffix hCases; rw [hBodyShape]
  have hPrefix := Compiler.Proofs.YulGeneration.Backends.Native.exec_switchCaseBody_nonpayable_prefix_postInitFreeMemory_eq
    (nativeGeneratedSelectorHitUserBodyFuel irContract fn cases' + suffix.length + 1) callvalueGuardBody calldataGuardBody bodyNative nativeContract (YulTransaction.ofIR tx) state.storage
    (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots (Compiler.runtimeCode irContract) observableSlots)
    (Compiler.Proofs.YulGeneration.Backends.freshNativeSwitchId reservedNames n0)
    Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchHasSelectorStore (4 + fn.params.length * 32)
    (Compiler.Proofs.YulGeneration.Backends.Native.DispatchGuardsSafe_msgValue_zero_mod_of_nonpayable fn tx hguards hNonPayable)
    (by simpa [YulTransaction.ofIR_args] using hNoWrap)
    (Compiler.Proofs.YulGeneration.Backends.Native.DispatchGuardsSafe_calldata_threshold_lt fn tx hguards)
    (Nat.add_le_add_left (Nat.mul_le_mul_right 32 hArgs) 4)
  have hFuelEq : suffix.length + (1 + (12 + (nativeRuntimeDispatcherFuel irContract - (cases'.length + 25)))) =
      suffix.length + (1 + (7 + (nativeRuntimeDispatcherFuel irContract - (cases'.length + 20)))) := by omega
  simpa [nativeGeneratedSelectorHitUserBodyFuel, hNonPayable, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hFuelEq] using hPrefix.trans (hBody pre suffix hCases)

/-- Success-only selector-hit adapter from the exact-fuel user-body execution
bridge, using the generated dispatcher continuation directly.

The selected body proof first chooses the normal `final/nativeYul` result; the
polymorphic generated success theorem then accepts that result in its
continuation. -/
private theorem nativeGeneratedSelectorHit_success_of_user_body_exec_bridge_atFuel_revived
    (spec : CompilationModel.CompilationModel) (selectors : List Nat) (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract) (tx : IRTransaction) (state : IRState) (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hUserBodyBridge : NativeGeneratedSelectorHitUserBodyExecBridgeAtFuelRevived irContract tx state observableSlots)
    (nativeContract : EvmYul.Yul.Ast.YulContract) (fn : IRFunction)
    (hLowerRuntime : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative (Compiler.emitYul irContract).runtimeCode = .ok nativeContract)
    (hFind : irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) = some fn)
    (hguards : DispatchGuardsSafe fn tx) (hArgs : fn.params.length ≤ tx.args.length) :
    nativeResultsMatchOn observableSlots (interpretIR irContract tx state)
      (nativeGeneratedCallDispatcherResultOf irContract tx state observableSlots nativeContract) := by
  rcases nativeGeneratedCallDispatcherResult_selector_hit_ok_matchesIR_forall_of_compile_ok_supported
      spec selectors hSupported irContract tx state observableSlots nativeContract fn hcompile hLowerRuntime
      hFind hSelectorRange hSelectorsRange hNoWrap with
    ⟨reservedNames, n0, cases', _midN, body', bodyStart, bodyEnd, hLowerCases, hCase, hBodyLower, hCaseCont⟩
  by_cases hPayable : fn.payable
  · rcases Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_eq
        reservedNames bodyStart fn body' bodyEnd (by simpa using hPayable) hBodyLower with
      ⟨guardBody, bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
    rcases hUserBodyBridge nativeContract fn reservedNames n0 cases' body' bodyNative bodyStart bodyEnd
        userBodyStart hLowerRuntime hFind hCase hBodyLower hUserBodyLower hguards hArgs with
      ⟨final, nativeYul, shared, store, hBody, hPreserves, hRevive, hProject, hMatchExec⟩
    exact hCaseCont final nativeYul
      (exec_switchCaseBody_payable_of_userBody_exec irContract tx state observableSlots nativeContract fn reservedNames n0 cases' body' guardBody bodyNative final (by simpa using hPayable) (nativeRuntimeDispatcherFuel_ge_cases_length_plus24 hcompile hSupported hLowerCases) hNoWrap hguards hArgs hBodyShape hBody)
      (fun pre suffix hCases => NativeBlockPreservesWord_switchCaseBody_payable_of_user_body fn nativeContract reservedNames n0 body' guardBody bodyNative bodyStart bodyEnd (by simpa using hPayable) hBodyLower hBodyShape (hPreserves pre suffix hCases))
      (projectResult_restoreCallFrame_initialState_eq_of_reviveJump_ok irContract tx state observableSlots nativeContract final nativeYul shared store hRevive hProject)
      (nativeResultsMatchOn_interpretIR_of_execIRFunction_dispatchGuards irContract tx state observableSlots fn (.ok nativeYul) hFind hguards hArgs hMatchExec)
  · have hNonPayable : fn.payable = false := Bool.eq_false_iff.2 hPayable
    rcases Compiler.Proofs.YulGeneration.Backends.Native.lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_eq
        reservedNames bodyStart fn body' bodyEnd hNonPayable hBodyLower with
      ⟨callvalueGuardBody, calldataGuardBody, bodyNative, userBodyStart, hBodyShape, hUserBodyLower⟩
    rcases hUserBodyBridge nativeContract fn reservedNames n0 cases' body' bodyNative bodyStart bodyEnd
        userBodyStart hLowerRuntime hFind hCase hBodyLower hUserBodyLower hguards hArgs with
      ⟨final, nativeYul, shared, store, hBody, hPreserves, hRevive, hProject, hMatchExec⟩
    exact hCaseCont final nativeYul
      (exec_switchCaseBody_nonpayable_of_userBody_exec irContract tx state observableSlots nativeContract fn reservedNames n0 cases' body' callvalueGuardBody calldataGuardBody bodyNative final hNonPayable (nativeRuntimeDispatcherFuel_ge_cases_length_plus25 hcompile hSupported hLowerCases) hNoWrap hguards hArgs hBodyShape hBody)
      (fun pre suffix hCases => NativeBlockPreservesWord_switchCaseBody_nonpayable_of_user_body fn nativeContract reservedNames n0 body' callvalueGuardBody calldataGuardBody bodyNative bodyStart bodyEnd hNonPayable hBodyLower hBodyShape (hPreserves pre suffix hCases))
      (projectResult_restoreCallFrame_initialState_eq_of_reviveJump_ok irContract tx state observableSlots nativeContract final nativeYul shared store hRevive hProject)
      (nativeResultsMatchOn_interpretIR_of_execIRFunction_dispatchGuards irContract tx state observableSlots fn (.ok nativeYul) hFind hguards hArgs hMatchExec)

/-- The exact-fuel selected user-body ExecBridge supplies the named
success-only selector-hit bridge. -/
private theorem NativeGeneratedSelectorHitSuccessBridge.of_user_body_exec_bridge_atFuel_revived
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hUserBodyBridge :
      NativeGeneratedSelectorHitUserBodyExecBridgeAtFuelRevived irContract tx
        state observableSlots) :
    NativeGeneratedSelectorHitSuccessBridge irContract tx state
      observableSlots := by
  intro nativeContract fn hLowerRuntime hFind hguards hArgs
  exact
    nativeGeneratedSelectorHit_success_of_user_body_exec_bridge_atFuel_revived
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap hUserBodyBridge nativeContract fn
      hLowerRuntime hFind hguards hArgs

/-- A direct selected-user-body exec-only bridge plus the dispatcher-local
matched-flag preservation bridge supplies the named selector-hit success
bridge.

This is the narrow success-case boundary for the remaining native
function-body theorem: prove direct execution of the lowered `fn.body` against
`execIRFunction`, while preservation can be discharged independently. -/
private theorem NativeGeneratedSelectorHitSuccessBridge.of_selected_user_body_exec_only_and_preserves
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hUserBodyExec :
      NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived irContract tx
        state observableSlots)
    (hUserBodyPreserves :
      NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel irContract tx) :
    NativeGeneratedSelectorHitSuccessBridge irContract tx state
      observableSlots :=
  NativeGeneratedSelectorHitSuccessBridge.of_user_body_exec_bridge_atFuel_revived
    spec selectors hSupported irContract tx state observableSlots hcompile
    hSelectorRange hSelectorsRange hNoWrap
    (NativeGeneratedSelectorHitUserBodyExecBridgeAtFuelRevived.of_exec_only_and_preserves
      irContract tx state observableSlots
      (NativeGeneratedSelectorHitUserBodyExecOnlyBridgeAtFuelRevived.of_selected_user_body_exec_only
        irContract tx state observableSlots hUserBodyExec)
      hUserBodyPreserves)

/-- A unified selected-user-body result bridge supplies the named selector-hit
success bridge.

This is the dispatcher-facing shape for the remaining generic native
function-body theorem: prove either the halt-channel body result or the normal
revived body result plus matched-flag preservation, and the generated prefix
and dispatcher continuation are discharged here. -/
private theorem NativeGeneratedSelectorHitSuccessBridge.of_selected_user_body_result
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hUserBodyResult :
      NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
        observableSlots) :
    NativeGeneratedSelectorHitSuccessBridge irContract tx state
      observableSlots := by
  rcases hUserBodyResult with hSelectedUserBodyHalt |
      ⟨hUserBodyExec, hUserBodyPreserves⟩
  · exact
      NativeGeneratedSelectorHitSuccessBridge.of_selected_user_body_halt_exec_atFuel
        spec selectors hSupported irContract tx state observableSlots hcompile
        hSelectorRange hSelectorsRange hNoWrap hSelectedUserBodyHalt
  · exact
      NativeGeneratedSelectorHitSuccessBridge.of_selected_user_body_exec_only_and_preserves
        spec selectors hSupported irContract tx state observableSlots hcompile
        hSelectorRange hSelectorsRange hNoWrap hUserBodyExec
        hUserBodyPreserves

/-- Generated `callDispatcher` result theorem from `SupportedSpec + compile`,
modulo the unified selected-user-body result bridge and only the generated
calldata-threshold fact needed by the short-calldata guard branch. -/
theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_result_threshold
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hUserBodyResult :
      NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
        observableSlots)
    (hThreshold :
      ∀ fn,
        irContract.functions.find? (fun fn => fn.selector == tx.functionSelector) =
          some fn →
        4 + fn.params.length * 32 < EvmYul.UInt256.size) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul irContract).runtimeCode = .ok nativeContract ∧
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  exact
    nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selector_hit_success_bridge_threshold
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap hThreshold
      (NativeGeneratedSelectorHitSuccessBridge.of_selected_user_body_result
        spec selectors hSupported irContract tx state observableSlots hcompile
        hSelectorRange hSelectorsRange hNoWrap hUserBodyResult)

/-- Public generated `callDispatcher` result theorem from `SupportedSpec +
compile`, modulo the unified exact-fuel selected user-body result bridge.

Selector miss and generated selector-hit guard failures are discharged
internally. Callers provide either the halt-channel selected-body proof or the
normal revived execution plus matched-flag preservation proof through
`NativeGeneratedSelectedUserBodyResultBridgeAtFuel`; the generated prefix,
compiled IR threshold transport, and broad success bridge stay behind private
adapters. -/
theorem nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange :
      ∀ selector, selector ∈ selectors →
        selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hUserBodyResult :
      NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx state
        observableSlots) :
    ∃ nativeContract : EvmYul.Yul.Ast.YulContract,
      nativeResultsMatchOn observableSlots
        (interpretIR irContract tx state)
        (nativeGeneratedCallDispatcherResultOf irContract tx state
          observableSlots nativeContract) := by
  rcases
      nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_result_threshold
      spec selectors hSupported irContract tx state observableSlots hcompile
      hSelectorRange hSelectorsRange hNoWrap
      hUserBodyResult
      (fun fn hFind =>
        generatedFunctionCalldataThreshold_of_compile_ok_supported
          spec selectors hSupported irContract tx hcompile fn hFind) with
    ⟨nativeContract, _hLower, hMatch⟩
  exact ⟨nativeContract, hMatch⟩

/-- Core generated-callDispatcher preservation theorem over the unified
selected-body result bridge.

Callers with halt-ending bodies supply the halt disjunct; callers with
normal-return bodies supply the revived exec-only plus matched-preservation
disjunct. -/
private theorem compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher_via_result
    (spec : CompilationModel.CompilationModel) (selectors : List Nat) (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract) (tx : IRTransaction) (initialWorld : Verity.ContractState) (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (htxNormalized : Function.TxContextNormalized tx) (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hUserBodyResult : NativeGeneratedSelectedUserBodyResultBridgeAtFuel irContract tx (FunctionBody.initialIRStateForTx spec tx initialWorld) observableSlots)
    (hEnv : Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) = .ok ()) :
    sourceResultMatchesNativeOn observableSlots (supportedSourceContractSemantics spec selectors hSupported tx initialWorld)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative (Nat.succ (sizeOf (Compiler.emitYul irContract).runtimeCode))
        irContract tx (FunctionBody.initialIRStateForTx spec tx initialWorld) observableSlots) := by
  rcases nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_result_threshold
      spec selectors hSupported irContract tx (FunctionBody.initialIRStateForTx spec tx initialWorld) observableSlots
      hcompile hSelectorRange hSelectorsRange hNoWrap hUserBodyResult
      (fun fn hFind => generatedFunctionCalldataThreshold_of_compile_ok_supported spec selectors hSupported irContract tx hcompile fn hFind) with
    ⟨nativeContract, hLower, hMatch⟩
  have hEq : nativeGeneratedCallDispatcherResultOf irContract tx (FunctionBody.initialIRStateForTx spec tx initialWorld) observableSlots nativeContract =
      Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative (Nat.succ (sizeOf (Compiler.emitYul irContract).runtimeCode))
        irContract tx (FunctionBody.initialIRStateForTx spec tx initialWorld) observableSlots :=
    callDispatcherResult_eq_nativeRuntime_supported_local tx (FunctionBody.initialIRStateForTx spec tx initialWorld) observableSlots nativeContract hcompile hSupported hLower hEnv
  rw [hEq] at hMatch
  exact sourceResultMatchesNativeOn_of_sourceResultMatchesIRResult_of_nativeResultsMatchOn
    (Compiler.Proofs.IRGeneration.Contract.compile_preserves_semantics spec selectors hSupported irContract tx initialWorld htxNormalized hcalldataSizeFits hcompile) hMatch

theorem compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (observableSlots : List Nat)
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
        (FunctionBody.initialIRStateForTx spec tx initialWorld)
        observableSlots)
    (hEnv :
      Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
        (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) =
          .ok ()) :
    sourceResultMatchesNativeOn observableSlots
      (supportedSourceContractSemantics spec selectors hSupported tx
        initialWorld)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        (Nat.succ (sizeOf (Compiler.emitYul irContract).runtimeCode))
        irContract tx (FunctionBody.initialIRStateForTx spec tx initialWorld)
        observableSlots) := by
  exact
    compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher_via_result
      spec selectors hSupported irContract tx initialWorld observableSlots
      hcompile htxNormalized hcalldataSizeFits hSelectorRange hSelectorsRange
      hNoWrap hUserBodyResult hEnv

attribute [deprecated nativeGeneratedCallDispatcherResultOf (since := "2026-05-07")]
  callDispatcherResult_eq_nativeRuntime_supported_local

end Compiler.Proofs.EndToEnd
