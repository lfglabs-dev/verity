import Compiler.Proofs.IRGeneration.CustomErrorPrefixFrame
import Compiler.Proofs.IRGeneration.FunctionBody.Base
import Verity.Core.Model.PhysicalMemory

namespace Compiler.Proofs.IRGeneration.CustomErrorFunctionEntry
open Compiler.CompilationModel Compiler.Yul SourceSemantics IRMemoryCoherence

/-- The real function carrier retains the world's physical memory. -/
theorem initial_coherent (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (coherent : PhysicalMemory.Coherent world) :
    Coherent (FunctionBody.initialIRStateForTx spec tx world) := by
  unfold Coherent
  intro query
  change (world.memory query).val = _
  simpa only [FunctionBody.initialIRStateForTx] using congrArg Verity.Core.Uint256.val (coherent query)

theorem binding_memory (state : IRState) (bindings : List (String × Nat)) (query : Nat) :
    (ParamLoading.applyBindingsToIRState state bindings).memory query = state.memory query := by
  induction bindings generalizing state with
  | nil => rfl
  | cons binding rest ih =>
      simpa only [ParamLoading.applyBindingsToIRState, IRState.setVar] using
        ih (state.setVar binding.1 binding.2)

theorem binding_coherent (state : IRState) (bindings : List (String × Nat))
    (initial : Coherent state) : Coherent (ParamLoading.applyBindingsToIRState state bindings) := by
  induction bindings generalizing state with
  | nil => exact initial
  | cons binding rest ih =>
      apply ih
      simpa only [Coherent, IRState.setVar] using initial

/-- Actual Source function entry supplies declarations. Parameter binding only
changes variables, so the signature extents come from the retained physical
pointer, with no invented initial-memory contents. -/
theorem entry_domain (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (bindings : List (String × Nat))
    (oracle : Nat → ExternalCallOutcome)
    (coherent : PhysicalMemory.Coherent world)
    (fits : ∀ definition ∈ spec.errors,
      (world.memory freeMemoryPointer).val +
        32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
          Verity.Core.Uint256.modulus) :
    CustomErrorDomain spec
      { world := withTransactionContext world tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
      (ParamLoading.applyBindingsToIRState (FunctionBody.initialIRStateForTx spec tx world) bindings) ∧
    Coherent (ParamLoading.applyBindingsToIRState
      (FunctionBody.initialIRStateForTx spec tx world) bindings) := by
  refine ⟨⟨rfl, ?_⟩, binding_coherent _ bindings (initial_coherent spec tx world coherent)⟩
  intro definition member
  rw [binding_memory]
  exact fits definition member

/-- The real parameter-loader prefix executes to that same admitted entry. -/
theorem loaded_entry (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (params : List Param) (bindings : List (String × Nat))
    (supported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (calldataFits : 4 + tx.args.length * 32 < Compiler.Constants.evmModulus)
    (bound : bindSupportedParams params tx.args = some bindings) :
    execIRStmts ((genParamLoads params).length + 1)
      (FunctionBody.initialIRStateForTx spec tx world) (genParamLoads params) =
      .continue (ParamLoading.applyBindingsToIRState
        (FunctionBody.initialIRStateForTx spec tx world) bindings) := by
  exact ParamLoading.exec_genParamLoads_supported _ params bindings supported calldataFits bound

/-- Preserve an exact terminal body result through the actual ABI loader. -/
theorem loaded_body (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (params : List Param) (bindings : List (String × Nat))
    (body : List YulStmt) (extra : Nat) (result : IRExecResult)
    (supported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (calldataFits : 4 + tx.args.length * 32 < Compiler.Constants.evmModulus)
    (bound : bindSupportedParams params tx.args = some bindings)
    (executed : execIRStmts (body.length + extra + 1)
      (ParamLoading.applyBindingsToIRState
        (FunctionBody.initialIRStateForTx spec tx world) bindings) body = result) :
    execIRStmts ((genParamLoads params).length + body.length + extra + 1)
      (FunctionBody.initialIRStateForTx spec tx world) (genParamLoads params ++ body) = result := by
  have loaded := ParamLoading.exec_genParamLoads_supported_then_extraFuel
    (FunctionBody.initialIRStateForTx spec tx world) params bindings body extra
    supported calldataFits bound
  exact loaded.trans executed

/-- The public helper-aware Source function uses the same declared entry and
preserves actual error bytes while restoring the transaction's initial world. -/
theorem public_source_error (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (bindings : List (String × Nat))
    (oracle : Nat → ExternalCallOutcome) (fuel : Nat) (data : List UInt8)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (executed : execStmtListWithHelpers spec (effectiveFields spec) fuel
      { world := withTransactionContext world tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
      fn.body = .revertWithData data) :
    interpretFunctionWithHelpers spec fuel fn tx world oracle =
      { revertedResult spec (withTransactionContext world tx) with revertData := data } := by
  simp only [interpretFunctionWithHelpers, bound, executed]

end Compiler.Proofs.IRGeneration.CustomErrorFunctionEntry
