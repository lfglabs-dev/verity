import Compiler.Proofs.IRGeneration.CustomErrorFunctionFuel
import Compiler.Proofs.IRGeneration.CustomErrorConditionalCompilation

namespace Compiler.Proofs.IRGeneration.CustomErrorConditionalFunction
open Compiler.CompilationModel Compiler.Yul SourceSemantics PhysicalSignatureExecution
open CustomErrorFunctionResult

private theorem conditional_budget (pre out : List YulStmt) (cond : YulExpr) :
    sizeOf (pre ++ out) + 2 ≤ sizeOf (pre ++ [.if_ cond out]) := by
  induction pre with
  | nil => simp; omega
  | cons stmt rest ih => simp at *; omega

/-- Actual structural function fuel accounts for both conditional stages. -/
theorem zero_conditional_extra (pre : List YulStmt) (definition : ErrorDef)
    (out : List YulStmt) (cond : YulExpr) (params : definition.params = [])
    (compiled : revertWithCustomError .calldata definition [] [] = .ok out) :
    ∃ extra, sizeOf (pre ++ [.if_ cond out]) + 1 = pre.length +
      (PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 9 := by
  have enough := CustomErrorFunctionFuel.zero_payload_fuel pre definition out params compiled
  have wrapped := conditional_budget pre out cond
  have bound : pre.length + (PhysicalCustomErrorExecution.signaturePrefix
      (bytesFromString (errorSignature definition))).length + 9 ≤
      sizeOf (pre ++ [.if_ cond out]) + 1 := by omega
  obtain ⟨extra, equation⟩ := Nat.exists_eq_add_of_le bound
  exact ⟨extra, by omega⟩

/-- The taken conditional consumes exactly its list and statement stages. -/
theorem conditional_revert (state final : IRState) (cond : YulExpr)
    (out : List YulStmt) (budget : Nat)
    (condition : evalIRExpr state cond = some 1)
    (body : execIRStmts budget state out = .revert final) :
    execIRStmts (budget + 2) state [.if_ cond out] = .revert final := by
  have step : execIRStmt (budget + 1) state (.if_ cond out) = .revert final := by
    simp only [execIRStmt, condition]
    exact body
  simp only [show budget + 2 = (budget + 1) + 1 by omega, execIRStmts, step]

/-- Evaluate a failing Source require at its actual helper-aware condition. -/
theorem source_zero_failure (spec : CompilationModel) (fields : List Field)
    (runtime : RuntimeState) (helperFuel : Nat) (cond : Expr) (name : String) (data : List UInt8)
    (condition : evalExprWithHelpers spec fields helperFuel runtime cond = some 0)
    (payload : execStmt fields runtime (.revertError name []) = .revertWithData data) :
    execStmtListWithHelpers spec fields helperFuel runtime [.requireError cond name []] =
      .revertWithData data := by
  simp only [execStmtListWithHelpers, execStmtWithHelpers, condition]
  simp only [execStmt] at payload
  simp [payload]

/-- Exact Source and physical IR observations of a failing zero-argument error.
The caller supplies condition evaluation and the actual payload compiler receipt. -/
theorem zero_body_failure (spec : CompilationModel) (fields : List Field)
    (runtime : RuntimeState) (state : IRState) (helperFuel extra : Nat)
    (definition : ErrorDef) (cond : Expr) (failCond : YulExpr) (out : List YulStmt)
    (params : definition.params = [])
    (compiled : revertWithCustomError .calldata definition [] [] = .ok out)
    (sourceCond : evalExprWithHelpers spec fields helperFuel runtime cond = some 0)
    (compiledCond : evalIRExpr state failCond = some 1)
    (unique : runtime.errors.filter (·.name == definition.name) = [definition])
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤ Verity.Core.Uint256.modulus) :
    ∃ final data,
      execStmtListWithHelpers spec fields helperFuel runtime [.requireError cond definition.name []] =
        .revertWithData data ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 9)
        state [.if_ failCond out] = .revert final ∧ final.revertBytes = some data := by
  obtain ⟨actual, final, data, payload, executed, captured, source⟩ :=
    PhysicalCustomErrorExecution.compiled_zero_source_bytes .calldata definition params state extra
      fields runtime unique extent
  have same : actual = out := Except.ok.inj (payload.symm.trans compiled)
  subst actual
  refine ⟨final, data, ?_, ?_, captured⟩
  · exact source_zero_failure spec fields runtime helperFuel cond definition.name data sourceCond source
  · simpa only [Nat.add_assoc] using conditional_revert state final failCond out _ compiledCond executed

/-- Concrete failing conditional error through the actual compiler, scalar ABI
loader, helper-aware Source condition, physical bytes and public rollback.
Condition evaluation is an explicit admission certificate, not a body oracle. -/
theorem compiled_zero_failure (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (compiled : IRFunction)
    (definition : ErrorDef) (out : List YulStmt) (bindings : List (String × Nat))
    (oracle : Nat → ExternalCallOutcome) (helperFuel : Nat)
    (fork : Verity.Core.Intrinsics.HardFork) (internals : List FunctionSpec)
    (cond : Expr) (failCond : YulExpr)
    (origin : compileFunctionSpec (effectiveFields spec) spec.events spec.errors spec.adtTypes
      tx.functionSelector fn fork internals = .ok compiled)
    (lookup : spec.errors.find? (·.name == definition.name) = some definition)
    (params : definition.params = [])
    (payloadCompiled : revertWithCustomError .calldata definition [] [] = .ok out)
    (sourceBody : fn.body = [.requireError cond definition.name []])
    (condition : compileRequireFailCondWithInternals (effectiveFields spec) .calldata
      internals cond = .ok failCond)
    (sourceCond : evalExprWithHelpers spec (effectiveFields spec) helperFuel
      { world := withTransactionContext world tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
      cond = some 0)
    (compiledCond : evalIRExpr
      (ParamLoading.applyBindingsToIRState
        (argumentState compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) bindings)
      failCond = some 1)
    (supported : ∀ param ∈ fn.bindingParams, SupportedExternalScalarParamType param.ty)
    (calldataFits : 4 + tx.args.length * 32 < Compiler.Constants.evmModulus)
    (loaded : bindSupportedParams fn.bindingParams tx.args = some bindings)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (unique : spec.errors.filter (·.name == definition.name) = [definition])
    (extent : (world.memory freeMemoryPointer).val +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretFunctionWithHelpers spec helperFuel fn tx world oracle)
      (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) := by
  have shape := CustomErrorConditionalCompilation.compiled_zero_body spec tx.functionSelector fn
    compiled definition cond failCond out fork internals origin sourceBody condition lookup payloadCompiled
  obtain ⟨extra, fuel⟩ := zero_conditional_extra (genParamLoads fn.bindingParams) definition out
    failCond params payloadCompiled
  obtain ⟨final, data, source, executed, captured⟩ := zero_body_failure spec (effectiveFields spec)
    _ _ helperFuel extra definition cond failCond out params payloadCompiled sourceCond compiledCond unique
    (by simpa only [CustomErrorLoadedFunction.bound_argument_memory, FunctionBody.initialIRStateForTx] using extent)
  exact CustomErrorLoadedFunction.loaded_public_error_match spec tx world fn compiled bindings oracle
    helperFuel [.if_ failCond out] _ final data shape supported calldataFits loaded bound
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by simpa only [shape, Nat.add_assoc] using fuel)
    (by simpa only [sourceBody] using source) executed captured

end Compiler.Proofs.IRGeneration.CustomErrorConditionalFunction
