import Compiler.CompilationModel.Dispatch
import Compiler.Proofs.IRGeneration.CustomErrorFunctionResult

namespace Compiler.Proofs.IRGeneration.CustomErrorCompilationOrigin
open Compiler.CompilationModel Compiler.Yul Verity.Core.Intrinsics

/-- Real function compilation retains dispatch metadata for any fork, ADT
 table and internal-function table, and exposes the actual ABI-prefixed body. -/
theorem components (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (adts : List AdtTypeDef) (selector : Nat) (fn : FunctionSpec)
    (fork : HardFork) (internals : List FunctionSpec) (compiled : IRFunction)
    (origin : compileFunctionSpec fields events errors adts selector fn fork internals = .ok compiled) :
    ∃ returns body,
      functionReturns fn = .ok returns ∧
      compileStmtListWithFork fields events errors .calldata [] false
        (fn.bindingParams.map (·.name)) adts fork fn.body internals = .ok body ∧
      compiled = {
        name := fn.name, selector := selector,
        params := fn.params.map Param.toIRParam,
        ret := (match returns with | [single] => single.toIRType | _ => IRType.unit),
        payable := fn.isPayable, body := genParamLoads fn.bindingParams ++ body } := by
  unfold compileFunctionSpec at origin
  cases validated : validateFunctionSpec fn with
  | error message => simp [validated, bind, Except.bind] at origin
  | ok value =>
    cases returned : functionReturns fn with
    | error message => simp [validated, returned, bind, Except.bind] at origin
    | ok returns =>
      cases lowered : compileStmtListWithFork fields events errors .calldata [] false
          (fn.bindingParams.map (·.name)) adts fork fn.body internals with
      | error message => simp [validated, returned, lowered, bind, Except.bind, Except.map, pure, Except.pure] at origin
      | ok body =>
        simp only [validated, returned, lowered, bind, Except.bind, pure, Except.pure,
          Except.map, Except.ok.injEq] at origin
        exact ⟨returns, body, rfl, rfl, origin.symm⟩

/-- Removing an absent guard preserves the actual function compiler receipt,
for every hard fork and internal-function table. -/
theorem unguarded_origin (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (adts : List AdtTypeDef) (internals : List FunctionSpec)
    (selector : Nat) (fn : FunctionSpec) (fork : HardFork) (compiled : IRFunction)
    (unlocked : fn.nonReentrantLock = none)
    (guarded : compileGuardedFunctionSpec fields events errors adts internals selector fn fork = .ok compiled) :
    compileFunctionSpec fields events errors adts selector fn fork internals = .ok compiled := by
  unfold compileGuardedFunctionSpec at guarded
  cases lowered : compileFunctionSpec fields events errors adts selector fn fork internals with
  | error message => simp [lowered, bind, Except.bind] at guarded
  | ok before =>
      simp only [lowered, bind, Except.bind, attachNonReentrantGuard, unlocked,
        pure, Except.pure, Except.ok.injEq] at guarded
      subst compiled
      rfl

/-- Payment and raw parameter-count guards are derived from actual compilation. -/
theorem metadata (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (adts : List AdtTypeDef) (selector : Nat) (fn : FunctionSpec)
    (fork : HardFork) (internals : List FunctionSpec) (compiled : IRFunction)
    (origin : compileFunctionSpec fields events errors adts selector fn fork internals = .ok compiled) :
    compiled.selector = selector ∧ compiled.payable = fn.isPayable ∧
      compiled.params.length = fn.params.length := by
  obtain ⟨returns, body, _, _, shape⟩ := components fields events errors adts selector fn fork internals compiled origin
  simp only [shape, List.length_map, and_self]

/-- Compiler-origin payment/count guards, joined to the actual selected contract
result. The function-list lookup remains a separate contract-compilation duty. -/
theorem compiled_selected_contract_match (spec : CompilationModel) (selectors : List Nat)
    (contract : IRContract) (tx : IRTransaction) (world : Verity.ContractState)
    (fn : FunctionSpec) (compiled : IRFunction) (helperFuel : Nat)
    (oracle : Nat → SourceSemantics.ExternalCallOutcome)
    (fork : HardFork) (internals : List FunctionSpec)
    (origin : compileFunctionSpec (SourceSemantics.effectiveFields spec) spec.events spec.errors
      spec.adtTypes tx.functionSelector fn fork internals = .ok compiled)
    (sourceSelected : SourceSemantics.findFunctionBySelector spec selectors tx.functionSelector = some fn)
    (irSelected : contract.functions.find? (·.selector == tx.functionSelector) = some compiled)
    (admitted : (!fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = false)
    (argumentsAdmitted : fn.params.length ≤ tx.args.length)
    (body : FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunctionWithHelpers spec helperFuel fn tx world oracle)
      (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world))) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretContractWithHelpers spec selectors helperFuel tx world oracle)
      (interpretIR contract tx (FunctionBody.initialIRStateForTx spec tx world)) := by
  obtain ⟨_, payable, count⟩ := metadata (SourceSemantics.effectiveFields spec)
    spec.events spec.errors spec.adtTypes tx.functionSelector fn fork internals compiled origin
  exact CustomErrorFunctionResult.selected_contract_match spec selectors contract tx world fn
    compiled helperFuel oracle sourceSelected irSelected (by simpa only [payable] using admitted)
    (by simpa only [payable] using admitted) (by simpa only [count] using argumentsAdmitted) body

end Compiler.Proofs.IRGeneration.CustomErrorCompilationOrigin
