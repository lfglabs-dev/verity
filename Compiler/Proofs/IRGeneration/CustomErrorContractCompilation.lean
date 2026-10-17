import Compiler.Proofs.IRGeneration.CustomErrorDispatchCompilation

namespace Compiler.Proofs.IRGeneration.CustomErrorContractCompilation
open Compiler.CompilationModel Compiler.Yul Verity.Core.Intrinsics

private theorem bind_success {α β : Type} {first : Except String α}
    {next : α → Except String β} {result : β}
    (success : (first >>= next) = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error message => simp [bind, Except.bind] at success
  | ok value => exact ⟨value, rfl, success⟩

/-- Extract the actual external-function map from full core compilation, with
no restrictions on guards, internal functions, special entrypoints or helpers. -/
theorem core_functions (spec : CompilationModel) (selectors : List Nat)
    (fork : HardFork) (contract : IRContract)
    (origin : compileValidatedCore spec selectors fork = .ok contract) :
    (SourceSemantics.selectorFunctionPairs spec selectors).mapM
      (fun entry => compileGuardedFunctionSpec (SourceSemantics.effectiveFields spec)
        spec.events spec.errors spec.adtTypes (spec.functions.filter (·.isInternal))
        entry.2 entry.1 fork) = .ok contract.functions := by
  unfold compileValidatedCore at origin
  obtain ⟨fallback, _, rest⟩ := bind_success origin
  obtain ⟨receive, _, rest⟩ := bind_success rest
  obtain ⟨functions, compiled, rest⟩ := bind_success rest
  obtain ⟨internalDefs, _, rest⟩ := bind_success rest
  by_cases empty : (templateIntrinsicItems spec).isEmpty = true
  all_goals
    simp only [empty, ↓reduceIte] at rest
    obtain ⟨templates, _, rest⟩ := bind_success rest
    obtain ⟨fallbackEntry, _, rest⟩ := bind_success rest
    obtain ⟨receiveEntry, _, rest⟩ := bind_success rest
    obtain ⟨deploy, _, rest⟩ := bind_success rest
    have shape := Except.ok.inj rest
    have functions_eq : functions = contract.functions := congrArg IRContract.functions shape
    simpa only [SourceSemantics.selectorFunctionPairs, selectorDispatchedFunctions,
      SourceSemantics.effectiveFields, functions_eq] using compiled

/-- The validated public compile result carries the same actual map receipt. -/
theorem compiled_functions (spec : CompilationModel) (selectors : List Nat)
    (fork : HardFork) (contract : IRContract)
    (origin : Compiler.CompilationModel.compile spec selectors fork = .ok contract) :
    (SourceSemantics.selectorFunctionPairs spec selectors).mapM
      (fun entry => compileGuardedFunctionSpec (SourceSemantics.effectiveFields spec)
        spec.events spec.errors spec.adtTypes (spec.functions.filter (·.isInternal))
        entry.2 entry.1 fork) = .ok contract.functions := by
  unfold Compiler.CompilationModel.compile at origin
  obtain ⟨_, _, core⟩ := bind_success origin
  exact core_functions spec selectors fork contract core

/-- Successful full compilation and real Source lookup suffice to select the
corresponding IR function and obtain its actual guarded compiler receipt. -/
theorem compiled_selected (spec : CompilationModel) (selectors : List Nat)
    (fork : HardFork) (contract : IRContract) (selector : Nat) (fn : FunctionSpec)
    (origin : Compiler.CompilationModel.compile spec selectors fork = .ok contract)
    (selected : SourceSemantics.findFunctionBySelector spec selectors selector = some fn) :
    ∃ compiled, contract.functions.find? (fun candidate => candidate.selector == selector) = some compiled ∧
      compileGuardedFunctionSpec (SourceSemantics.effectiveFields spec) spec.events spec.errors
        spec.adtTypes (spec.functions.filter (·.isInternal)) selector fn fork = .ok compiled :=
  CustomErrorDispatchCompilation.guarded_list_selected spec selectors fork contract.functions
    selector fn (compiled_functions spec selectors fork contract origin) selected

/-- Full compiler/dispatcher bridge for an admitted Source entrypoint. The
remaining premise is exact semantics of its actual guarded compiled body. -/
theorem compiled_contract_match (spec : CompilationModel) (selectors : List Nat)
    (fork : HardFork) (contract : IRContract) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (helperFuel : Nat)
    (oracle : Nat → SourceSemantics.ExternalCallOutcome)
    (origin : Compiler.CompilationModel.compile spec selectors fork = .ok contract)
    (selected : SourceSemantics.findFunctionBySelector spec selectors tx.functionSelector = some fn)
    (admitted : (!fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = false)
    (argumentsAdmitted : fn.params.length ≤ tx.args.length)
    (body : ∀ compiled,
      compileGuardedFunctionSpec (SourceSemantics.effectiveFields spec) spec.events spec.errors
        spec.adtTypes (spec.functions.filter (·.isInternal)) tx.functionSelector fn fork = .ok compiled →
      FunctionBody.sourceResultMatchesIRResult
        (SourceSemantics.interpretFunctionWithHelpers spec helperFuel fn tx world oracle)
        (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world))) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretContractWithHelpers spec selectors helperFuel tx world oracle)
      (interpretIR contract tx (FunctionBody.initialIRStateForTx spec tx world)) := by
  obtain ⟨compiled, found, receipt⟩ := compiled_selected spec selectors fork contract
    tx.functionSelector fn origin selected
  obtain ⟨_, payable, count⟩ := CustomErrorDispatchCompilation.guarded_metadata
    (SourceSemantics.effectiveFields spec) spec.events spec.errors spec.adtTypes
    (spec.functions.filter (·.isInternal)) tx.functionSelector fn fork compiled receipt
  exact CustomErrorFunctionResult.selected_contract_match spec selectors contract tx world fn
    compiled helperFuel oracle selected found admitted (by simpa only [payable] using admitted)
    (by simpa only [count] using argumentsAdmitted) (body compiled receipt)

/-- Dispatch composition exposing both the guarded receipt and its unguarded
origin. Keeping both lets expression certificates refer to the selected body. -/
theorem compiled_unguarded_contract_match (spec : CompilationModel) (selectors : List Nat)
    (fork : HardFork) (contract : IRContract) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (helperFuel : Nat)
    (oracle : Nat → SourceSemantics.ExternalCallOutcome)
    (origin : Compiler.CompilationModel.compile spec selectors fork = .ok contract)
    (selected : SourceSemantics.findFunctionBySelector spec selectors tx.functionSelector = some fn)
    (unlocked : fn.nonReentrantLock = none)
    (admitted : (!fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = false)
    (argumentsAdmitted : fn.params.length ≤ tx.args.length)
    (body : ∀ compiled,
      compileGuardedFunctionSpec (SourceSemantics.effectiveFields spec) spec.events spec.errors
        spec.adtTypes (spec.functions.filter (·.isInternal)) tx.functionSelector fn fork = .ok compiled →
      compileFunctionSpec (SourceSemantics.effectiveFields spec) spec.events spec.errors spec.adtTypes
        tx.functionSelector fn fork (spec.functions.filter (·.isInternal)) = .ok compiled →
      FunctionBody.sourceResultMatchesIRResult
        (SourceSemantics.interpretFunctionWithHelpers spec helperFuel fn tx world oracle)
        (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world))) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretContractWithHelpers spec selectors helperFuel tx world oracle)
      (interpretIR contract tx (FunctionBody.initialIRStateForTx spec tx world)) := by
  apply compiled_contract_match spec selectors fork contract tx world fn helperFuel oracle
    origin selected admitted argumentsAdmitted
  intro compiled guarded
  exact body compiled guarded (CustomErrorCompilationOrigin.unguarded_origin
    (SourceSemantics.effectiveFields spec) spec.events spec.errors spec.adtTypes
    (spec.functions.filter (·.isInternal)) tx.functionSelector fn fork compiled unlocked guarded)

end Compiler.Proofs.IRGeneration.CustomErrorContractCompilation
