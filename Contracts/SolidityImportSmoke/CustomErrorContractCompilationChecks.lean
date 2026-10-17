import Compiler.Proofs.IRGeneration.CustomErrorContractCompilation

namespace SolidityImportSmoke.CustomErrorContractCompilationChecks
open Compiler Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open CustomErrorContractCompilation Verity.Core.Intrinsics

example (spec : CompilationModel) (selectors : List Nat)
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
      (interpretIR contract tx (FunctionBody.initialIRStateForTx spec tx world)) :=
  compiled_contract_match spec selectors fork contract tx world fn helperFuel oracle
    origin selected admitted argumentsAdmitted body

/-- Successful full compilation cannot lose an actually selected entrypoint. -/
example (spec : CompilationModel) (selectors : List Nat) (fork : HardFork)
    (contract : IRContract) (selector : Nat) (fn : FunctionSpec)
    (origin : Compiler.CompilationModel.compile spec selectors fork = .ok contract)
    (selected : SourceSemantics.findFunctionBySelector spec selectors selector = some fn)
    (missing : contract.functions.find? (fun candidate => candidate.selector == selector) = none) : False := by
  obtain ⟨compiled, found, _⟩ := compiled_selected spec selectors fork contract selector fn origin selected
  rw [missing] at found
  cases found

end SolidityImportSmoke.CustomErrorContractCompilationChecks
