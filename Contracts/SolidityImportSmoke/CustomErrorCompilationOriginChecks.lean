import Compiler.Proofs.IRGeneration.CustomErrorCompilationOrigin

namespace SolidityImportSmoke.CustomErrorCompilationOriginChecks
open Compiler Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open CustomErrorCompilationOrigin Verity.Core.Intrinsics

example (spec : CompilationModel) (selectors : List Nat)
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
      (interpretIR contract tx (FunctionBody.initialIRStateForTx spec tx world)) :=
  compiled_selected_contract_match spec selectors contract tx world fn compiled helperFuel oracle
    fork internals origin sourceSelected irSelected admitted argumentsAdmitted body

/-- A compile-success premise cannot certify a changed selector. -/
example (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (adts : List AdtTypeDef) (selector : Nat) (fn : FunctionSpec)
    (fork : HardFork) (internals : List FunctionSpec) (compiled : IRFunction)
    (origin : compileFunctionSpec fields events errors adts selector fn fork internals = .ok compiled)
    (changed : compiled.selector ≠ selector) : False :=
  changed (metadata fields events errors adts selector fn fork internals compiled origin).1

end SolidityImportSmoke.CustomErrorCompilationOriginChecks
