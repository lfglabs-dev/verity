import Compiler.Proofs.IRGeneration.GenericInduction.CustomErrorDomain

namespace SolidityImportSmoke.SourceErrorDeclarationChecks
open Compiler.CompilationModel Compiler.Proofs.IRGeneration
open SourceSemantics SourceErrorDeclarations

example (fields : List Field) (state : RuntimeState) (stmt : Stmt) :
    Preserves state.errors (execStmt fields state stmt) := statement_errors fields state stmt

example (spec : CompilationModel) (fields : List Field) (fuel : Nat)
    (state : RuntimeState) (stmts : List Stmt) :
    Preserves state.errors (execStmtListWithHelpers spec fields fuel state stmts) :=
  helper_list_errors spec fields fuel state stmts

example (spec : CompilationModel) (fields : List Field) (fuel : Nat)
    (world : Verity.ContractState) (bindings : List (String × Nat)) (selector : Nat)
    (oracle : Nat → ExternalCallOutcome) (body : List Stmt) :
    Preserves spec.errors (execStmtListWithHelpers spec fields fuel
      { world := world, bindings := bindings, selector := selector,
        externalCallOracle := oracle, errors := spec.errors } body) :=
  function_entry_declarations spec fields fuel world bindings selector oracle body

example (name : String) (runBody : RuntimeState → StmtResult)
    (body : ∀ state, Preserves state.errors (runBody state))
    (state : RuntimeState) (index remaining : Nat) :
    Preserves state.errors (execForEachLoop name runBody state index remaining) :=
  forEach_errors name runBody body state index remaining

example (spec : CompilationModel) (fields : List Field) (fuel : Nat)
    (runtime next : RuntimeState) (state nextIR : IRState) (body : List Stmt)
    (domain : CustomErrorDomain spec runtime state)
    (executed : execStmtListWithHelpers spec fields fuel runtime body = .continue next)
    (physical : ∀ definition ∈ spec.errors,
      nextIR.memory freeMemoryPointer +
        32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
          Verity.Core.Uint256.modulus) :
    CustomErrorDomain spec next nextIR :=
  CustomErrorDomain.after_helper_continuation spec fields fuel runtime next state nextIR body domain executed physical

example (state : RuntimeState) (nonempty : state.errors ≠ []) :
    ¬ Preserves state.errors (.continue { state with errors := [] }) := by
  simpa only [Preserves] using Ne.symm nonempty

end SolidityImportSmoke.SourceErrorDeclarationChecks
