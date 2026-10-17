import Compiler.Proofs.IRGeneration.CustomErrorContinuation

namespace SolidityImportSmoke.CustomErrorContinuationChecks
open Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open SourceSemantics IRMemoryCoherence CustomErrorContinuation

example (spec : CompilationModel) (fields : List Field)
    (scope : List String) (stmt : Stmt) (out : List YulStmt) (minimum : Nat)
    (step : CompiledErrorStepWithin spec fields scope stmt out minimum)
    (helperFuel irFuel extraFuel : Nat) (runtime next : RuntimeState) (state nextIR : IRState)
    (pre : List Stmt) (prefixIR : List YulStmt)
    (domain : CustomErrorDomain spec runtime state) (initial : Coherent state)
    (source : execStmtListWithHelpers spec fields helperFuel runtime pre = .continue next)
    (compiled : execIRStmts irFuel state prefixIR = .continue nextIR)
    (pointer : nextIR.memory freeMemoryPointer = state.memory freeMemoryPointer)
    (enough : minimum ≤ extraFuel)
    (remaining : irFuel - prefixIR.length = out.length + extraFuel + 1) :
    ∃ sourceResult irExec,
      execStmtListWithHelpers spec fields helperFuel runtime (pre ++ [stmt]) = sourceResult ∧
      execIRStmts irFuel state (prefixIR ++ out) = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope stmt) sourceResult irExec := prefix_then_error spec fields scope stmt out minimum step helperFuel irFuel extraFuel runtime next state nextIR pre prefixIR domain initial source compiled pointer enough remaining

end SolidityImportSmoke.CustomErrorContinuationChecks
