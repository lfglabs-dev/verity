import Compiler.Proofs.IRGeneration.CustomErrorListCompilation

namespace SolidityImportSmoke.CustomErrorListCompilationChecks
open Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open SourceSemantics IRMemoryCoherence CustomErrorListCompilation

example (spec : CompilationModel) (fields : List Field)
    (scope : List String) (pre : List Stmt) (preIR : List YulStmt)
    (stmt : Stmt) (out : List YulStmt) (minimum : Nat)
    (step : CompiledErrorStepWithin spec fields
      (pre.foldl (fun names stmt => collectStmtBindNames stmt ++ names) scope) stmt out minimum)
    (first : compileStmtList fields spec.events spec.errors .calldata [] false scope [] pre = .ok preIR)
    (helperFuel irFuel extraFuel : Nat) (runtime next : RuntimeState) (state nextIR : IRState)
    (domain : CustomErrorDomain spec runtime state) (initial : Coherent state)
    (source : execStmtListWithHelpers spec fields helperFuel runtime pre = .continue next)
    (executed : execIRStmts irFuel state preIR = .continue nextIR)
    (pointer : nextIR.memory freeMemoryPointer = state.memory freeMemoryPointer)
    (enough : minimum ≤ extraFuel)
    (remaining : irFuel - preIR.length = out.length + extraFuel + 1) :
    compileStmtList fields spec.events spec.errors .calldata [] false scope [] (pre ++ [stmt]) =
      .ok (preIR ++ out) ∧
    ∃ sourceResult irExec,
      execStmtListWithHelpers spec fields helperFuel runtime (pre ++ [stmt]) = sourceResult ∧
      execIRStmts irFuel state (preIR ++ out) = irExec ∧
      stmtStepMatchesIRExec fields
        (stmtNextScope (pre.foldl (fun names stmt => collectStmtBindNames stmt ++ names) scope) stmt)
        sourceResult irExec := compiled_prefix_then_error spec fields scope pre preIR stmt out minimum step first helperFuel irFuel extraFuel runtime next state nextIR domain initial source executed pointer enough remaining

example : ([Stmt.letVar "x" (.literal 7), .letVar "y" (.literal 9)]).foldl
    (fun names stmt => collectStmtBindNames stmt ++ names) ["arg"] = ["y", "x", "arg"] := by
  simp [List.foldl, collectStmtBindNames]

end SolidityImportSmoke.CustomErrorListCompilationChecks
