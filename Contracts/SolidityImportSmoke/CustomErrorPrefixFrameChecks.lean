import Compiler.Proofs.IRGeneration.CustomErrorPrefixFrame

namespace SolidityImportSmoke.CustomErrorPrefixFrameChecks
open Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open SourceSemantics IRMemoryCoherence CustomErrorPrefixFrame

example (name : String) (expr : YulExpr) : Step freeMemoryPointer (.let_ name expr) :=
  let_frame freeMemoryPointer name expr

example (value : YulExpr) :
    Step 64 (.exprStmt (.call "mstore" [.lit 0, value])) :=
  mstore_frame 64 0 value (by right; change 0 + 32 ≤ 64; omega)

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
    (frames : ∀ stmt ∈ preIR, Step freeMemoryPointer stmt)
    (enough : minimum ≤ extraFuel)
    (remaining : irFuel - preIR.length = out.length + extraFuel + 1) :
    compileStmtList fields spec.events spec.errors .calldata [] false scope [] (pre ++ [stmt]) =
      .ok (preIR ++ out) ∧
    ∃ sourceResult irExec,
      execStmtListWithHelpers spec fields helperFuel runtime (pre ++ [stmt]) = sourceResult ∧
      execIRStmts irFuel state (preIR ++ out) = irExec ∧
      stmtStepMatchesIRExec fields
        (stmtNextScope (pre.foldl (fun names stmt => collectStmtBindNames stmt ++ names) scope) stmt)
        sourceResult irExec :=
  compiled_framed_prefix_then_error spec fields scope pre preIR stmt out minimum step first
    helperFuel irFuel extraFuel runtime next state nextIR domain initial source executed frames enough remaining

end SolidityImportSmoke.CustomErrorPrefixFrameChecks
