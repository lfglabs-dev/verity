import Compiler.Proofs.IRGeneration.CustomErrorListCompilation
import Compiler.Proofs.IRGeneration.PhysicalEventMemory

namespace Compiler.Proofs.IRGeneration.CustomErrorPrefixFrame
open Compiler.CompilationModel Compiler.Yul IRMemoryCoherence SourceSemantics

/-- A continuing opcode's word frame, quantified over its actual evaluation. -/
def Step (query : Nat) (stmt : YulStmt) : Prop :=
  ∀ fuel state next, Coherent state → execIRStmt fuel state stmt = .continue next →
    next.memory query = state.memory query

theorem let_frame (query : Nat) (name : String) (expr : YulExpr) :
    Step query (.let_ name expr) := by
  intro fuel state next coherent executed
  cases fuel with
  | zero => simp [execIRStmt] at executed
  | succ fuel =>
      simp only [execIRStmt] at executed
      cases evaluated : evalIRExpr state expr <;> simp only [evaluated] at executed
      · cases executed
      · cases executed
        rfl

theorem assign_frame (query : Nat) (name : String) (expr : YulExpr) :
    Step query (.assign name expr) := by
  intro fuel state next coherent executed
  cases fuel with
  | zero => simp [execIRStmt] at executed
  | succ fuel =>
      simp only [execIRStmt] at executed
      cases evaluated : evalIRExpr state expr <;> simp only [evaluated] at executed
      · cases executed
      · cases executed
        rfl

/-- Physical writes miss the complete observed 32-byte word after EVM offset
normalization. Coherence is propagated separately by the actual executor. -/
theorem mstore_frame (query offset : Nat) (value : YulExpr)
    (outside : query + 32 ≤ (Verity.Core.Uint256.ofNat offset).val ∨
      (Verity.Core.Uint256.ofNat offset).val + 32 ≤ query) :
    Step query (.exprStmt (.call "mstore" [.lit offset, value])) := by
  intro fuel state next coherent executed
  cases fuel with
  | zero => simp [execIRStmt] at executed
  | succ fuel =>
      cases evaluated : evalIRExpr state value with
      | none => simp [execIRStmt, evalIRExpr, evaluated] at executed
      | some result =>
          have actual := execIRStmt_physical_mstore_of_eval state (.lit offset) value offset result fuel
            (by simp only [evalIRExpr]) evaluated
          rw [actual] at executed
          cases executed
          simpa only [Verity.Core.Uint256.ofNat, Verity.Core.UINT256_MODULUS,
            Compiler.Constants.evmModulus, Verity.Core.Uint256.modulus] using
            word_outside_store state (Verity.Core.Uint256.ofNat offset).val result query coherent outside

theorem list_frame (query : Nat) (body : List YulStmt) (frames : ∀ stmt ∈ body, Step query stmt)
    (fuel : Nat) (state next : IRState) (initial : Coherent state)
    (executed : execIRStmts fuel state body = .continue next) :
    next.memory query = state.memory query := by
  induction body generalizing fuel state with
  | nil =>
      simp only [execIRStmts] at executed
      cases executed
      rfl
  | cons stmt rest ih =>
      have head : Step query stmt := frames stmt List.mem_cons_self
      have tail : ∀ stmt ∈ rest, Step query stmt :=
        fun item member => frames item (List.mem_cons_of_mem _ member)
      have main : next.memory query = state.memory query := by
          cases fuel with
          | zero => simp [execIRStmts] at executed
          | succ fuel =>
              cases step : execIRStmt fuel state stmt <;>
                simp only [execIRStmts, step] at executed
              case «continue» middle =>
                have kept := (executors fuel).1 state stmt initial
                have middleCoherent : Coherent middle := by simpa only [step, Preserves] using kept
                exact (ih tail fuel middle middleCoherent executed).trans (head fuel state middle initial step)
              all_goals cases executed
      exact main

theorem compiled_framed_prefix_then_error (spec : CompilationModel) (fields : List Field)
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
        sourceResult irExec := by
  have pointer := list_frame freeMemoryPointer preIR frames irFuel state nextIR initial executed
  exact CustomErrorListCompilation.compiled_prefix_then_error spec fields scope pre preIR stmt out minimum
    step first helperFuel irFuel extraFuel runtime next state nextIR domain initial source executed
    pointer enough remaining

end Compiler.Proofs.IRGeneration.CustomErrorPrefixFrame
