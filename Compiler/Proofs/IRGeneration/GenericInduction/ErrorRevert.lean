import Compiler.Proofs.IRGeneration.GenericInduction.ExprStmt
import Compiler.Proofs.IRGeneration.GenericInduction.CustomErrorDomain

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel Compiler.Yul

/-- Exact pointwise helper-aware error step. A type-level all-runtime step is
not inferred from coarse revertedness: actual declaration/argument resolution,
physical extent and sufficient execution fuel must supply the byte certificate. -/
theorem compiledStmtStep_revertError
    (spec : CompilationModel) (fields : List Field) (scope : List String)
    (runtime : SourceSemantics.RuntimeState) (state final : IRState)
    (name : String) (args : List Expr) (out : List YulStmt)
    (helperFuel extraFuel : Nat) (data : List UInt8)
    (_compiled : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (.revertError name args) = .ok out)
    (sourcePayload : SourceSemantics.typedErrorRevertResult fields runtime name args = .revertWithData data)
    (executed : execIRStmts (out.length + extraFuel + 1) state out = .revert final)
    (payload : final.revertBytes = some data) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime (.revertError name args) = sourceResult ∧
      execIRStmts (out.length + extraFuel + 1) state out = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.revertError name args)) sourceResult irExec := by
  refine ⟨.revertWithData data, .revert final, ?_, executed, payload⟩
  simpa only [SourceSemantics.execStmtWithHelpers] using sourcePayload

/-- Failing helper-aware require uses the actual typed Source bytes and exact
IR capture. The payload execution has the fuel remaining after the if stages. -/
theorem compiledStmtStep_requireError
    (spec : CompilationModel) (fields : List Field) (scope : List String)
    (runtime : SourceSemantics.RuntimeState) (state final : IRState)
    (cond : Expr) (name : String) (args : List Expr) (failCond : YulExpr)
    (out : List YulStmt) (helperFuel extraFuel : Nat) (data : List UInt8)
    (_compiled : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (.requireError cond name args) = .ok [.if_ failCond out])
    (sourceCondition : SourceSemantics.evalExprWithHelpers spec fields helperFuel runtime cond = some 0)
    (compiledCondition : evalIRExpr state failCond = some 1)
    (sourcePayload : SourceSemantics.typedErrorRevertResult fields runtime name args = .revertWithData data)
    (executed : execIRStmts extraFuel state out = .revert final)
    (payload : final.revertBytes = some data) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
        (.requireError cond name args) = sourceResult ∧
      execIRStmts ([YulStmt.if_ failCond out].length + extraFuel + 1) state
        [.if_ failCond out] = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.requireError cond name args)) sourceResult irExec := by
  have conditional : execIRStmt (extraFuel + 1) state (.if_ failCond out) = .revert final := by
    simp only [execIRStmt, compiledCondition]
    exact executed
  refine ⟨.revertWithData data, .revert final, ?_, ?_, payload⟩
  · simp [SourceSemantics.execStmtWithHelpers, sourceCondition, sourcePayload]
  · rw [show [YulStmt.if_ failCond out].length + extraFuel + 1 = (extraFuel + 1) + 1 by simp; omega]
    simp only [execIRStmts, conditional]

/-- Successful require evaluates no payload and retains the full existing
binding/storage/environment relation. -/
theorem compiledStmtStep_requireError_continue
    (spec : CompilationModel) (fields : List Field) (scope : List String)
    (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (cond : Expr) (name : String) (args : List Expr) (failCond : YulExpr)
    (out : List YulStmt) (helperFuel extraFuel value : Nat)
    (sourceCondition : SourceSemantics.evalExprWithHelpers spec fields helperFuel runtime cond = some value)
    (nonzero : value ≠ 0) (compiledCondition : evalIRExpr state failCond = some 0)
    (alignment : stmtStepMatchesIRExec fields (stmtNextScope scope (.requireError cond name args))
      (.continue runtime) (.continue state)) :
    SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime (.requireError cond name args) =
      .continue runtime ∧
    execIRStmts ([YulStmt.if_ failCond out].length + extraFuel + 1) state [.if_ failCond out] =
      .continue state ∧
    stmtStepMatchesIRExec fields (stmtNextScope scope (.requireError cond name args))
      (.continue runtime) (.continue state) := by
  refine ⟨?_, ?_, alignment⟩
  · simp [SourceSemantics.execStmtWithHelpers, sourceCondition, nonzero]
  · rw [show [YulStmt.if_ failCond out].length + extraFuel + 1 = (extraFuel + 1) + 1 by simp; omega]
    simp [execIRStmts, execIRStmt, compiledCondition]

end Compiler.Proofs.IRGeneration
