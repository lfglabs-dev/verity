import Compiler.Proofs.IRGeneration.CustomErrorCompilationOrigin

namespace Compiler.Proofs.IRGeneration.CustomErrorConditionalCompilation
open Compiler.CompilationModel Compiler.Yul SourceSemantics

/-- Conditional errors use the same actual payload compiler as unconditional
errors, for arbitrary events, ADTs, fork and internal-function table. -/
theorem require_from_revert (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (source : DynamicDataSource) (locals : List String)
    (isInternal : Bool) (scope : List String) (adts : List AdtTypeDef)
    (fork : Verity.Core.Intrinsics.HardFork) (internals : List FunctionSpec)
    (cond : Expr) (name : String) (args : List Expr) (failCond : YulExpr)
    (out : List YulStmt)
    (condition : compileRequireFailCondWithInternals fields source internals cond = .ok failCond)
    (error : compileStmtWithFork fields events errors source locals isInternal scope adts fork
      (.revertError name args) internals = .ok out) :
    compileStmtWithFork fields events errors source locals isInternal scope adts fork
      (.requireError cond name args) internals = .ok [.if_ failCond out] := by
  unfold compileStmtWithFork at error ⊢
  simp only [condition, Bind.bind, Except.bind] at error ⊢
  cases lookup : errors.find? (·.name == name) with
  | none => simp [lookup, Bind.bind, Except.bind] at error
  | some definition =>
      cases compiled : compileExprListWithInternals fields source internals args with
      | error message => simp [lookup, compiled, Bind.bind, Except.bind, pure, Except.pure] at error
      | ok argExprs =>
          cases payload : revertWithCustomError source definition args argExprs with
          | error message =>
              simp [lookup, compiled, payload, Bind.bind, Except.bind, pure, Except.pure] at error
          | ok result =>
              simp [lookup, compiled, payload, Bind.bind, Except.bind, pure, Except.pure] at error ⊢
              exact error

/-- Actual function origin fixes the ABI-prefixed conditional zero-error body;
no supplied IR body shape or empty internal table is assumed. -/
theorem compiled_zero_body (spec : CompilationModel) (selector : Nat)
    (fn : FunctionSpec) (compiled : IRFunction) (definition : ErrorDef)
    (cond : Expr) (failCond : YulExpr) (out : List YulStmt)
    (fork : Verity.Core.Intrinsics.HardFork) (internals : List FunctionSpec)
    (origin : compileFunctionSpec (effectiveFields spec) spec.events spec.errors spec.adtTypes
      selector fn fork internals = .ok compiled)
    (sourceBody : fn.body = [.requireError cond definition.name []])
    (condition : compileRequireFailCondWithInternals (effectiveFields spec) .calldata
      internals cond = .ok failCond)
    (lookup : spec.errors.find? (·.name == definition.name) = some definition)
    (payload : revertWithCustomError .calldata definition [] [] = .ok out) :
    compiled.body = genParamLoads fn.bindingParams ++ [.if_ failCond out] := by
  obtain ⟨returns, actual, _, lowered, shape⟩ := CustomErrorCompilationOrigin.components
    (effectiveFields spec) spec.events spec.errors spec.adtTypes selector fn fork internals compiled origin
  have revertCompiled : compileStmtWithFork (effectiveFields spec) spec.events spec.errors
      .calldata [] false (fn.bindingParams.map (·.name)) spec.adtTypes fork
      (.revertError definition.name []) internals = .ok out := by
    simp [compileStmtWithFork, lookup, compileExprListWithInternals, payload,
      Bind.bind, Except.bind, pure, Except.pure]
  have requireCompiled := require_from_revert (effectiveFields spec) spec.events spec.errors
    .calldata [] false (fn.bindingParams.map (·.name)) spec.adtTypes fork internals cond
    definition.name [] failCond out condition revertCompiled
  have compiledList : compileStmtListWithFork (effectiveFields spec) spec.events spec.errors
      .calldata [] false (fn.bindingParams.map (·.name)) spec.adtTypes fork fn.body internals =
      .ok [.if_ failCond out] := by
    simp [sourceBody, compileStmtListWithFork, requireCompiled,
      Bind.bind, Except.bind, pure, Except.pure]
  have actualEq := Except.ok.inj (lowered.symm.trans compiledList)
  simpa only [shape, actualEq]

end Compiler.Proofs.IRGeneration.CustomErrorConditionalCompilation
