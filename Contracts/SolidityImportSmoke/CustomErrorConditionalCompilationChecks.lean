import Compiler.Proofs.IRGeneration.CustomErrorConditionalCompilation

namespace SolidityImportSmoke.CustomErrorConditionalCompilationChecks
open Compiler Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open CustomErrorConditionalCompilation Verity.Core.Intrinsics

/-- The conditional compiler bridge retains arbitrary helper tables and fork. -/
example (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (source : DynamicDataSource) (locals : List String) (isInternal : Bool)
    (scope : List String) (adts : List AdtTypeDef) (fork : HardFork)
    (internals : List FunctionSpec) (cond : Expr) (name : String)
    (args : List Expr) (failCond : YulExpr) (out : List YulStmt)
    (condition : compileRequireFailCondWithInternals fields source internals cond = .ok failCond)
    (error : compileStmtWithFork fields events errors source locals isInternal scope adts fork
      (.revertError name args) internals = .ok out) :
    compileStmtWithFork fields events errors source locals isInternal scope adts fork
      (.requireError cond name args) internals = .ok [.if_ failCond out] :=
  require_from_revert fields events errors source locals isInternal scope adts fork internals
    cond name args failCond out condition error

/-- Changing the conditional body contradicts its actual compiler receipt. -/
example (spec : CompilationModel) (selector : Nat) (fn : FunctionSpec)
    (compiled : IRFunction) (definition : ErrorDef) (cond : Expr)
    (failCond : YulExpr) (out : List YulStmt) (fork : HardFork)
    (internals : List FunctionSpec)
    (origin : compileFunctionSpec (SourceSemantics.effectiveFields spec) spec.events spec.errors
      spec.adtTypes selector fn fork internals = .ok compiled)
    (sourceBody : fn.body = [.requireError cond definition.name []])
    (condition : compileRequireFailCondWithInternals (SourceSemantics.effectiveFields spec)
      .calldata internals cond = .ok failCond)
    (lookup : spec.errors.find? (·.name == definition.name) = some definition)
    (payload : revertWithCustomError .calldata definition [] [] = .ok out)
    (changed : compiled.body ≠ genParamLoads fn.bindingParams ++ [.if_ failCond out]) : False :=
  changed (compiled_zero_body spec selector fn compiled definition cond failCond out fork internals
    origin sourceBody condition lookup payload)

/-- A conditional compiler receipt cannot turn an error into an unconditional
payload: the branch wrapper itself is part of the verified body shape. -/
example (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (source : DynamicDataSource) (locals : List String) (isInternal : Bool)
    (scope : List String) (adts : List AdtTypeDef) (fork : HardFork)
    (internals : List FunctionSpec) (cond : Expr) (name : String)
    (args : List Expr) (failCond : YulExpr) (out : List YulStmt)
    (condition : compileRequireFailCondWithInternals fields source internals cond = .ok failCond)
    (error : compileStmtWithFork fields events errors source locals isInternal scope adts fork
      (.revertError name args) internals = .ok out)
    (changed : compileStmtWithFork fields events errors source locals isInternal scope adts fork
      (.requireError cond name args) internals ≠ .ok [.if_ failCond out]) : False :=
  changed (require_from_revert fields events errors source locals isInternal scope adts fork internals
    cond name args failCond out condition error)

end SolidityImportSmoke.CustomErrorConditionalCompilationChecks
