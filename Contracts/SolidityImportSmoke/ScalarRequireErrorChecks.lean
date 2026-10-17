import Compiler.Proofs.IRGeneration.GenericInduction.CustomErrorBytes

namespace SolidityImportSmoke.ScalarRequireErrorChecks
open Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open CustomErrorExpressionFrame

example
    (definition : ErrorDef) (fields : List Field) (scope : List String)
    (errors : List ErrorDef) (ty : ParamType) (srcExpr cond : Expr)
    (argExpr encoded failCond : YulExpr)
    (compilerLookup : errors.find? (·.name == definition.name) = some definition)
    (compiledArgs : compileExprListWithInternals fields .calldata [] [srcExpr] = .ok [argExpr])
    (params : definition.params = [ty])
    (scalar : PhysicalCustomErrorScalarExecution.staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded)
    (condition : compileRequireFailCondWithInternals fields .calldata [] cond = .ok failCond)
    (runtime : SourceSemantics.RuntimeState) (state : IRState) (value extra : Nat)
    (typeName : String)
    (evaluated : SourceSemantics.evalExprList fields runtime [srcExpr] = some [value])
    (resolved : runtime.errors.filter (·.name == definition.name) = [definition])
    (canonical : Denote.errorScalarValueValid ty value = true)
    (supported : Denote.errorScalarType ty = some typeName)
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus)
    (argument : evalIRExpr state argExpr = some value)
    (supportedExpr : ScratchExpr argExpr)
    (sourceCond : SourceSemantics.evalExpr fields runtime cond = some 0)
    (compiledCond : evalIRExpr state failCond = some 1) :
    ∃ out data final,
      Compiler.CompilationModel.compileStmt fields [] errors .calldata [] false scope []
        (.requireError cond definition.name [srcExpr]) = .ok [.if_ failCond out] ∧
      SourceSemantics.execStmt fields runtime (.requireError cond definition.name [srcExpr]) =
        .revertWithData data ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 10)
        state [.if_ failCond out] = .revert final ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope
        (.requireError cond definition.name [srcExpr])) (.revertWithData data) (.revert final) :=
  compiled_requireError_scalar_failure_exact_bytes definition fields scope errors ty srcExpr cond argExpr encoded failCond compilerLookup compiledArgs params scalar encoding condition runtime state value extra typeName evaluated resolved canonical supported extent argument supportedExpr sourceCond compiledCond

end SolidityImportSmoke.ScalarRequireErrorChecks
