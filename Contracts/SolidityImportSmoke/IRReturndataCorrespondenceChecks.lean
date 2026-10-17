import Compiler.Proofs.IRGeneration.GenericInduction.ReturndataBytes

namespace SolidityImportSmoke.IRReturndataCorrespondenceChecks
open Compiler.Proofs.IRGeneration Compiler.CompilationModel

example {fields : List Field} {scope : List String}
    (runtime : SourceSemantics.RuntimeState) (state : IRState) (extraFuel : Nat)
    (aligned : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (extent : 32 * state.returndata.length < Verity.Core.Uint256.modulus)
    (slack : sizeOf PhysicalReturndataExecution.body -
      PhysicalReturndataExecution.body.length ≤ extraFuel) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmt fields runtime .revertReturndata = sourceResult ∧
      execIRStmts (PhysicalReturndataExecution.body.length + extraFuel + 1)
        state PhysicalReturndataExecution.body = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope .revertReturndata)
        sourceResult irExec :=
  compiled_revertReturndata_exact_bytes runtime state extraFuel aligned extent slack

example (fields : List Field) (scope : List String) :
    Compiler.CompilationModel.compileStmt fields [] [] .calldata [] false scope []
      .revertReturndata = Except.ok PhysicalReturndataExecution.body :=
  compile_revertReturndata_body fields scope

end SolidityImportSmoke.IRReturndataCorrespondenceChecks
