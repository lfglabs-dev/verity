import Compiler.CompilationModel.Validation
import Compiler.Proofs.IRGeneration.FunctionBody.RequirePayloadBounds

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel

/-- A successful production function validation supplies physical payload
bounds; concrete compiler-correctness callers need no extra assumption. -/
theorem requirePayloadsFit_of_validateFunctionSpec (fn : FunctionSpec)
    (validated : validateFunctionSpec fn = .ok ()) :
    FunctionBody.requirePayloadsFit fn.body := by
  cases checked : validateRequirePayloads s!"function '{fn.name}'" fn.body with
  | error message =>
      simp only [validateFunctionSpec, checked] at validated
      change (Except.error message : Except String Unit) = .ok () at validated
      cases validated
  | ok value =>
      cases value
      exact FunctionBody.requirePayloadsFit_of_validation _ fn.body checked

/-- Constructor bounds come from the production constructor validation gate. -/
theorem requirePayloadsFit_of_validateConstructorSpec (ctor : ConstructorSpec)
    (validated : validateConstructorSpec (some ctor) = .ok ()) :
    FunctionBody.requirePayloadsFit ctor.body := by
  cases checked : validateRequirePayloads "constructor" ctor.body with
  | error message =>
      simp only [validateConstructorSpec, checked] at validated
      change (Except.error message : Except String Unit) = .ok () at validated
      cases validated
  | ok value =>
      cases value
      exact FunctionBody.requirePayloadsFit_of_validation _ ctor.body checked

end Compiler.Proofs.IRGeneration
